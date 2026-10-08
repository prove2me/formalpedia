-- Prove2me | solution 1 for HoffmanBound.ErrorBound.eq8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:20:02.18653+00:00
-- url     : https://prove2.me/submissions/2f109531-9281-4b01-a8c6-426fb154d117

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model
import Definitions.Def_HoffmanBound_ErrorBound_NormConstants



namespace HoffmanBound.ErrorBound

open Matrix

theorem hoff_norm_equiv {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : IsPosHomogeneous F) :
    (∃ ν : ℝ, 0 ≤ ν ∧ ∀ z, F z ≤ ν * ‖z‖) ∧ (∃ μ : ℝ, 0 < μ ∧ ∀ z, μ * ‖z‖ ≤ F z) := by
  obtain ⟨hcont, hnn, hzero, hhom⟩ := hF
  have hK : IsCompact (Metric.sphere (0 : Fin k → ℝ) 1) := isCompact_sphere _ _
  have hnormz : ∀ z : Fin k → ℝ, z ≠ 0 → ‖(‖z‖⁻¹) • z‖ = 1 := by
    intro z hz
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [norm_smul, norm_inv, norm_norm]; field_simp
  have hdecomp : ∀ z : Fin k → ℝ, F z = ‖z‖ * F ((‖z‖⁻¹) • z) := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp [(hzero 0).2 rfl]
    · rw [← hhom _ (norm_nonneg z)]
      have : 0 < ‖z‖ := norm_pos_iff.2 hz
      rw [smul_smul, mul_inv_cancel₀ this.ne', one_smul]
  constructor
  · obtain ⟨ν, hν⟩ := hK.bddAbove_image hcont.continuousOn
    refine ⟨max ν 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z = 0
    · subst hz; simp [(hzero 0).2 rfl]
    · rw [hdecomp z]
      have h1 : F ((‖z‖⁻¹) • z) ≤ ν := hν ⟨_, by simpa using hnormz z hz, rfl⟩
      have h2 : F ((‖z‖⁻¹) • z) ≤ max ν 0 := h1.trans (le_max_left _ _)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg z)
  · by_cases hne : (Metric.sphere (0 : Fin k → ℝ) 1).Nonempty
    · obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
      have hz0ne : z0 ≠ 0 := by
        intro h; subst h; simp at hz0
      have hpos : 0 < F z0 := lt_of_le_of_ne (hnn _) (fun h => hz0ne ((hzero _).1 h.symm))
      refine ⟨F z0, hpos, fun z => ?_⟩
      by_cases hz : z = 0
      · subst hz; simp [(hzero 0).2 rfl]
      · rw [hdecomp z]
        have h1 : F z0 ≤ F ((‖z‖⁻¹) • z) := hmin (by simpa using hnormz z hz)
        have := mul_le_mul_of_nonneg_left h1 (norm_nonneg z)
        linarith
    · refine ⟨1, one_pos, fun z => ?_⟩
      by_cases hz : z = 0
      · subst hz; simp [(hzero 0).2 rfl]
      · exact absurd ⟨_, by simpa using hnormz z hz⟩ hne

theorem hoff_lemma1_core {m : ℕ} (Fm : (Fin m → ℝ) → ℝ) (hFm : IsPosHomogeneous Fm) :
    ∃ e : ℝ, 0 < e ∧ ∀ (y : Fin m → ℝ) (S : Finset (Fin m)), Fm (restrictVec S y) ≤ e * Fm y := by
  obtain ⟨⟨ν, hν0, hν⟩, ⟨μ, hμ, hμ'⟩⟩ := hoff_norm_equiv Fm hFm
  refine ⟨ν / μ + 1, by positivity, fun y S => ?_⟩
  have h1 : ‖restrictVec S y‖ ≤ ‖y‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun i => ?_
    unfold restrictVec
    split_ifs
    · exact norm_le_pi_norm y i
    · simp
  have h2 : Fm (restrictVec S y) ≤ ν * ‖y‖ := (hν _).trans (mul_le_mul_of_nonneg_left h1 hν0)
  have h3 : ‖y‖ ≤ Fm y / μ := by rw [le_div_iff₀ hμ]; linarith [hμ' y]
  have h4 : Fm (restrictVec S y) ≤ ν / μ * Fm y := by
    calc _ ≤ ν * ‖y‖ := h2
      _ ≤ ν * (Fm y / μ) := mul_le_mul_of_nonneg_left h3 hν0
      _ = ν / μ * Fm y := by ring
  have : 0 ≤ Fm y := hFm.2.1 y
  nlinarith

theorem hoff_isClosed_sol {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsClosed (solutionSet A b) := by
  unfold solutionSet
  have : Continuous (fun x : Fin n → ℝ => A *ᵥ x) := by
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  exact isClosed_le this continuous_const

theorem hoff_exists_nearest {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (x : Fin n → ℝ) :
    ∃ y, IsNearest (solutionSet A b) x y := by
  obtain ⟨x1, hx1⟩ := hcons
  set f : (Fin n → ℝ) → ℝ := fun z => (x - z) ⬝ᵥ (x - z) with hf
  have hfc : Continuous f := by
    simp only [hf, dotProduct]; fun_prop
  set K := solutionSet A b ∩ {z | f z ≤ f x1} with hKdef
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (hoff_isClosed_sol A b).inter (isClosed_le hfc continuous_const)
    · refine (Metric.isBounded_iff_subset_closedBall x).2 ⟨f x1 + 1, fun z hz => ?_⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      refine (pi_norm_le_iff_of_nonneg (by have : 0 ≤ f x1 := Finset.sum_nonneg (fun i _ => mul_self_nonneg _); linarith)).2 fun i => ?_
      have hz2 : f z ≤ f x1 := hz.2
      have hsq : (x i - z i) * (x i - z i) ≤ f z :=
        Finset.single_le_sum (f := fun j => (x j - z j) * (x j - z j)) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      have : |z i - x i| * |z i - x i| ≤ f x1 := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; nlinarith
      nlinarith [abs_nonneg (z i - x i)]
  obtain ⟨y, hyK, hymin⟩ := hKc.exists_isMinOn ⟨x1, hx1, (le_rfl : f x1 ≤ f x1)⟩ hfc.continuousOn
  refine ⟨y, hyK.1, fun z hz => ?_⟩
  by_cases h : f z ≤ f x1
  · exact hymin ⟨hz, h⟩
  · exact (hyK.2).trans (not_le.1 h).le

theorem hoff_dot_expand {n : ℕ} (u d : Fin n → ℝ) :
    (u - d) ⬝ᵥ (u - d) = u ⬝ᵥ u - 2 * (u ⬝ᵥ d) + d ⬝ᵥ d := by
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm d u]; ring

theorem hoff_mulVec_eval {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y d : Fin n → ℝ) (t : ℝ) (i : Fin m) :
    (A *ᵥ (y + t • d)) i = (A *ᵥ y) i + t * (A *ᵥ d) i := by
  simp [Matrix.mulVec_add, Matrix.mulVec_smul]

theorem hoff_var {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x y : Fin n → ℝ)
    (hy : IsNearest (solutionSet A b) x y) (d : Fin n → ℝ)
    (hd : ∀ i ∈ activeSet A b y, (A *ᵥ d) i ≤ 0) : (x - y) ⬝ᵥ d ≤ 0 := by
  by_contra hp
  push_neg at hp
  set p := (x - y) ⬝ᵥ d with hpdef
  set q := d ⬝ᵥ d with hqdef
  have hq : 0 < q := by
    have hq0 : 0 ≤ q := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rcases hq0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : d = 0 := dotProduct_self_eq_zero.1 h.symm
      rw [hpdef, this] at hp; simp at hp
  have hyΩ : A *ᵥ y ≤ b := hy.1
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ i, i ∉ activeSet A b y → (A *ᵥ (y + t • d)) i < b i := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : i ∈ activeSet A b y
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · have hlt : (A *ᵥ y) i < b i := by
        refine lt_of_le_of_ne (hyΩ i) ?_
        intro h; exact hi (by simp [activeSet, h])
      have hc : Continuous (fun t : ℝ => (A *ᵥ (y + t • d)) i) := by
        simp only [hoff_mulVec_eval]; fun_prop
      have h0 : (A *ᵥ (y + (0:ℝ) • d)) i < b i := by simpa [hoff_mulVec_eval] using hlt
      exact ((hc.tendsto 0).eventually (gt_mem_nhds h0)).mono fun t ht _ => ht
  have h3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), y + t • d ∈ solutionSet A b := by
    refine ((hev.filter_mono nhdsWithin_le_nhds).and h3).mono fun t ⟨ht, htpos⟩ => ?_
    show A *ᵥ (y + t • d) ≤ b
    intro i
    by_cases hi : i ∈ activeSet A b y
    · have hyi : (A *ᵥ y) i = b i := by simpa [activeSet] using hi
      rw [hoff_mulVec_eval, hyi]
      have := mul_nonpos_of_nonneg_of_nonpos htpos.le (hd i hi)
      linarith
    · exact (ht i hi).le
  have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < p / q :=
    (eventually_lt_nhds (div_pos hp hq)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht1, ht2, ht3⟩ := (h1.and (h2.and h3)).exists
  have := hy.2 _ ht1
  have e : x - (y + t • d) = (x - y) - t • d := by abel
  rw [e] at this
  have h5 := hoff_dot_expand (x - y) (t • d)
  rw [h5] at this
  have h6 : (x - y) ⬝ᵥ (t • d) = t * p := by rw [hpdef]; simp [dotProduct_smul]
  have h7 : (t • d) ⬝ᵥ (t • d) = t * t * q := by rw [hqdef]; simp [dotProduct_smul, smul_dotProduct]; ring
  rw [h6, h7] at this
  have hlt : t * q < p := by rwa [lt_div_iff₀ hq] at ht2
  nlinarith

theorem hoff_lemma2_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x y : Fin n → ℝ)
    (hx : x ∉ solutionSet A b) (hy : IsNearest (solutionSet A b) x y) :
    x ∉ {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} ∧
      IsNearest {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} x y := by
  have hact : ∀ i ∈ activeSet A b y, (A *ᵥ y) i = b i := fun i hi => by simpa [activeSet] using hi
  have hsub : ∀ z : Fin n → ℝ, ∀ i ∈ activeSet A b y, (A *ᵥ (z - y)) i = (A *ᵥ z) i - b i := by
    intro z i hi; rw [Matrix.mulVec_sub]; simp [hact i hi]
  refine ⟨fun hxS => ?_, ⟨fun i hi => (hact i hi).le, fun z hz => ?_⟩⟩
  · have := hoff_var A b x y hy (x - y) (fun i hi => by rw [hsub x i hi]; linarith [hxS i hi])
    have h0 : x - y = 0 := dotProduct_self_eq_zero.1 (le_antisymm this
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)))
    exact hx (by rw [sub_eq_zero.1 h0]; exact hy.1)
  · have := hoff_var A b x y hy (z - y) (fun i hi => by rw [hsub z i hi]; linarith [hz i hi])
    have e : x - z = (x - y) - (z - y) := by abel
    rw [e]
    have h5 := hoff_dot_expand (x - y) (z - y)
    have : 0 ≤ (z - y) ⬝ᵥ (z - y) := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    linarith

theorem hoff_polar {n : ℕ} (T : Set (Fin n → ℝ)) (hT : ∀ t : ℝ, 0 ≤ t → ∀ w ∈ T, t • w ∈ T)
    (x : Fin n → ℝ) (hx : IsNearest T x 0) : ∀ w ∈ T, x ⬝ᵥ w ≤ 0 := by
  intro w hw
  by_contra hp
  push_neg at hp
  set p := x ⬝ᵥ w with hpdef
  set q := w ⬝ᵥ w with hqdef
  have hq : 0 < q := by
    have hq0 : 0 ≤ q := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rcases hq0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : w = 0 := dotProduct_self_eq_zero.1 h.symm
      rw [hpdef, this] at hp; simp at hp
  have h1 := hx.2 ((p / q) • w) (hT _ (div_pos hp hq).le w hw)
  have h5 := hoff_dot_expand x ((p / q) • w)
  simp only [sub_zero] at h1
  have h6 : x ⬝ᵥ ((p / q) • w) = p / q * p := by rw [hpdef]; simp [dotProduct_smul]
  have h7 : ((p / q) • w) ⬝ᵥ ((p / q) • w) = p / q * (p / q) * q := by
    rw [hqdef]; simp [dotProduct_smul, smul_dotProduct]; ring
  rw [h5, h6, h7] at h1
  have : p / q * (p / q) * q = p / q * p := by field_simp
  have : 0 < p / q * p := mul_pos (div_pos hp hq) hp
  linarith

theorem hoff_posPart_smul {k : ℕ} (r : ℝ) (hr : 0 ≤ r) (v : Fin k → ℝ) :
    posPartVec (r • v) = r • posPartVec v := by
  funext i
  simp only [posPartVec, Pi.smul_apply, smul_eq_mul]
  rw [← mul_zero r, ← mul_max_of_nonneg _ _ hr]; simp

theorem hoff_lemma3_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m))
    (Fn : (Fin n → ℝ) → ℝ) (Fm : (Fin m → ℝ) → ℝ)
    (hFn : IsPosHomogeneous Fn) (hFm : IsPosHomogeneous Fm) :
    ∃ dS : ℝ, 0 < dS ∧ ∀ x ∈ setE A S, dS * Fn x ≤ Fm (posPartVec (rowsOn A S *ᵥ x)) := by
  set M := rowsOn A S with hM
  set T := solutionSet M 0 with hTdef
  have hTcone : ∀ t : ℝ, 0 ≤ t → ∀ w ∈ T, t • w ∈ T := by
    intro t ht w hw
    show M *ᵥ (t • w) ≤ 0
    intro i
    have : (M *ᵥ w) i ≤ 0 := hw i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonpos_of_nonneg_of_nonpos ht this
  have hT0 : (0 : Fin n → ℝ) ∈ T := by
    show M *ᵥ 0 ≤ 0
    simp
  obtain ⟨⟨ν, hν0, hν⟩, ⟨μ, hμ, hμ'⟩⟩ := hoff_norm_equiv Fn hFn
  set C : Set (Fin n → ℝ) := Metric.sphere 0 1 ∩ {z | ∀ w ∈ T, z ⬝ᵥ w ≤ 0} with hC
  have hCclosed : IsClosed C := by
    refine Metric.isClosed_sphere.inter ?_
    have : {z : Fin n → ℝ | ∀ w ∈ T, z ⬝ᵥ w ≤ 0} = ⋂ w ∈ T, {z | z ⬝ᵥ w ≤ 0} := by ext; simp
    rw [this]
    exact isClosed_biInter fun w _ => isClosed_le (by simp only [dotProduct]; fun_prop) continuous_const
  have hCc : IsCompact C := (isCompact_sphere _ _).of_isClosed_subset hCclosed Set.inter_subset_left
  set φ : (Fin n → ℝ) → ℝ := fun z => Fm (posPartVec (M *ᵥ z)) with hφ
  have hφc : Continuous φ := by
    refine hFm.1.comp ?_
    refine continuous_pi fun i => ?_
    simp only [posPartVec, Matrix.mulVec, dotProduct]
    fun_prop
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ C, δ ≤ φ z := by
    by_cases hne : C.Nonempty
    · obtain ⟨z0, hz0, hmin⟩ := hCc.exists_isMinOn hne hφc.continuousOn
      refine ⟨φ z0, ?_, fun z hz => hmin hz⟩
      refine lt_of_le_of_ne (hFm.2.1 _) (fun h => ?_)
      have h0 : posPartVec (M *ᵥ z0) = 0 := (hFm.2.2.1 _).1 h.symm
      have hz0T : z0 ∈ T := by
        intro i
        have := congrFun h0 i
        simp only [posPartVec, Pi.zero_apply] at this
        have := le_max_left ((M *ᵥ z0) i) 0
        simp_all
      have := hz0.2 z0 hz0T
      have hz : z0 = 0 := dotProduct_self_eq_zero.1 (le_antisymm this
        (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)))
      have := hz0.1
      rw [hz] at this; simp at this
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hne⟩
  obtain ⟨δ, hδ0, hδ⟩ := hδ
  refine ⟨δ / (ν + 1), by positivity, fun x hx => ?_⟩
  obtain ⟨hxT, hxn⟩ := hx
  have hx0 : x ≠ 0 := fun h => hxT (h ▸ hT0)
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hpol := hoff_polar T hTcone x hxn
  have hxhat : (‖x‖⁻¹) • x ∈ C := by
    have hn1 : ‖(‖x‖⁻¹) • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]; field_simp
    refine ⟨by simpa [Metric.mem_sphere] using hn1, fun w hw => ?_⟩
    simp only [smul_dotProduct, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hr.le) (hpol w hw)
  have h1 := hδ _ hxhat
  have e : x = ‖x‖ • ((‖x‖⁻¹) • x) := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have h2 : φ x = ‖x‖ * φ ((‖x‖⁻¹) • x) := by
    conv_lhs => rw [e]
    simp only [hφ, Matrix.mulVec_smul]
    rw [hoff_posPart_smul _ hr.le, hFm.2.2.2 _ hr.le]
  have h3 : Fn x ≤ ν * ‖x‖ := hν x
  have h4 : δ / (ν + 1) * Fn x ≤ δ * ‖x‖ := by
    have hnn : 0 ≤ Fn x := hFn.2.1 x
    calc δ / (ν + 1) * Fn x ≤ δ / (ν + 1) * (ν * ‖x‖) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = δ * ‖x‖ * (ν / (ν + 1)) := by field_simp
      _ ≤ δ * ‖x‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = _ := mul_one _
  have : ‖x‖ * δ ≤ φ x := by rw [h2]; exact mul_le_mul_of_nonneg_left h1 hr.le
  show _ ≤ φ x
  linarith

theorem hoff_rowsOn_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m))
    (z : Fin n → ℝ) (i : Fin m) :
    (rowsOn A S *ᵥ z) i = if i ∈ S then (A *ᵥ z) i else 0 := by
  by_cases h : i ∈ S <;> simp [rowsOn, Matrix.mulVec, h]

theorem hoff_theorem_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty)
    (Fn : (Fin n → ℝ) → ℝ) (Fm : (Fin m → ℝ) → ℝ)
    (hFn : IsPosHomogeneous Fn) (hFm : IsPosHomogeneous Fm) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      Fn (x - x₀) ≤ c * Fm (posPartVec (A *ᵥ x - b)) := by
  classical
  obtain ⟨e, he, hel⟩ := hoff_lemma1_core Fm hFm
  have h3 : ∀ S : Finset (Fin m), ∃ dS : ℝ, 0 < dS ∧ ∀ x ∈ setE A S,
      dS * Fn x ≤ Fm (posPartVec (rowsOn A S *ᵥ x)) := fun S => hoff_lemma3_core A S Fn Fm hFn hFm
  choose d hd0 hd using h3
  set SG : ℝ := ∑ S : Finset (Fin m), (d S)⁻¹ with hSGdef
  have hSGpos : 0 < SG := by
    apply Finset.sum_pos (fun S _ => inv_pos.2 (hd0 S))
    exact ⟨∅, Finset.mem_univ _⟩
  refine ⟨e * SG, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ solutionSet A b
  · refine ⟨x, hx, ?_⟩
    rw [sub_self, (hFn.2.2.1 0).2 rfl]
    exact mul_nonneg (by positivity) (hFm.2.1 _)
  · obtain ⟨y, hy⟩ := hoff_exists_nearest A b hcons x
    refine ⟨y, hy.1, ?_⟩
    set S := activeSet A b y with hS
    have hact : ∀ i ∈ S, (A *ᵥ y) i = b i := fun i hi => by simpa [hS, activeSet] using hi
    have hsub : ∀ i ∈ S, (A *ᵥ (x - y)) i = (A *ᵥ x) i - b i := by
      intro i hi; rw [Matrix.mulVec_sub]; simp [hact i hi]
    have hxE : (x - y) ∈ setE A S := by
      have hT : ∀ z, z ∈ solutionSet (rowsOn A S) 0 ↔ ∀ i ∈ S, (A *ᵥ z) i ≤ 0 := by
        intro z
        constructor
        · intro h i hi
          have := h i
          rwa [hoff_rowsOn_mulVec, if_pos hi] at this
        · intro h i
          rw [hoff_rowsOn_mulVec]
          split_ifs with hi
          · exact h i hi
          · exact le_rfl
      refine ⟨fun hmem => ?_, ?_, fun z hz => ?_⟩
      · have hmem' := (hT _).1 hmem
        have := hoff_var A b x y hy (x - y) hmem'
        have h0 : x - y = 0 := dotProduct_self_eq_zero.1 (le_antisymm this
          (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)))
        exact hx (by rw [sub_eq_zero.1 h0]; exact hy.1)
      · exact (hT 0).2 (fun i _ => by simp)
      · have := hoff_var A b x y hy z ((hT z).1 hz)
        simp only [sub_zero]
        have h5 := hoff_dot_expand (x - y) z
        have : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
        linarith
    have h1 := hd S (x - y) hxE
    have hpp : posPartVec (rowsOn A S *ᵥ (x - y)) = restrictVec S (posPartVec (A *ᵥ x - b)) := by
      funext i
      simp only [posPartVec, restrictVec, hoff_rowsOn_mulVec]
      by_cases hi : i ∈ S
      · rw [if_pos hi, if_pos hi, hsub i hi]; rfl
      · simp [hi]
    rw [hpp] at h1
    have h2 := hel (posPartVec (A *ᵥ x - b)) S
    have hdS : (d S)⁻¹ ≤ SG :=
      Finset.single_le_sum (f := fun S => (d S)⁻¹) (fun S _ => (inv_pos.2 (hd0 S)).le) (Finset.mem_univ S)
    have hF0 := hFm.2.1 (posPartVec (A *ᵥ x - b))
    have h4 : Fn (x - y) ≤ (d S)⁻¹ * (e * Fm (posPartVec (A *ᵥ x - b))) := by
      rw [← div_eq_inv_mul, le_div_iff₀ (hd0 S)]
      calc Fn (x - y) * d S = d S * Fn (x - y) := mul_comm _ _
        _ ≤ _ := h1.trans h2
    calc Fn (x - y) ≤ (d S)⁻¹ * (e * Fm (posPartVec (A *ᵥ x - b))) := h4
      _ ≤ SG * (e * Fm (posPartVec (A *ᵥ x - b))) :=
          mul_le_mul_of_nonneg_right hdS (by positivity)
      _ = e * SG * Fm (posPartVec (A *ᵥ x - b)) := by ring

def coneOf {m n : ℕ} (v : Fin m → (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}

theorem hoff_sum_ext {m n : ℕ} (v : Fin m → (Fin n → ℝ)) (J : Finset (Fin m)) (c : Fin m → ℝ)
    (hc : ∀ i ∉ J, c i = 0) : ∑ i, c i • v i = ∑ j : J, c j • v j := by
  rw [Finset.sum_coe_sort J (fun i => c i • v i)]
  exact (Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hc i hi])).symm

theorem hoff_cara {m n : ℕ} (v : Fin m → (Fin n → ℝ)) :
    ∀ (T : Finset (Fin m)) (c : Fin m → ℝ), (∀ i, 0 ≤ c i) → (∀ i ∉ T, c i = 0) →
    ∃ J : Finset (Fin m), J ⊆ T ∧ LinearIndependent ℝ (fun j : J => v j) ∧
      ∃ c' : Fin m → ℝ, (∀ i, 0 ≤ c' i) ∧ (∀ i ∉ J, c' i = 0) ∧
        ∑ i, c' i • v i = ∑ i, c i • v i := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro c hc hcT
  by_cases hli : LinearIndependent ℝ (fun j : T => v j)
  · exact ⟨T, Finset.Subset.refl _, hli, c, hc, hcT, rfl⟩
  · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hli
    set g' : Fin m → ℝ := fun i => if h : i ∈ T then g ⟨i, h⟩ else 0 with hg'
    have hg'T : ∀ i ∉ T, g' i = 0 := fun i hi => by simp [hg', hi]
    have hg'sum : ∑ i, g' i • v i = 0 := by
      rw [hoff_sum_ext v T g' hg'T, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hg', j.2]
    have hex : ∃ h : Fin m → ℝ, ∑ i, h i • v i = 0 ∧ (∀ i ∉ T, h i = 0) ∧ ∃ i, 0 < h i := by
      by_cases hp : ∃ i, 0 < g' i
      · exact ⟨g', hg'sum, hg'T, hp⟩
      · refine ⟨fun i => - g' i, ?_, fun i hi => by simp [hg'T i hi], ?_⟩
        · simp only [neg_smul, Finset.sum_neg_distrib, hg'sum, neg_zero]
        · push_neg at hp
          refine ⟨i0, ?_⟩
          have : g' i0 ≠ 0 := by simpa [hg', i0.2] using hi0
          have := lt_of_le_of_ne (hp i0) this
          linarith
    obtain ⟨h, hsum, hhT, i1, hi1⟩ := hex
    have hne : (T.filter (fun i => 0 < h i)).Nonempty :=
      ⟨i1, Finset.mem_filter.2 ⟨by by_contra hh; exact absurd (hhT i1 hh) hi1.ne', hi1⟩⟩
    obtain ⟨j0, hj0P, hmin⟩ := (T.filter (fun i => 0 < h i)).exists_min_image (fun i => c i / h i) hne
    have hj0T : j0 ∈ T := (Finset.mem_filter.1 hj0P).1
    have hj0pos : 0 < h j0 := (Finset.mem_filter.1 hj0P).2
    set θ := c j0 / h j0 with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (hc _) hj0pos.le
    have hc'' : ∀ i, 0 ≤ c i - θ * h i := by
      intro i
      by_cases hpos : 0 < h i
      · have hiT : i ∈ T := by by_contra hh; exact absurd (hhT i hh) hpos.ne'
        have := hmin i (Finset.mem_filter.2 ⟨hiT, hpos⟩)
        rw [le_div_iff₀ hpos] at this
        linarith
      · have : h i ≤ 0 := not_lt.1 hpos
        nlinarith [hc i, mul_nonneg hθ0 (neg_nonneg.2 this)]
    have hj0z : c j0 - θ * h j0 = 0 := by rw [hθ]; field_simp; ring
    have hsupp : ∀ i ∉ T.erase j0, c i - θ * h i = 0 := by
      intro i hi
      by_cases hij : i = j0
      · rw [hij]; exact hj0z
      · have hiT : i ∉ T := fun hh => hi (Finset.mem_erase.2 ⟨hij, hh⟩)
        rw [hcT i hiT, hhT i hiT]; ring
    obtain ⟨J, hJT, hJ, c', hc'0, hc'J, hc'sum⟩ :=
      ih (T.erase j0) (Finset.erase_ssubset hj0T) (fun i => c i - θ * h i) hc'' hsupp
    refine ⟨J, hJT.trans (Finset.erase_subset _ _), hJ, c', hc'0, hc'J, ?_⟩
    rw [hc'sum]
    have : ∑ i, (c i - θ * h i) • v i = ∑ i, c i • v i - θ • ∑ i, h i • v i := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_smul, mul_smul]
    rw [this, hsum, smul_zero, sub_zero]

theorem hoff_cone_closed {m n : ℕ} (v : Fin m → (Fin n → ℝ)) : IsClosed (coneOf v) := by
  classical
  have key : coneOf v = ⋃ J : Finset (Fin m), ⋃ (_ : LinearIndependent ℝ (fun j : J => v j)),
      (Fintype.linearCombination ℝ (fun j : J => v j)) '' {d : J → ℝ | ∀ j, 0 ≤ d j} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨J, -, hJ, c', hc'0, hc'J, hc'sum⟩ := hoff_cara v Finset.univ c hc (fun i hi => absurd (Finset.mem_univ i) hi)
      refine ⟨J, hJ, fun j => c' j, fun j => hc'0 _, ?_⟩
      rw [Fintype.linearCombination_apply, ← hc'sum, hoff_sum_ext v J c' hc'J]
    · rintro ⟨J, hJ, d, hd, rfl⟩
      refine ⟨fun i => if h : i ∈ J then d ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
      · by_cases h : i ∈ J
        · simp [h, hd]
        · simp [h]
      · rw [hoff_sum_ext v J _ (fun i hi => by simp [hi]), Fintype.linearCombination_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [j.2]
  rw [key]
  refine isClosed_iUnion_of_finite fun J => isClosed_iUnion_of_finite fun hJ => ?_
  have hemb := LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hJ))
  refine hemb.isClosedMap _ ?_
  have : {d : J → ℝ | ∀ j, 0 ≤ d j} = ⋂ j, {d | 0 ≤ d j} := by ext; simp
  rw [this]
  exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)

theorem hoff_exists_nearest_gen {n : ℕ} (Ω : Set (Fin n → ℝ)) (hΩ : IsClosed Ω)
    (hcons : Ω.Nonempty) (x : Fin n → ℝ) : ∃ y, IsNearest Ω x y := by
  obtain ⟨x1, hx1⟩ := hcons
  set f : (Fin n → ℝ) → ℝ := fun z => (x - z) ⬝ᵥ (x - z) with hf
  have hfc : Continuous f := by
    simp only [hf, dotProduct]; fun_prop
  set K := Ω ∩ {z | f z ≤ f x1} with hKdef
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hΩ.inter (isClosed_le hfc continuous_const)
    · refine (Metric.isBounded_iff_subset_closedBall x).2 ⟨f x1 + 1, fun z hz => ?_⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      refine (pi_norm_le_iff_of_nonneg (by have : 0 ≤ f x1 := Finset.sum_nonneg (fun i _ => mul_self_nonneg _); linarith)).2 fun i => ?_
      have hz2 : f z ≤ f x1 := hz.2
      have hsq : (x i - z i) * (x i - z i) ≤ f z :=
        Finset.single_le_sum (f := fun j => (x j - z j) * (x j - z j)) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      have : |z i - x i| * |z i - x i| ≤ f x1 := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; nlinarith
      nlinarith [abs_nonneg (z i - x i)]
  obtain ⟨y, hyK, hymin⟩ := hKc.exists_isMinOn ⟨x1, hx1, (le_rfl : f x1 ≤ f x1)⟩ hfc.continuousOn
  refine ⟨y, hyK.1, fun z hz => ?_⟩
  by_cases h : f z ≤ f x1
  · exact hymin ⟨hz, h⟩
  · exact (hyK.2).trans (not_le.1 h).le

theorem hoff_cone_combo {m n : ℕ} (v : Fin m → (Fin n → ℝ)) {x1 x2 : Fin n → ℝ}
    (h1 : x1 ∈ coneOf v) (h2 : x2 ∈ coneOf v) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x1 + b • x2 ∈ coneOf v := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  refine ⟨fun i => a * c1 i + b * c2 i, fun i => by have := hc1 i; have := hc2 i; positivity, ?_⟩
  simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]

theorem hoff_cone_var {m n : ℕ} (v : Fin m → (Fin n → ℝ)) (x p : Fin n → ℝ)
    (hp : IsNearest (coneOf v) x p) : ∀ z ∈ coneOf v, (x - p) ⬝ᵥ (z - p) ≤ 0 := by
  intro z hz
  by_contra hpos
  push_neg at hpos
  set p0 := (x - p) ⬝ᵥ (z - p) with hp0
  set q := (z - p) ⬝ᵥ (z - p) with hq
  have hqpos : 0 < q := by
    have hq0 : 0 ≤ q := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rcases hq0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : z - p = 0 := dotProduct_self_eq_zero.1 h.symm
      rw [hp0, this] at hpos; simp at hpos
  set t := min 1 (p0 / q) / 2 with ht
  have ht0 : 0 < t := by have : 0 < min 1 (p0 / q) := lt_min one_pos (div_pos hpos hqpos); rw [ht]; linarith
  have ht1 : t ≤ 1 := by have := min_le_left 1 (p0 / q); rw [ht]; linarith
  have ht2 : t * q < p0 := by
    have h1 : t < p0 / q := by
      have := min_le_right 1 (p0 / q); have : 0 < min 1 (p0 / q) := lt_min one_pos (div_pos hpos hqpos)
      rw [ht]; linarith
    rwa [lt_div_iff₀ hqpos] at h1
  have hmem : p + t • (z - p) ∈ coneOf v := by
    have : p + t • (z - p) = (1 - t) • p + t • z := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact hoff_cone_combo v hp.1 hz (by linarith) ht0.le
  have := hp.2 _ hmem
  have e : x - (p + t • (z - p)) = (x - p) - t • (z - p) := by abel
  rw [e] at this
  have h5 := hoff_dot_expand (x - p) (t • (z - p))
  rw [h5] at this
  have h6 : (x - p) ⬝ᵥ (t • (z - p)) = t * p0 := by rw [hp0]; simp [dotProduct_smul]
  have h7 : (t • (z - p)) ⬝ᵥ (t • (z - p)) = t * t * q := by rw [hq]; simp [dotProduct_smul, smul_dotProduct]; ring
  rw [h6, h7] at this
  nlinarith

theorem hoff_farkas {m n : ℕ} (v : Fin m → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hx : ∀ w : Fin n → ℝ, (∀ i, v i ⬝ᵥ w ≤ 0) → x ⬝ᵥ w ≤ 0) : x ∈ coneOf v := by
  by_contra hxC
  have h0 : (0 : Fin n → ℝ) ∈ coneOf v := ⟨0, fun _ => le_rfl, by simp⟩
  obtain ⟨p, hp⟩ := hoff_exists_nearest_gen _ (hoff_cone_closed v) ⟨0, h0⟩ x
  set w := x - p with hw
  have hwv : ∀ i, v i ⬝ᵥ w ≤ 0 := by
    intro i
    have hpv : p + v i ∈ coneOf v := by
      obtain ⟨c, hc, hcp⟩ := hp.1
      refine ⟨fun j => c j + if j = i then 1 else 0, fun j => ?_, ?_⟩
      · have := hc j; show 0 ≤ c j + (if j = i then 1 else 0); split_ifs <;> linarith
      · simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← hcp]
    have := hoff_cone_var v x p hp _ hpv
    rw [add_sub_cancel_left] at this
    rwa [dotProduct_comm]
  have h1 := hx w hwv
  have h2 := hoff_cone_var v x p hp 0 h0
  have hwne : w ≠ 0 := fun h => hxC (by have : x = p := sub_eq_zero.1 h; rw [this]; exact hp.1)
  have hww : 0 < w ⬝ᵥ w := by
    rcases (Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i)) : 0 ≤ w ⬝ᵥ w).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.1 h.symm) hwne
  have e : x = w + p := by rw [hw]; abel
  have h3 : x ⬝ᵥ w = w ⬝ᵥ w + p ⬝ᵥ w := by
    conv_lhs => rw [e]
    rw [add_dotProduct]
  have h4 : p ⬝ᵥ w = w ⬝ᵥ p := dotProduct_comm _ _
  rw [zero_sub, dotProduct_neg] at h2
  linarith

theorem hoff_lemma4_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) :
    conePrime A S = setE A S := by
  set M := rowsOn A S with hM
  have hcone_dot : ∀ (c : Fin m → ℝ) (w : Fin n → ℝ),
      (∑ i, c i • M i) ⬝ᵥ w = ∑ i, c i * (M *ᵥ w) i := by
    intro c w
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_dotProduct, smul_eq_mul]; rfl
  have hTcone : ∀ t : ℝ, 0 ≤ t → ∀ w ∈ solutionSet M 0, t • w ∈ solutionSet M 0 := by
    intro t ht w hw
    show M *ᵥ (t • w) ≤ 0
    intro i
    have : (M *ᵥ w) i ≤ 0 := hw i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonpos_of_nonneg_of_nonpos ht this
  have hT0 : (0 : Fin n → ℝ) ∈ solutionSet M 0 := by
    show M *ᵥ 0 ≤ 0
    simp
  ext x
  constructor
  · rintro ⟨hx0, c, hc, rfl⟩
    have hneg : ∀ w ∈ solutionSet M 0, (∑ i, c i • M i) ⬝ᵥ w ≤ 0 := by
      intro w hw
      rw [hcone_dot]
      exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hc i) (hw i)
    refine ⟨fun hmem => hx0 ?_, ⟨hT0, fun z hz => ?_⟩⟩
    · have := hneg _ hmem
      exact dotProduct_self_eq_zero.1 (le_antisymm this (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)))
    · have h1 := hneg z hz
      simp only [sub_zero]
      have h5 := hoff_dot_expand (∑ i, c i • M i) z
      have : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
      linarith
  · rintro ⟨hxT, hxn⟩
    have hx0 : x ≠ 0 := fun h => hxT (h ▸ hT0)
    refine ⟨hx0, ?_⟩
    have hpol := hoff_polar _ hTcone x hxn
    exact hoff_farkas (fun i => M i) x (fun w hw => hpol w (fun i => by simpa [Matrix.mulVec] using hw i))

theorem hoff_u_mem_E {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x y : Fin n → ℝ)
    (hx : x ∉ solutionSet A b) (hy : IsNearest (solutionSet A b) x y) :
    x - y ∈ setE A (activeSet A b y) := by
  set S := activeSet A b y with hS
  have hact : ∀ i ∈ S, (A *ᵥ y) i = b i := fun i hi => by simpa [hS, activeSet] using hi
  have hT : ∀ z, z ∈ solutionSet (rowsOn A S) 0 ↔ ∀ i ∈ S, (A *ᵥ z) i ≤ 0 := by
    intro z
    constructor
    · intro h i hi
      have := h i
      rwa [hoff_rowsOn_mulVec, if_pos hi] at this
    · intro h i
      rw [hoff_rowsOn_mulVec]
      split_ifs with hi
      · exact h i hi
      · exact le_rfl
  refine ⟨fun hmem => ?_, ?_, fun z hz => ?_⟩
  · have hmem' := (hT _).1 hmem
    have := hoff_var A b x y hy (x - y) hmem'
    have h0 : x - y = 0 := dotProduct_self_eq_zero.1 (le_antisymm this
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)))
    exact hx (by rw [sub_eq_zero.1 h0]; exact hy.1)
  · exact (hT 0).2 (fun i _ => by simp)
  · have := hoff_var A b x y hy z ((hT z).1 hz)
    simp only [sub_zero]
    have h5 := hoff_dot_expand (x - y) z
    have : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    linarith

theorem hoff_decomp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (x : Fin n → ℝ) (hx : x ∉ solutionSet A b) :
    ∃ x₀ ∈ solutionSet A b, ∃ (S : Finset (Fin m)) (c : Fin m → ℝ), (∀ i, 0 ≤ c i) ∧
      (∀ i ∉ S, c i = 0) ∧ x - x₀ = ∑ i, c i • A i ∧ x - x₀ ≠ 0 ∧
      ∀ k ∈ S, (A *ᵥ (x - x₀)) k = (A *ᵥ x - b) k := by
  classical
  obtain ⟨y, hy⟩ := hoff_exists_nearest A b hcons x
  set S := activeSet A b y with hS
  have hact : ∀ i ∈ S, (A *ᵥ y) i = b i := fun i hi => by simpa [hS, activeSet] using hi
  have hE := hoff_u_mem_E A b x y hx hy
  have hcp : x - y ∈ conePrime A S := by rw [hoff_lemma4_core]; exact hE
  obtain ⟨hu0, c, hc, hsum⟩ := hcp
  refine ⟨y, hy.1, S, fun i => if i ∈ S then c i else 0, fun i => ?_, fun i hi => by simp [hi], ?_, hu0, ?_⟩
  · by_cases h : i ∈ S
    · simp [h, hc i]
    · simp [h]
  · rw [hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hrow : rowsOn A S i = if i ∈ S then A i else 0 := rfl
    show _ = (if i ∈ S then c i else 0) • A i
    by_cases h : i ∈ S
    · rw [hrow, if_pos h, if_pos h]
    · rw [hrow, if_neg h, if_neg h, smul_zero, zero_smul]
  · intro k hk
    rw [Matrix.mulVec_sub]; simp [hact k hk]

theorem hoff_bound_u {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i)
    (a : ℝ) (ha : ∀ i j, |A i j| ≤ a) (j : Fin n) :
    |(∑ i, c i • A i) j| ≤ a * ∑ i, c i := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ i, c i * A i j| ≤ ∑ i, |c i * A i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, c i * a := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hc i)]
        exact mul_le_mul_of_nonneg_left (ha i j) (hc i)
    _ = a * ∑ i, c i := by rw [← Finset.sum_mul, mul_comm]

theorem hoff_Au {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (k : Fin m) :
    (A *ᵥ ∑ i, c i • A i) k = ∑ i, c i * gram A k i := by
  simp only [Matrix.mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul, gram, Matrix.of_apply]

theorem hoff_maxNorm_le {k : ℕ} (u : Fin k → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ j, |u j| ≤ B) :
    maxNorm u ≤ B := by
  unfold maxNorm
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · simp [Real.iSup_of_isEmpty, hB]
  · exact ciSup_le h

theorem hoff_le_maxNorm {k : ℕ} (u : Fin k → ℝ) (j : Fin k) : |u j| ≤ maxNorm u :=
  le_ciSup (f := fun i => |u i|) (Set.finite_range _).bddAbove j

theorem hoff_maxNorm_nonneg {k : ℕ} (u : Fin k → ℝ) : 0 ≤ maxNorm u :=
  Real.iSup_nonneg fun i => abs_nonneg _

theorem hoff_aMax_ge {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    |A i j| ≤ aMax A := by
  unfold aMax
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j, |A i j|) (Set.finite_range _).bddAbove i)
  exact le_ciSup (f := fun j => |A i j|) (Set.finite_range _).bddAbove j

theorem hoff_aMax_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ aMax A :=
  Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => abs_nonneg _

theorem hoff_eq9_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (hpos : ∀ i j, 0 < A i ⬝ᵥ A j) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ aMax A / vMin A * maxNorm (posPartVec (A *ᵥ x - b)) := by
  intro x
  have hvle : ∀ k i, vMin A ≤ gram A k i := by
    intro k i
    unfold vMin
    refine le_trans (ciInf_le (f := fun i => ⨅ j, gram A i j) (Set.finite_range _).bddBelow k) ?_
    exact ciInf_le (f := fun j => gram A k j) (Set.finite_range _).bddBelow i
  have hgpos : ∀ i j, 0 < gram A i j := fun i j => hpos i j
  have hv0 : 0 ≤ vMin A := by
    unfold vMin
    exact Real.iInf_nonneg fun i => Real.iInf_nonneg fun j => (hgpos i j).le
  have hcoef : 0 ≤ aMax A / vMin A := div_nonneg (hoff_aMax_nonneg A) hv0
  by_cases hx : x ∈ solutionSet A b
  · refine ⟨x, hx, ?_⟩
    rw [sub_self]
    have : maxNorm (0 : Fin n → ℝ) = 0 := by simp [maxNorm]
    rw [this]
    exact mul_nonneg hcoef (hoff_maxNorm_nonneg _)
  · obtain ⟨x₀, hx₀, S, c, hc, hcS, hu, hu0, hAu⟩ := hoff_decomp A b hcons x hx
    refine ⟨x₀, hx₀, ?_⟩
    set t := ∑ i, c i with ht
    have hex : ∃ i, c i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hu0; rw [hu]; simp [h]
    obtain ⟨i0, hi0⟩ := hex
    have hi0S : i0 ∈ S := by by_contra h; exact hi0 (hcS i0 h)
    have hi0pos : 0 < c i0 := lt_of_le_of_ne (hc i0) (Ne.symm hi0)
    have htpos : 0 < t := lt_of_lt_of_le hi0pos
      (Finset.single_le_sum (f := c) (fun i _ => hc i) (Finset.mem_univ i0))
    have hnn : Nonempty (Fin n) := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hu0 (Subsingleton.elim _ _)
    haveI : Nonempty (Fin m) := ⟨i0⟩
    haveI := hnn
    have hvpos : 0 < vMin A := by
      unfold vMin
      obtain ⟨i1, hi1⟩ := exists_eq_ciInf_of_finite (f := fun i => ⨅ j, gram A i j)
      obtain ⟨j1, hj1⟩ := exists_eq_ciInf_of_finite (f := fun j => gram A i1 j)
      rw [← hi1, ← hj1]; exact hgpos _ _
    have h1 : maxNorm (x - x₀) ≤ aMax A * t := by
      rw [hu]
      exact hoff_maxNorm_le _ _ (mul_nonneg (hoff_aMax_nonneg A) htpos.le)
        (hoff_bound_u A c hc _ (hoff_aMax_ge A))
    have h2 : vMin A * t ≤ (A *ᵥ (x - x₀)) i0 := by
      rw [hu, hoff_Au, ht, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hvle i0 i) (hc i)
    have h3 : (A *ᵥ (x - x₀)) i0 ≤ maxNorm (posPartVec (A *ᵥ x - b)) := by
      rw [hAu i0 hi0S]
      refine le_trans ?_ (hoff_le_maxNorm _ i0)
      simp only [posPartVec]
      exact (le_max_left _ _).trans (le_abs_self _)
    calc maxNorm (x - x₀) ≤ aMax A * t := h1
      _ = aMax A / vMin A * (vMin A * t) := by field_simp
      _ ≤ aMax A / vMin A * maxNorm (posPartVec (A *ᵥ x - b)) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hcoef

theorem hoff_gram_self_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    0 ≤ gram A i i := by
  show 0 ≤ A i ⬝ᵥ A i
  exact Finset.sum_nonneg (fun j _ => mul_self_nonneg _)

theorem hoff_gram_comm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin m) :
    gram A i j = gram A j i := by
  show A i ⬝ᵥ A j = A j ⬝ᵥ A i
  exact dotProduct_comm _ _

theorem hoff_rowsum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) (i : Fin m)
    (hi : i ∈ S) : wConst A ≤ ∑ k ∈ S, gram A k i := by
  classical
  have h1 : wConst A ≤ gram A i i + ∑ j ∈ Finset.univ.filter (fun j => gram A i j < 0), gram A i j :=
    ciInf_le (f := fun i => gram A i i + ∑ j ∈ Finset.univ.filter (fun j => gram A i j < 0), gram A i j)
      (Set.finite_range _).bddBelow i
  refine h1.trans ?_
  have e1 : ∑ j ∈ Finset.univ.filter (fun j => gram A i j < 0), gram A i j
      = ∑ j, if gram A i j < 0 then gram A i j else 0 := by rw [Finset.sum_filter]
  have e2 : gram A i i = ∑ j, if j = i then gram A i i else 0 := by simp
  have e3 : ∑ k ∈ S, gram A k i = ∑ j, if j ∈ S then gram A i j else 0 := by
    rw [← Finset.sum_filter]
    · apply Finset.sum_congr
      · ext j; simp
      · intro j _; exact hoff_gram_comm A j i
  rw [e1, e3]
  conv_lhs => rw [e2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hii := hoff_gram_self_nonneg A i
  by_cases hj : j = i
  · subst hj
    simp [hi, not_lt.2 hii]
  · by_cases hjS : j ∈ S
    · by_cases hneg : gram A i j < 0
      · simp [hj, hjS, hneg]
      · simp [hj, hjS, hneg, not_lt.1 hneg]
    · by_cases hneg : gram A i j < 0
      · simp [hj, hjS, hneg, hneg.le]
      · simp [hj, hjS, hneg]

theorem hoff_eq10_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (hw : 0 < wConst A) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ aMax A / wConst A * sumNorm (posPartVec (A *ᵥ x - b)) := by
  intro x
  have hcoef : 0 ≤ aMax A / wConst A := div_nonneg (hoff_aMax_nonneg A) hw.le
  have hsn : 0 ≤ sumNorm (posPartVec (A *ᵥ x - b)) := Finset.sum_nonneg fun i _ => abs_nonneg _
  by_cases hx : x ∈ solutionSet A b
  · refine ⟨x, hx, ?_⟩
    rw [sub_self]
    have : maxNorm (0 : Fin n → ℝ) = 0 := by simp [maxNorm]
    rw [this]
    exact mul_nonneg hcoef hsn
  · obtain ⟨x₀, hx₀, S, c, hc, hcS, hu, hu0, hAu⟩ := hoff_decomp A b hcons x hx
    refine ⟨x₀, hx₀, ?_⟩
    set t := ∑ i, c i with ht
    have hex : ∃ i, c i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hu0; rw [hu]; simp [h]
    obtain ⟨i0, hi0⟩ := hex
    have hi0pos : 0 < c i0 := lt_of_le_of_ne (hc i0) (Ne.symm hi0)
    have htpos : 0 < t := lt_of_lt_of_le hi0pos
      (Finset.single_le_sum (f := c) (fun i _ => hc i) (Finset.mem_univ i0))
    have h1 : maxNorm (x - x₀) ≤ aMax A * t := by
      rw [hu]
      exact hoff_maxNorm_le _ _ (mul_nonneg (hoff_aMax_nonneg A) htpos.le)
        (hoff_bound_u A c hc _ (hoff_aMax_ge A))
    have h2 : wConst A * t ≤ ∑ k ∈ S, (A *ᵥ (x - x₀)) k := by
      rw [hu]
      simp only [hoff_Au]
      rw [Finset.sum_comm, ht, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i ∈ S
      · have := hoff_rowsum A S i hi
        rw [mul_comm]
        calc c i * wConst A ≤ c i * ∑ k ∈ S, gram A k i := mul_le_mul_of_nonneg_left this (hc i)
          _ = ∑ k ∈ S, c i * gram A k i := by rw [Finset.mul_sum]
      · rw [hcS i hi]; simp
    have h3 : ∑ k ∈ S, (A *ᵥ (x - x₀)) k ≤ sumNorm (posPartVec (A *ᵥ x - b)) := by
      calc ∑ k ∈ S, (A *ᵥ (x - x₀)) k = ∑ k ∈ S, (A *ᵥ x - b) k :=
            Finset.sum_congr rfl fun k hk => hAu k hk
        _ ≤ ∑ k ∈ S, |posPartVec (A *ᵥ x - b) k| := by
            refine Finset.sum_le_sum fun k _ => ?_
            simp only [posPartVec]
            rw [abs_of_nonneg (le_max_right _ _)]
            exact le_max_left _ _
        _ ≤ ∑ k, |posPartVec (A *ᵥ x - b) k| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => abs_nonneg _)
    calc maxNorm (x - x₀) ≤ aMax A * t := h1
      _ = aMax A / wConst A * (wConst A * t) := by field_simp
      _ ≤ aMax A / wConst A * sumNorm (posPartVec (A *ᵥ x - b)) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hcoef

theorem hoff_simplex_compact {m : ℕ} (J : Finset (Fin m)) : IsCompact (simplexOn J) := by
  classical
  apply Metric.isCompact_of_isClosed_isBounded
  · have e : simplexOn J = ({l : Fin m → ℝ | ∀ j, 0 ≤ l j} ∩ {l | ∀ j, j ∉ J → l j = 0}) ∩
        {l | ∑ j ∈ J, l j = 1} := by
      ext l; simp [simplexOn, and_assoc]
    rw [e]
    refine (IsClosed.inter (IsClosed.inter ?_ ?_) ?_)
    · rw [Set.setOf_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
    · rw [Set.setOf_forall]
      refine isClosed_iInter fun j => ?_
      by_cases hj : j ∈ J
      · simp [hj]
      · simp only [hj, not_false_eq_true, true_implies]
        exact isClosed_eq (continuous_apply j) continuous_const
    · exact isClosed_eq (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun l hl => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    rw [Real.norm_eq_abs]
    by_cases hj : j ∈ J
    · rw [abs_of_nonneg (hl.1 j)]
      calc l j ≤ ∑ i ∈ J, l i := Finset.single_le_sum (f := l) (fun i _ => hl.1 i) hj
        _ = 1 := hl.2.2
    · rw [hl.2.1 j hj]; simp

theorem hoff_vS_aux {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (J : Finset (Fin m))
    (l : Fin m → ℝ) (hl : ∀ j ∉ J, l j = 0) :
    (∑ i, l i • A i) ⬝ᵥ (∑ i, l i • A i) = ∑ i ∈ J, l i * ∑ j ∈ J, gram A i j * l j := by
  classical
  have h1 : ∀ i, A i ⬝ᵥ (∑ j, l j • A j) = ∑ j ∈ J, gram A i j * l j := by
    intro i
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
    rw [← Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => by simp [hl j hj])]
    exact Finset.sum_congr rfl fun j _ => by simp only [gram, Matrix.of_apply]; ring
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, h1]
  exact (Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hl i hi])).symm

theorem hoff_vS_lower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (J : Finset (Fin m))
    (hne : J.Nonempty) (hli : LinearIndependent ℝ (fun j : J => A j)) :
    ∃ r : ℝ, 0 < r ∧ ∀ l ∈ simplexOn J,
      r ≤ ⨆ i : J, ∑ j ∈ J, gram A i j * l j := by
  classical
  set f : (Fin m → ℝ) → ℝ := fun l => (∑ i, l i • A i) ⬝ᵥ (∑ i, l i • A i) with hf
  have hfc : Continuous f := by
    simp only [hf, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  obtain ⟨j0, hj0⟩ := hne
  have hl0 : (Pi.single j0 1 : Fin m → ℝ) ∈ simplexOn J := by
    refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
    · by_cases h : j = j0
      · subst h; simp
      · simp [h]
    · have : j ≠ j0 := fun h => hj (h ▸ hj0)
      simp [this]
    · simp [hj0]
  obtain ⟨l1, hl1, hmin⟩ := (hoff_simplex_compact J).exists_isMinOn ⟨_, hl0⟩ hfc.continuousOn
  have hfpos : ∀ l ∈ simplexOn J, 0 < f l := by
    intro l hl
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (fun h => ?_)
    have h0 : ∑ i, l i • A i = 0 := dotProduct_self_eq_zero.1 h.symm
    have := Fintype.linearIndependent_iff.1 hli (fun j => l j) (by
      rw [← hoff_sum_ext A J l hl.2.1] ; exact h0)
    have : ∑ j ∈ J, l j = 0 := Finset.sum_eq_zero fun j hj => this ⟨j, hj⟩
    rw [hl.2.2] at this; exact one_ne_zero this
  refine ⟨f l1, hfpos l1 hl1, fun l hl => ?_⟩
  refine (hmin hl).trans ?_
  show f l ≤ _
  rw [hf]
  simp only
  rw [hoff_vS_aux A J l hl.2.1]
  calc ∑ i ∈ J, l i * ∑ j ∈ J, gram A i j * l j
      ≤ ∑ i ∈ J, l i * ⨆ i : J, ∑ j ∈ J, gram A i j * l j := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul_of_nonneg_left
          (le_ciSup (f := fun i : J => ∑ j ∈ J, gram A i j * l j) (Set.finite_range _).bddAbove ⟨i, hi⟩)
          (hl.1 i)
    _ = ⨆ i : J, ∑ j ∈ J, gram A i j * l j := by rw [← Finset.sum_mul, hl.2.2, one_mul]

theorem hoff_vS_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (J : Finset (Fin m))
    (hne : J.Nonempty) (hli : LinearIndependent ℝ (fun j : J => A j)) : 0 < vS A J := by
  classical
  obtain ⟨r, hr, hle⟩ := hoff_vS_lower A J hne hli
  haveI : Nonempty (simplexOn J) := by
    obtain ⟨j0, hj0⟩ := hne
    refine ⟨⟨Pi.single j0 1, fun j => ?_, fun j hj => ?_, ?_⟩⟩
    · by_cases h : j = j0
      · subst h; simp
      · simp [h]
    · have : j ≠ j0 := fun h => hj (h ▸ hj0)
      simp [this]
    · simp [hj0]
  exact lt_of_lt_of_le hr (le_ciInf fun l => hle l l.2)

theorem hoff_bound_u' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (J : Finset (Fin m)) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hcJ : ∀ i ∉ J, c i = 0)
    (a : ℝ) (ha : ∀ i ∈ J, ∀ j, |A i j| ≤ a) (j : Fin n) :
    |(∑ i, c i • A i) j| ≤ a * ∑ i, c i := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ i, c i * A i j| ≤ ∑ i, |c i * A i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, c i * a := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hc i)]
        by_cases hi : i ∈ J
        · exact mul_le_mul_of_nonneg_left (ha i hi j) (hc i)
        · rw [hcJ i hi]; simp
    _ = a * ∑ i, c i := by rw [← Finset.sum_mul, mul_comm]

theorem hoff_aS_ge {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (J : Finset (Fin m)) (i : Fin m)
    (hi : i ∈ J) (j : Fin n) : |A i j| ≤ aS A J := by
  unfold aS
  refine le_trans ?_ (le_ciSup (f := fun i : J => ⨆ j, |A i j|) (Set.finite_range _).bddAbove ⟨i, hi⟩)
  exact le_ciSup (f := fun j => |A i j|) (Set.finite_range _).bddAbove j

theorem hoff_aS_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (J : Finset (Fin m)) :
    0 ≤ aS A J := Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => abs_nonneg _

theorem hoff_eq8_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ constC8 A * maxNorm (posPartVec (A *ᵥ x - b)) := by
  classical
  intro x
  have hc8nn : 0 ≤ constC8 A := by
    unfold constC8
    exact Real.iSup_nonneg fun S => div_nonneg (hoff_aS_nonneg A S.1) S.2.2.le
  by_cases hx : x ∈ solutionSet A b
  · refine ⟨x, hx, ?_⟩
    rw [sub_self]
    have : maxNorm (0 : Fin n → ℝ) = 0 := by simp [maxNorm]
    rw [this]
    exact mul_nonneg hc8nn (hoff_maxNorm_nonneg _)
  · obtain ⟨x₀, hx₀, S, c, hc, hcS, hu, hu0, hAu⟩ := hoff_decomp A b hcons x hx
    refine ⟨x₀, hx₀, ?_⟩
    obtain ⟨J, hJS, hJli, c', hc'0, hc'J, hc'sum⟩ := hoff_cara (fun i => A i) S c hc hcS
    have hu' : x - x₀ = ∑ i, c' i • A i := by rw [hu, ← hc'sum]
    set t := ∑ i, c' i with ht
    have hex : ∃ i, c' i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hu0; rw [hu']; simp [h]
    obtain ⟨i0, hi0⟩ := hex
    have hi0J : i0 ∈ J := by by_contra h; exact hi0 (hc'J i0 h)
    have hi0pos : 0 < c' i0 := lt_of_le_of_ne (hc'0 i0) (Ne.symm hi0)
    have htpos : 0 < t := lt_of_lt_of_le hi0pos
      (Finset.single_le_sum (f := c') (fun i _ => hc'0 i) (Finset.mem_univ i0))
    have hne : J.Nonempty := ⟨i0, hi0J⟩
    have hvpos : 0 < vS A J := hoff_vS_pos A J hne hJli
    obtain ⟨r, hr, hle⟩ := hoff_vS_lower A J hne hJli
    have htJ : ∑ j ∈ J, c' j = t := by
      rw [ht]; exact Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => hc'J i hi)
    set μ : Fin m → ℝ := fun j => c' j / t with hμ
    have hμS : μ ∈ simplexOn J := by
      refine ⟨fun j => div_nonneg (hc'0 j) htpos.le, fun j hj => by simp [hμ, hc'J j hj], ?_⟩
      simp only [hμ]
      rw [← Finset.sum_div, htJ, div_self htpos.ne']
    haveI : Nonempty J := ⟨⟨i0, hi0J⟩⟩
    obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun i : J => ∑ j ∈ J, gram A i j * μ j)
    have hvle : vS A J ≤ ∑ j ∈ J, gram A k j * μ j := by
      rw [hk]
      unfold vS
      exact ciInf_le (f := fun l : simplexOn J => ⨆ i : J, ∑ j ∈ J, gram A i j * (l : Fin m → ℝ) j)
        ⟨r, by rintro _ ⟨l, rfl⟩; exact hle l l.2⟩ ⟨μ, hμS⟩
    have hkS : (k : Fin m) ∈ S := hJS k.2
    have hAuk : (A *ᵥ (x - x₀)) k = t * ∑ j ∈ J, gram A k j * μ j := by
      rw [hu', hoff_Au, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hc'J i hi])]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hμ]; field_simp
    have h1 : maxNorm (x - x₀) ≤ aS A J * t := by
      rw [hu']
      exact hoff_maxNorm_le _ _ (mul_nonneg (hoff_aS_nonneg A J) htpos.le)
        (hoff_bound_u' A J c' hc'0 hc'J _ (fun i hi j => hoff_aS_ge A J i hi j))
    have h2 : vS A J * t ≤ (A *ᵥ (x - x₀)) k := by
      rw [hAuk, mul_comm]
      exact mul_le_mul_of_nonneg_left hvle htpos.le
    have h3 : (A *ᵥ (x - x₀)) k ≤ maxNorm (posPartVec (A *ᵥ x - b)) := by
      rw [hAu k hkS]
      refine le_trans ?_ (hoff_le_maxNorm _ k)
      simp only [posPartVec]
      exact (le_max_left _ _).trans (le_abs_self _)
    have hcoef : aS A J / vS A J ≤ constC8 A := by
      unfold constC8
      exact le_ciSup (f := fun S : {S : Finset (Fin m) // S.Nonempty ∧ 0 < vS A S} => aS A S.1 / vS A S.1)
        (Set.finite_range _).bddAbove ⟨J, hne, hvpos⟩
    have hcoef0 : 0 ≤ aS A J / vS A J := div_nonneg (hoff_aS_nonneg A J) hvpos.le
    calc maxNorm (x - x₀) ≤ aS A J * t := h1
      _ = aS A J / vS A J * (vS A J * t) := by field_simp
      _ ≤ aS A J / vS A J * maxNorm (posPartVec (A *ᵥ x - b)) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hcoef0
      _ ≤ constC8 A * maxNorm (posPartVec (A *ᵥ x - b)) :=
          mul_le_mul_of_nonneg_right hcoef (hoff_maxNorm_nonneg _)

end HoffmanBound.ErrorBound

open HoffmanBound.ErrorBound
open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ constC8 A * maxNorm (posPartVec (A *ᵥ x - b)) := by
  exact hoff_eq8_core A b hcons
