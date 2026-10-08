-- Prove2me | solution 1 for HoffmanBound.ErrorBound.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:04:18.491886+00:00
-- url     : https://prove2.me/submissions/d19f8f0f-8ba5-41b5-acda-97ce7479f267

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model



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

end HoffmanBound.ErrorBound

open HoffmanBound.ErrorBound
open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x y : Fin n → ℝ)
    (hx : x ∉ solutionSet A b) (hy : IsNearest (solutionSet A b) x y) :
    x ∉ {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} ∧
      IsNearest {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} x y := by
  exact hoff_lemma2_core A b x y hx hy
