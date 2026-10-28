-- Prove2me | solution 1 for HighDimStat.NonparametricLS.thm13_6_critical_radius_exists_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:22:54.532785+00:00
-- url     : https://prove2.me/submissions/706b1c35-6f48-4698-a72f-9b5cdda58f04

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace S99Crit

open MeasureTheory ProbabilityTheory HighDimStat.NonparametricLS

variable {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

noncomputable def F (x : Fin n → X) (w : Fin n → Ω → ℝ) (h : X → ℝ) (ω : Ω) : ℝ :=
  |(∑ i, w i ω * h (x i)) / n|

noncomputable def S (x : Fin n → X) (w : Fin n → Ω → ℝ) (H : Set (X → ℝ)) (δ : ℝ) (ω : Ω) :
    ℝ :=
  ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ}, F x w h.1 ω

lemma empiricalNorm_smul (x : Fin n → X) (h : X → ℝ) (α : ℝ) :
    empiricalNorm x (fun z => α * h z) = |α| * empiricalNorm x h := by
  unfold empiricalNorm empiricalNormSq
  have : (∑ i, (α * h (x i)) ^ 2) / (n : ℝ) = α ^ 2 * ((∑ i, (h (x i)) ^ 2) / n) := by
    rw [mul_div_assoc', Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma F_smul (x : Fin n → X) (w : Fin n → Ω → ℝ) (h : X → ℝ) (α : ℝ) (ω : Ω) :
    F x w (fun z => α * h z) ω = |α| * F x w h ω := by
  unfold F
  have : (∑ i, w i ω * (α * h (x i))) / (n : ℝ) = α * ((∑ i, w i ω * h (x i)) / n) := by
    rw [mul_div_assoc', Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [this, abs_mul]

lemma F_nonneg (x : Fin n → X) (w : Fin n → Ω → ℝ) (h : X → ℝ) (ω : Ω) : 0 ≤ F x w h ω :=
  abs_nonneg _

lemma F_bound (x : Fin n → X) (w : Fin n → Ω → ℝ) (h : X → ℝ) (ω : Ω) (δ : ℝ)
    (hh : empiricalNorm x h ≤ δ) :
    F x w h ω ≤ Real.sqrt ((∑ i, (w i ω) ^ 2) * (n * δ ^ 2)) / n := by
  unfold F
  rw [abs_div, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.abs_le_sqrt
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h0 : 0 ≤ empiricalNorm x h := Real.sqrt_nonneg _
    have hsq : empiricalNorm x h ^ 2 = (∑ i, (h (x i)) ^ 2) / n := by
      unfold empiricalNorm empiricalNormSq
      rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) hn'.le)]
    have : (∑ i, (h (x i)) ^ 2) = n * empiricalNorm x h ^ 2 := by
      rw [hsq]; field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hn'.le
    exact pow_le_pow_left₀ h0 hh 2

lemma bdd (x : Fin n → X) (w : Fin n → Ω → ℝ) (H : Set (X → ℝ)) (δ : ℝ) (ω : Ω) :
    BddAbove (Set.range fun h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ} => F x w h.1 ω) := by
  refine ⟨Real.sqrt ((∑ i, (w i ω) ^ 2) * (n * δ ^ 2)) / n, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact F_bound x w h.1 ω δ h.2.2

lemma S_nonneg (x : Fin n → X) (w : Fin n → Ω → ℝ) (H : Set (X → ℝ)) (δ : ℝ) (ω : Ω) :
    0 ≤ S x w H δ ω :=
  Real.iSup_nonneg fun h => F_nonneg x w h.1 ω

lemma le_S (x : Fin n → X) (w : Fin n → Ω → ℝ) (H : Set (X → ℝ)) (δ : ℝ) (ω : Ω)
    (h : X → ℝ) (hH : h ∈ H) (hh : empiricalNorm x h ≤ δ) : F x w h ω ≤ S x w H δ ω :=
  le_ciSup (f := fun h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ} => F x w h.1 ω)
    (bdd x w H δ ω) ⟨h, hH, hh⟩

lemma S_scale (x : Fin n → X) (w : Fin n → Ω → ℝ) (H : Set (X → ℝ)) (hH : IsStarShaped H)
    (δ t : ℝ) (hδ : 0 < δ) (hδt : δ ≤ t) (ω : Ω) :
    S x w H t ω ≤ (t / δ) * S x w H δ ω := by
  have ht : 0 < t := hδ.trans_le hδt
  unfold S
  by_cases hne : Nonempty {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ t}
  · apply ciSup_le
    rintro ⟨h, hmem, hh⟩
    set α := δ / t
    have hα0 : 0 ≤ α := div_nonneg hδ.le ht.le
    have hα1 : α ≤ 1 := (div_le_one ht).2 hδt
    have hmem' := hH h hmem α ⟨hα0, hα1⟩
    have hn' : empiricalNorm x (fun z => α * h z) ≤ δ := by
      rw [empiricalNorm_smul, abs_of_nonneg hα0]
      calc α * empiricalNorm x h ≤ α * t := mul_le_mul_of_nonneg_left hh hα0
        _ = δ := by simp [α]; field_simp
    have := le_S x w H δ ω _ hmem' hn'
    rw [F_smul, abs_of_nonneg hα0] at this
    show F x w h ω ≤ t / δ * S x w H δ ω
    have e : F x w h ω = (t / δ) * (α * F x w h ω) := by
      simp only [α]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this (div_nonneg ht.le hδ.le)
  · rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty]
    exact mul_nonneg (div_nonneg ht.le hδ.le) (S_nonneg x w H δ ω)

lemma S_mono (x : Fin n → X) (w : Fin n → Ω → ℝ) (H : Set (X → ℝ))
    (δ t : ℝ) (hδt : δ ≤ t) (ω : Ω) :
    S x w H δ ω ≤ S x w H t ω := by
  unfold S
  by_cases hne : Nonempty {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ}
  · apply ciSup_le
    rintro ⟨h, hmem, hh⟩
    exact le_S x w H t ω h hmem (hh.trans hδt)
  · rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty]
    exact S_nonneg x w H t ω

lemma G_eq (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) (H : Set (X → ℝ)) (δ : ℝ) :
    localGaussianComplexity x w P H δ = ∫ ω, S x w H δ ω ∂P := rfl

/-- nondegenerate linear combination of iid gaussians has positive expected abs value -/
lemma pos_integral (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hw : IsIIDStdGaussian P w) (a : Fin n → ℝ) (ha : ∃ i, a i ≠ 0) :
    Integrable (fun ω => |(∑ i, w i ω * a i) / n|) P ∧
    0 < ∫ ω, |(∑ i, w i ω * a i) / n| ∂P := by
  obtain ⟨hm, hind, hg⟩ := hw
  have hL2 : ∀ i, MemLp (w i) 2 P := by
    intro i
    have h1 : MemLp id 2 (P.map (w i)) := by rw [hg i]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hm i).aemeasurable).1 h1
  have hvar : ∀ i, variance (w i) P = 1 := by
    intro i
    have := variance_map (X := id) (μ := P) (Y := w i) aemeasurable_id (hm i).aemeasurable
    rw [hg i, variance_id_gaussianReal] at this
    simpa using this.symm
  set Y : Fin n → Ω → ℝ := fun i ω => w i ω * a i with hY
  have hYL2 : ∀ i ∈ (Finset.univ : Finset (Fin n)), MemLp (Y i) 2 P :=
    fun i _ => (hL2 i).mul_const (a i)
  have hYind : Set.Pairwise ↑(Finset.univ : Finset (Fin n)) fun i j => Y i ⟂ᵢ[P] Y j := by
    intro i _ j _ hij
    have := hind.indepFun hij
    exact this.comp (φ := fun t => t * a i) (ψ := fun t => t * a j)
      (measurable_id.mul_const _) (measurable_id.mul_const _)
  have hvs := IndepFun.variance_sum hYL2 hYind
  have hsumfun : (∑ i ∈ (Finset.univ : Finset (Fin n)), Y i) = fun ω => ∑ i, w i ω * a i := by
    funext ω; simp [hY, Finset.sum_apply]
  rw [hsumfun] at hvs
  have hvs2 : variance (fun ω => ∑ i, w i ω * a i) P = ∑ i, a i ^ 2 := by
    rw [hvs]; apply Finset.sum_congr rfl; intro i _
    simp only [hY]; rw [variance_mul_const, hvar]; ring
  have hZL2 : MemLp (fun ω => ∑ i, w i ω * a i) 2 P := by
    rw [← hsumfun]; exact memLp_finsetSum' _ hYL2
  have hint : Integrable (fun ω => |(∑ i, w i ω * a i) / n|) P :=
    ((hZL2.integrable (by norm_num)).div_const _).abs
  refine ⟨hint, ?_⟩
  have hI0 : 0 ≤ ∫ ω, |(∑ i, w i ω * a i) / n| ∂P := integral_nonneg fun ω => abs_nonneg _
  rcases hI0.lt_or_eq with h | h
  · exact h
  exfalso
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) hint).1 h.symm
  have hn : (n : ℝ) ≠ 0 := by
    obtain ⟨i, _⟩ := ha
    have : 0 < n := Fin.pos i
    exact_mod_cast this.ne'
  have hz' : (fun ω => ∑ i, w i ω * a i) =ᵐ[P] 0 := by
    filter_upwards [hz] with ω hω
    simp only [Pi.zero_apply, abs_eq_zero, div_eq_zero_iff, hn, or_false] at hω
    simpa using hω
  rw [variance_congr hz', variance_zero] at hvs2
  obtain ⟨i, hi⟩ := ha
  have : 0 < ∑ j, a j ^ 2 :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < a i ^ 2) (Finset.single_le_sum (fun j _ => sq_nonneg (a j))
      (Finset.mem_univ i))
  linarith

end S99Crit

open HighDimStat.NonparametricLS MeasureTheory in
theorem solution {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hw : IsIIDStdGaussian P w)
    (H : Set (X → ℝ)) (hH : IsStarShaped H)
    (hH0 : ∃ h ∈ H, empiricalNorm x h ≠ 0)
    (hmeas : ∀ δ : ℝ, 0 < δ →
      Integrable (fun ω => ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δ},
        |(∑ i, w i ω * h.1 (x i)) / n|) P) :
    (∀ δ t : ℝ, 0 < δ → δ ≤ t →
        localGaussianComplexity x w P H t / t ≤ localGaussianComplexity x w P H δ / δ) ∧
      ∀ c : ℝ, 0 < c →
        ∃ δ, IsLeast {δ : ℝ | 0 < δ ∧ localGaussianComplexity x w P H δ / δ ≤ c * δ} δ := by
  open S99Crit in
  set G := localGaussianComplexity x w P H with hGdef
  have hI : ∀ δ, 0 < δ → Integrable (S x w H δ) P := hmeas
  have Gnn : ∀ δ, 0 ≤ G δ := fun δ => integral_nonneg fun ω => S_nonneg x w H δ ω
  have Gscale : ∀ δ t, 0 < δ → δ ≤ t → G t ≤ (t / δ) * G δ := by
    intro δ t hδ hδt
    rw [hGdef, G_eq, G_eq, ← integral_const_mul]
    exact integral_mono (hI t (hδ.trans_le hδt)) ((hI δ hδ).const_mul _)
      fun ω => S_scale x w H hH δ t hδ hδt ω
  have Gmono : ∀ δ t, 0 < δ → δ ≤ t → G δ ≤ G t := by
    intro δ t hδ hδt
    rw [hGdef, G_eq, G_eq]
    exact integral_mono (hI δ hδ) (hI t (hδ.trans_le hδt)) fun ω => S_mono x w H δ t hδt ω
  refine ⟨?_, ?_⟩
  · intro δ t hδ hδt
    have ht : 0 < t := hδ.trans_le hδt
    rw [div_le_div_iff₀ ht hδ]
    have := Gscale δ t hδ hδt
    calc G t * δ ≤ (t / δ) * G δ * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = G δ * t := by field_simp
  · intro c hc
    -- lower bound
    obtain ⟨h0, h0H, h0ne⟩ := hH0
    set r := empiricalNorm x h0
    have hr : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0ne)
    have ha : ∃ i, h0 (x i) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply h0ne
      simp [r, empiricalNorm, empiricalNormSq, hcon]
    obtain ⟨hFint, hFpos⟩ := pos_integral w P hw (fun i => h0 (x i)) ha
    set K := ∫ ω, |(∑ i, w i ω * h0 (x i)) / n| ∂P
    have Glow : ∀ δ, 0 < δ → δ ≤ r → δ * (K / r) ≤ G δ := by
      intro δ hδ hδr
      have hα0 : 0 ≤ δ / r := div_nonneg hδ.le hr.le
      have hmem := hH h0 h0H (δ / r) ⟨hα0, (div_le_one hr).2 hδr⟩
      have hnorm : empiricalNorm x (fun z => δ / r * h0 z) ≤ δ := by
        rw [empiricalNorm_smul, abs_of_nonneg hα0]
        apply le_of_eq; field_simp; rfl
      have hpt : ∀ ω, (δ / r) * |(∑ i, w i ω * h0 (x i)) / n| ≤ S x w H δ ω := by
        intro ω
        have := le_S x w H δ ω _ hmem hnorm
        rw [F_smul, abs_of_nonneg hα0] at this
        exact this
      have := integral_mono (hFint.const_mul (δ / r)) (hI δ hδ) hpt
      rw [integral_const_mul] at this
      rw [hGdef, G_eq]
      calc δ * (K / r) = δ / r * K := by ring
        _ ≤ _ := this
    have hκ : 0 < K / r := div_pos hFpos hr
    set A := {δ : ℝ | 0 < δ ∧ G δ / δ ≤ c * δ}
    have memA : ∀ δ, 0 < δ → (δ ∈ A ↔ G δ ≤ c * δ ^ 2) := by
      intro δ hδ
      simp only [A, Set.mem_ofPred_eq, hδ, true_and]
      rw [div_le_iff₀ hδ]; ring_nf
    set m := min r ((K / r) / c)
    have hm : 0 < m := lt_min hr (div_pos hκ hc)
    have lowA : ∀ δ ∈ A, m ≤ δ := by
      intro δ hδA
      have hδ : 0 < δ := hδA.1
      have h2 := (memA δ hδ).1 hδA
      by_contra hlt
      push Not at hlt
      have h1 : δ < r := lt_of_lt_of_le hlt (min_le_left _ _)
      have h3 : δ < (K / r) / c := lt_of_lt_of_le hlt (min_le_right _ _)
      have h4 := Glow δ hδ h1.le
      have : c * δ < K / r := by rwa [lt_div_iff₀ hc, mul_comm] at h3
      nlinarith
    have upA : ∀ δ ∈ A, ∀ t, δ ≤ t → t ∈ A := by
      intro δ hδA t hδt
      have hδ : 0 < δ := hδA.1
      have ht : 0 < t := hδ.trans_le hδt
      rw [memA t ht]
      have h2 := (memA δ hδ).1 hδA
      have := Gscale δ t hδ hδt
      calc G t ≤ (t / δ) * G δ := this
        _ ≤ (t / δ) * (c * δ ^ 2) := mul_le_mul_of_nonneg_left h2 (div_nonneg ht.le hδ.le)
        _ = c * t * δ := by field_simp
        _ ≤ c * t * t := mul_le_mul_of_nonneg_left hδt (by positivity)
        _ = c * t ^ 2 := by ring
    -- nonempty
    set d0 := max 1 (G 1 / c)
    have hd0 : d0 ∈ A := by
      have h1 : (1 : ℝ) ≤ d0 := le_max_left _ _
      have hpos : 0 < d0 := lt_of_lt_of_le one_pos h1
      rw [memA d0 hpos]
      have := Gscale 1 d0 one_pos h1
      have h2 : G 1 ≤ c * d0 := by
        have := le_max_right 1 (G 1 / c)
        rwa [div_le_iff₀ hc, mul_comm] at this
      calc G d0 ≤ d0 / 1 * G 1 := this
        _ ≤ d0 / 1 * (c * d0) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = c * d0 ^ 2 := by ring
    have hbdd : BddBelow A := ⟨m, lowA⟩
    have hne : A.Nonempty := ⟨d0, hd0⟩
    set ds := sInf A
    have hds : m ≤ ds := le_csInf hne lowA
    have hdspos : 0 < ds := hm.trans_le hds
    refine ⟨ds, ?_, fun δ hδ => csInf_le hbdd hδ⟩
    -- ds ∈ A
    have gtA : ∀ t, ds < t → t ∈ A := by
      intro t ht
      obtain ⟨a, haA, hat⟩ := exists_lt_of_csInf_lt hne ht
      exact upA a haA t hat.le
    rw [memA ds hdspos]
    by_contra hcon
    push Not at hcon
    -- G ds > c ds^2 ; pick t slightly larger
    have hcont : ∀ t, ds < t → G ds ≤ c * t ^ 2 := by
      intro t ht
      have := (memA t (hdspos.trans ht)).1 (gtA t ht)
      exact (Gmono ds t hdspos ht.le).trans this
    -- c t^2 → c ds^2 as t → ds
    have hlim : Filter.Tendsto (fun t : ℝ => c * t ^ 2) (nhdsWithin ds (Set.Ioi ds))
        (nhds (c * ds ^ 2)) :=
      ((continuous_const.mul (continuous_pow 2)).tendsto ds).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in nhdsWithin ds (Set.Ioi ds), c * t ^ 2 < G ds :=
      hlim (Iio_mem_nhds hcon)
    obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
    exact absurd (hcont t ht2) (not_le.2 ht1)
