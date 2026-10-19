-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.optimal_loss_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:19:05.706338+00:00
-- url     : https://prove2.me/submissions/9777558e-973e-49e8-a351-ede9d18f034f

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_integrable_id (d : ℕ) : Integrable (fun x : Space d => x) (gaussian d) := by
  unfold gaussian; exact IsGaussian.integrable_id

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_integrable_inner {d : ℕ} (w : Space d) :
    Integrable (fun x : Space d => ⟪w, x⟫) (gaussian d) :=
  (hn2_integrable_id d).const_inner w

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreMax_integrable {d k : ℕ} [NeZero k] (v : Fin k → Space d) :
    Integrable (fun x => scoreMax v x) (gaussian d) := by
  refine Integrable.mono' (g := fun x => ∑ i, |⟪v i, x⟫|)
    (integrable_finsetSum _ (fun i _ => (hn2_integrable_inner (v i)).abs)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold scoreMax
    apply Continuous.finset_sup'_apply
    intro i _; fun_prop
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h0 := Finset.le_sup' (fun i => ⟪v i, x⟫) (Finset.mem_univ (0 : Fin k))
      have h1 := Finset.single_le_sum (f := fun i => |⟪v i, x⟫|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ (0 : Fin k))
      have h2 := neg_abs_le ⟪v 0, x⟫
      change ⟪v 0, x⟫ ≤ scoreMax v x at h0
      linarith
    · apply Finset.sup'_le
      intro i _
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |⟪v i, x⟫|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ i))

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_pair_eq {d k : ℕ} [NeZero k] {A : Fin k → Set (Space d)} (hA : ∀ i, MeasurableSet (A i))
    (v : Tuple d k) : ⟪v, moments A⟫ =
      ∫ x, ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x ∂gaussian d := by
  classical
  have hcent : ∀ i, ⟪v.ofLp i, centroid (A i)⟫ = ∫ x, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x ∂gaussian d := by
    intro i
    rw [integral_indicator (hA i), centroid, integral_inner ((hn2_integrable_id d).integrableOn)]
  rw [PiLp.inner_apply]
  change ∑ i, ⟪v.ofLp i, centroid (A i)⟫ = _
  simp_rw [hcent]
  rw [← integral_finsetSum _ (fun i _ => (hn2_integrable_inner (v.ofLp i)).indicator (hA i))]

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreCell_unique {d k : ℕ} [NeZero k] (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ⟪v j, x⟫) Finset.univ_nonempty
  have hS : (Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫)).Nonempty := ⟨m, by simp⟩
  set i := (Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫)).min' hS with hi
  have hiS : i ∈ Finset.univ.filter (fun j => ⟪v j, x⟫ = ⟪v m, x⟫) := Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiS
  refine ⟨i, ⟨fun j => hiS ▸ hm j (Finset.mem_univ _), fun j hj => ?_⟩, ?_⟩
  · rcases lt_or_eq_of_le (hm j (Finset.mem_univ _)) with h | h
    · rw [hiS]; exact h
    · exfalso
      have : i ≤ j := Finset.min'_le _ _ (by simp [h])
      exact absurd hj (not_lt.mpr this)
  · rintro i' ⟨h1, h2⟩
    have e' : ⟪v i', x⟫ = ⟪v m, x⟫ := le_antisymm (hm i' (Finset.mem_univ _)) (h1 m)
    rcases lt_trichotomy i' i with h | h | h
    · exfalso
      have : i ≤ i' := Finset.min'_le _ _ (by simp [e'])
      exact absurd h (not_lt.mpr this)
    · exact h
    · exfalso
      have := h2 i h
      rw [hiS, e'] at this
      exact lt_irrefl _ this

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreCell_measurable {d k : ℕ} [NeZero k] (v : Fin k → Space d) (i : Fin k) :
    MeasurableSet (scoreCell v i) := by
  have : scoreCell v i = (⋂ j, {x | ⟪v j, x⟫ ≤ ⟪v i, x⟫}) ∩ ⋂ j, ⋂ (_ : j < i), {x | ⟪v j, x⟫ < ⟪v i, x⟫} := by
    ext x; simp [scoreCell]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_) (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · exact measurableSet_lt (by fun_prop) (by fun_prop)

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_width_eq_pair {d k : ℕ} [NeZero k] (v : Tuple d k) :
    width v = ⟪v, moments (scoreCell v.ofLp)⟫ := by
  classical
  rw [hn2_pair_eq (hn2_scoreCell_measurable _), width]
  congr 1; funext x
  obtain ⟨i, hi, hu⟩ := hn2_scoreCell_unique v.ofLp x
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => hi.1 j)
    · exact Finset.le_sup' (fun i => ⟪v.ofLp i, x⟫) (Finset.mem_univ i)
  · intro j _ hj
    exact Set.indicator_of_notMem (fun h => hj (hu j h)) _
  · simp

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreCell_partition {d k : ℕ} [NeZero k] (v : Fin k → Space d) :
    IsPartition (scoreCell v) :=
  ⟨hn2_scoreCell_measurable v, Filter.Eventually.of_forall (hn2_scoreCell_unique v)⟩

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_norm_moments_sq {d k : ℕ} [NeZero k] (A : Fin k → Set (Space d)) :
    ‖moments A‖ ^ 2 = value A := by
  rw [PiLp.norm_sq_eq_of_L2]; rfl

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_pair_le_width {d k : ℕ} [NeZero k] {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) : ⟪v, moments A⟫ ≤ width v := by
  classical
  have hcent : ∀ i, ⟪v.ofLp i, centroid (A i)⟫ = ∫ x, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x ∂gaussian d := by
    intro i
    rw [integral_indicator (hA.1 i), centroid, integral_inner ((hn2_integrable_id d).integrableOn)]
  rw [PiLp.inner_apply]
  change ∑ i, ⟪v.ofLp i, centroid (A i)⟫ ≤ width v
  simp_rw [hcent]
  rw [← integral_finsetSum _ (fun i _ => (hn2_integrable_inner (v.ofLp i)).indicator (hA.1 i))]
  unfold width
  apply integral_mono_ae (integrable_finsetSum _ (fun i _ => (hn2_integrable_inner (v.ofLp i)).indicator (hA.1 i)))
    (hn2_scoreMax_integrable _)
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, hu⟩ := hx
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi]
    exact Finset.le_sup' (fun i => ⟪v.ofLp i, x⟫) (Finset.mem_univ i)
  · intro j _ hj
    exact Set.indicator_of_notMem (fun h => hj (hu j h)) _
  · simp

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_sum_centroid {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : ∑ i, centroid (A i) = 0 := by
  classical
  have hint : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian; exact IsGaussian.integrable_id
  have h1 : ∀ i, centroid (A i) = ∫ x, (A i).indicator (fun x => x) x ∂gaussian d := fun i =>
    (integral_indicator (hA.1 i)).symm
  simp_rw [h1]
  rw [← integral_finsetSum _ (fun i _ => hint.indicator (hA.1 i))]
  have h2 : (fun x => ∑ i, (A i).indicator (fun x : Space d => x) x) =ᵐ[gaussian d] fun x => x := by
    filter_upwards [hA.2] with x hx
    obtain ⟨i, hi, hu⟩ := hx
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hj
      exact Set.indicator_of_notMem (fun h => hj (hu j h)) _
    · simp
  rw [integral_congr_ae h2]
  unfold gaussian
  exact integral_id_stdGaussian

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_scoreMax_recentered {d k : ℕ} [NeZero k] (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) (x : Space d) :
    scoreMax (recentered z i).ofLp x = omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
  classical
  have hk1 : (1:ℝ) < k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < (k:ℝ) - 1 := by linarith
  have hr : ∀ j, (recentered z i).ofLp j = if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i := fun j => rfl
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rw [hr]
    by_cases hj : j = i
    · rw [if_pos hj, inner_zero_left]
      have hs : ∑ j ∈ Finset.univ.erase i, ⟪z j, x⟫ = - ⟪z i, x⟫ := by
        rw [← sum_inner]
        have : ∑ j ∈ Finset.univ.erase i, z j = - z i := by
          rw [eq_neg_iff_add_eq_zero, add_comm, Finset.add_sum_erase _ _ (Finset.mem_univ i), hz]
        rw [this, inner_neg_left]
      have hle := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun j => ⟪z j, x⟫)
        (omittedMax hk z i x) (fun j hj => Finset.le_sup' (fun j => ⟪z j,x⟫) hj)
      rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one] at hle
      rw [inner_smul_left]
      simp only [RCLike.conj_to_real]
      have : -(((k:ℝ)-1)⁻¹ * ⟪z i, x⟫) ≤ omittedMax hk z i x := by
        rw [← mul_neg, inv_mul_le_iff₀ hk0]; linarith
      linarith
    · rw [if_neg hj, inner_add_left]
      have := Finset.le_sup' (fun j => ⟪z j,x⟫) (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      change ⟪z j, x⟫ ≤ omittedMax hk z i x at this
      linarith
  · have : omittedMax hk z i x ≤ scoreMax (recentered z i).ofLp x - ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
      apply Finset.sup'_le
      intro j hj
      have := Finset.le_sup' (fun j => ⟪(recentered z i).ofLp j, x⟫) (Finset.mem_univ j)
      change ⟪(recentered z i).ofLp j, x⟫ ≤ scoreMax (recentered z i).ofLp x at this
      rw [hr, if_neg (Finset.ne_of_mem_erase hj), inner_add_left] at this
      linarith
    linarith

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_recentered_norm_sq {d k : ℕ} [NeZero k] (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ‖recentered z i‖^2 = (∑ j, ‖z j‖^2) -
      ((k:ℝ)/((k:ℝ)-1)) * ‖z i‖^2 := by
  classical
  set c : ℝ := ((k:ℝ)-1)⁻¹ with hc
  have hk1 : (1:ℝ) < k := by exact_mod_cast hk
  have hk0 : (k:ℝ) - 1 ≠ 0 := by linarith
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [recentered, PiLp.toLp_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, norm_zero]
  rw [show (0:ℝ)^2 = 0 by norm_num, zero_add]
  have hrest : ∀ j ∈ Finset.univ.erase i, ‖(if j = i then (0 : Space d) else z j + c • z i)‖ ^ 2
      = ‖z j‖^2 + 2 * (c * ⟪z j, z i⟫) + c^2 * ‖z i‖^2 := by
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj), norm_add_sq_real, inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl hrest, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← sum_inner, Finset.sum_const]
  have hs : ∑ j ∈ Finset.univ.erase i, z j = - z i := by
    rw [eq_neg_iff_add_eq_zero, add_comm, Finset.add_sum_erase _ _ (Finset.mem_univ i), hz]
  rw [hs, inner_neg_left, real_inner_self_eq_norm_sq, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hcast]
  have : (k:ℝ)/((k:ℝ)-1) = 1 + c := by rw [hc]; field_simp; ring
  rw [this]
  have : ((k:ℝ) - 1) * (c^2 * ‖z i‖^2) = c * ‖z i‖^2 := by rw [hc]; field_simp
  rw [this]
  ring

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_width_opt {d k : ℕ} [NeZero k] {A : Fin k → Set (Space d)} (hA : Optimal A) :
    width (moments A) = value A := by
  have hv := hn2_norm_moments_sq A
  apply le_antisymm
  · rw [hn2_width_eq_pair]
    set B := scoreCell (moments A).ofLp
    have hB := hA.2 B (hn2_scoreCell_partition _)
    have hw := hn2_norm_moments_sq B
    have h1 := real_inner_le_norm (moments A) (moments B)
    have h2 : ‖moments B‖ ≤ ‖moments A‖ := by
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, hw, hv]; exact hB
    nlinarith [norm_nonneg (moments A), norm_nonneg (moments B)]
  · have := hn2_pair_le_width hA.1 (moments A)
    rw [real_inner_self_eq_norm_sq, hv] at this
    exact this

theorem solution (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : Optimal A) (i : Fin k) :
    value A - Real.sqrt (value A) *
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) ≤
    ∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d := by
  classical
  set z : Fin k → Space d := fun j => centroid (A j) with hzdef
  have hz : ∑ j, z j = 0 := hn2_sum_centroid hA.1
  set r := recentered z i
  have hsplit : ∀ x, scoreMax z x = omittedMax hk z i x + max (⟪z i, x⟫ - omittedMax hk z i x) 0 := by
    intro x
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      by_cases hj : j = i
      · subst hj; have := le_max_left (⟪z j, x⟫ - omittedMax hk z j x) 0; linarith
      · have h1 : ⟪z j, x⟫ ≤ omittedMax hk z i x :=
          Finset.le_sup' (fun j => ⟪z j,x⟫) (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
        have := le_max_right (⟪z i, x⟫ - omittedMax hk z i x) 0; linarith
    · have hM : omittedMax hk z i x ≤ scoreMax z x :=
        Finset.sup'_le _ _ (fun j _ => Finset.le_sup' (fun j => ⟪z j,x⟫) (Finset.mem_univ j))
      have ht : ⟪z i, x⟫ ≤ scoreMax z x := Finset.le_sup' (fun j => ⟪z j,x⟫) (Finset.mem_univ i)
      rcases le_total (⟪z i, x⟫ - omittedMax hk z i x) 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
  have heq : (fun x => max (⟪z i, x⟫ - omittedMax hk z i x) 0) =
      fun x => scoreMax z x - scoreMax r.ofLp x + ⟪((k:ℝ)-1)⁻¹ • z i, x⟫ := by
    funext x; rw [hn2_scoreMax_recentered hk z hz i x, hsplit x]; ring
  change _ ≤ ∫ x, max (⟪z i, x⟫ - omittedMax hk z i x) 0 ∂gaussian d
  have i1 : Integrable (fun x => scoreMax z x - scoreMax r.ofLp x) (gaussian d) :=
    (hn2_scoreMax_integrable _).sub (hn2_scoreMax_integrable _)
  rw [heq, integral_add i1 (hn2_integrable_inner _), integral_sub (hn2_scoreMax_integrable _) (hn2_scoreMax_integrable _),
    integral_inner (hn2_integrable_id d), gaussian, integral_id_stdGaussian, inner_zero_right, add_zero]
  have hw : ∫ x, scoreMax z x ∂stdGaussian (Space d) = value A :=
    hn2_width_opt hA
  rw [hw]
  -- width r ≤ ‖r‖ * sqrt (value A)
  have hwr : ∫ x, scoreMax r.ofLp x ∂stdGaussian (Space d) = ⟪r, moments (scoreCell r.ofLp)⟫ :=
    hn2_width_eq_pair r
  rw [hwr]
  have h1 := real_inner_le_norm r (moments (scoreCell r.ofLp))
  have hB := hA.2 _ (hn2_scoreCell_partition r.ofLp)
  have hmB : ‖moments (scoreCell r.ofLp)‖ ≤ Real.sqrt (value A) := by
    rw [← Real.sqrt_sq (norm_nonneg (moments _))]
    exact Real.sqrt_le_sqrt (by rw [hn2_norm_moments_sq]; exact hB)
  have hr : ‖r‖ = Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) := by
    rw [← Real.sqrt_sq (norm_nonneg r), hn2_recentered_norm_sq hk z hz i]; rfl
  rw [← hr]
  have := mul_le_mul_of_nonneg_left hmB (norm_nonneg r)
  nlinarith [Real.sqrt_nonneg (value A)]

