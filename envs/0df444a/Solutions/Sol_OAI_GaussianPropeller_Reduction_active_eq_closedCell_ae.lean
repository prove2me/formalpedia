-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.active_eq_closedCell_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:21:54.80115+00:00
-- url     : https://prove2.me/submissions/abb39e05-b80b-43cd-b708-05b412284bbd

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


open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_merge_contra {d k : ℕ} [NeZero k] {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) {i j : Fin k} (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0)
    (hj : gaussian d (A j) ≠ 0) (hz : centroid (A i) = centroid (A j)) : False := by
  classical
  have hP := hA.1.1
  have hdisj : AEDisjoint (gaussian d) (A i) (A j) := by
    rw [AEDisjoint, measure_eq_zero_iff_ae_notMem]
    filter_upwards [hP.2] with x hx
    rintro ⟨h1, h2⟩
    obtain ⟨l, -, hu⟩ := hx
    exact hij ((hu i h1).trans (hu j h2).symm)
  have hcu : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := by
    unfold centroid
    exact setIntegral_union₀ hdisj (hP.1 j).nullMeasurableSet (hn2_integrable_id d).integrableOn
      (hn2_integrable_id d).integrableOn
  have hmP : IsPartition (merge A i j) := by
    refine ⟨fun l => ?_, ?_⟩
    · unfold merge
      split_ifs
      · exact (hP.1 i).union (hP.1 j)
      · exact MeasurableSet.empty
      · exact hP.1 l
    · filter_upwards [hP.2] with x hx
      obtain ⟨l, hl, hu⟩ := hx
      have key : ∀ m, x ∈ merge A i j m ↔ m = (if l = j then i else l) := by
        intro m
        unfold merge
        by_cases hmi : m = i
        · subst hmi
          simp only [if_true, Set.mem_union]
          constructor
          · rintro (h | h)
            · rw [hu m h]; simp
            · rw [hu j h]; simp
          · intro h
            by_cases hlj : l = j
            · subst hlj; exact Or.inr hl
            · rw [if_neg hlj] at h; subst h; exact Or.inl hl
        · rw [if_neg hmi]
          by_cases hmj : m = j
          · subst hmj
            simp only [if_true, Set.mem_empty_iff_false, false_iff]
            intro h
            by_cases hlj : l = m
            · rw [if_pos hlj] at h; exact hmi h
            · rw [if_neg hlj] at h; exact hlj h.symm
          · rw [if_neg hmj]
            constructor
            · intro h; have := hu m h; subst this; rw [if_neg hmj]
            · intro h
              by_cases hlj : l = j
              · rw [if_pos hlj] at h; exact absurd h hmi
              · rw [if_neg hlj] at h; subst h; exact hl
      exact ⟨_, (key _).mpr rfl, fun m hm => (key m).mp hm⟩
  have hval : value A ≤ value (merge A i j) := by
    unfold value
    rw [← sub_nonneg, ← Finset.sum_sub_distrib,
      Finset.sum_eq_add i j hij (fun l _ hl => by simp [merge, hl.1, hl.2]) (by simp) (by simp)]
    simp only [merge, if_true, if_neg hij.symm, centroid_empty, norm_zero, hcu, hz]
    rw [← two_smul ℝ, norm_smul]
    have := sq_nonneg ‖centroid (A j)‖
    norm_num; nlinarith
  have hmO : Optimal (merge A i j) :=
    ⟨hmP, fun B hB => (hA.1.2 B hB).trans hval⟩
  have hc := hA.2 _ hmO
  have hact : activeLabels (merge A i j) = (activeLabels A).erase j := by
    ext l
    simp only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    unfold merge
    by_cases hli : l = i
    · subst hli
      simp only [if_true]
      refine ⟨fun _ => ⟨hij, hi⟩, fun _ => ?_⟩
      intro h0; exact hi (measure_mono_null Set.subset_union_left h0)
    · rw [if_neg hli]
      by_cases hlj : l = j
      · subst hlj; simp
      · rw [if_neg hlj]; simp [hlj]
  have hjm : j ∈ activeLabels A := by simp [activeLabels, hj]
  unfold activeCount at hc
  rw [hact, Finset.card_erase_of_mem hjm] at hc
  have : 0 < (activeLabels A).card := Finset.card_pos.mpr ⟨j, hjm⟩
  omega

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction MeasureTheory ProbabilityTheory in
open scoped RealInnerProductSpace in
theorem hn2_hyperplane_null {d : ℕ} (z : Space d) (hz : z ≠ 0) (c : ℝ) :
    gaussian d {x | ⟪z, x⟫ = c} = 0 := by
  let L : StrongDual ℝ (Space d) := innerSL ℝ z
  have hset : {x : Space d | ⟪z, x⟫ = c} = L ⁻¹' {c} := by
    ext x; simp [L]
  rw [hset, gaussian, ← Measure.map_apply L.continuous.measurable (measurableSet_singleton c),
    IsGaussian.map_eq_gaussianReal, variance_dual_stdGaussian]
  have hL : ‖L‖ = ‖z‖ := innerSL_apply_norm ℝ z
  have hv : (‖L‖ ^ 2).toNNReal ≠ 0 := by
    rw [hL]; intro h
    rw [Real.toNNReal_eq_zero] at h
    have : 0 < ‖z‖ := norm_pos_iff.mpr hz
    nlinarith
  exact gaussianReal_absolutelyContinuous _ hv (Real.volume_singleton)

theorem solution {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) :
    A i =ᵐ[gaussian d] closedCell (fun j => centroid (A j)) i := by
  classical
  set z : Fin k → Space d := fun j => centroid (A j) with hzdef
  have hP := hA.1.1
  -- Step 1: a.e. on A j, the score of j is maximal.
  have hint : Integrable (fun x => ∑ j, (A j).indicator (fun x => ⟪z j, x⟫) x) (gaussian d) :=
    integrable_finsetSum _ (fun j _ => (hn2_integrable_inner (z j)).indicator (hP.1 j))
  have hnn : 0 ≤ᵐ[gaussian d] fun x => scoreMax z x - ∑ j, (A j).indicator (fun x => ⟪z j, x⟫) x := by
    filter_upwards [hP.2] with x hx
    obtain ⟨l, hl, hu⟩ := hx
    rw [Finset.sum_eq_single l (fun j _ hj => Set.indicator_of_notMem (fun h => hj (hu j h)) _)
      (by simp), Set.indicator_of_mem hl]
    simp only [Pi.zero_apply, sub_nonneg]
    exact Finset.le_sup' (fun j => ⟪z j, x⟫) (Finset.mem_univ l)
  have hzero : ∫ x, (scoreMax z x - ∑ j, (A j).indicator (fun x => ⟪z j, x⟫) x) ∂gaussian d = 0 := by
    rw [integral_sub (hn2_scoreMax_integrable _) hint]
    have h1 := hn2_width_opt hA.1
    have h2 := hn2_pair_eq hP.1 (moments A)
    rw [real_inner_self_eq_norm_sq, hn2_norm_moments_sq] at h2
    unfold width at h1
    change ∫ x, scoreMax z x ∂gaussian d = value A at h1
    change value A = ∫ x, ∑ j, (A j).indicator (fun x => ⟪z j, x⟫) x ∂gaussian d at h2
    rw [h1, ← h2, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn ((hn2_scoreMax_integrable _).sub hint)).mp hzero
  have step1 : ∀ᵐ x ∂gaussian d, ∀ j, x ∈ A j → x ∈ closedCell z j := by
    filter_upwards [hae, hP.2] with x hx hx2
    intro j hj
    obtain ⟨l, hl, hu⟩ := hx2
    have hjl := hu j hj; subst hjl
    simp only [Pi.zero_apply] at hx
    rw [Finset.sum_eq_single j (fun m _ hm => Set.indicator_of_notMem (fun h => hm (hu m h)) _)
      (by simp), Set.indicator_of_mem hj] at hx
    intro m
    have := Finset.le_sup' (fun j => ⟪z j, x⟫) (Finset.mem_univ m)
    change ⟪z m, x⟫ ≤ scoreMax z x at this
    linarith
  -- Step 2
  have step2 : ∀ j, ∀ᵐ x ∂gaussian d, j ≠ i → x ∉ A j ∨ ⟪z i - z j, x⟫ ≠ 0 := by
    intro j
    by_cases hj0 : gaussian d (A j) = 0
    · rw [measure_eq_zero_iff_ae_notMem] at hj0
      filter_upwards [hj0] with x hx _ using Or.inl hx
    · by_cases hji : j = i
      · exact Filter.Eventually.of_forall (fun x h => absurd hji h)
      · have hne : z i - z j ≠ 0 := by
          intro h
          exact hn2_merge_contra hA (Ne.symm hji) hi hj0 (sub_eq_zero.mp h)
        have hnull := hn2_hyperplane_null (z i - z j) hne 0
        rw [measure_eq_zero_iff_ae_notMem] at hnull
        filter_upwards [hnull] with x hx _ using Or.inr hx
  rw [← ae_all_iff] at step2
  filter_upwards [step1, step2, hP.2] with x h1 h2 h3
  apply propext
  constructor
  · exact h1 i
  · intro hc
    obtain ⟨l, hl, hu⟩ := h3
    by_cases hli : l = i
    · rw [← hli]; exact hl
    · exfalso
      rcases h2 l hli with h | h
      · exact h hl
      · apply h
        have a1 := h1 l hl i
        have a2 := hc l
        rw [inner_sub_left]; linarith

