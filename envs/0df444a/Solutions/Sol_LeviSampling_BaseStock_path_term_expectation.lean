-- Prove2me | solution 1 for LeviSampling.BaseStock.path_term_expectation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:05:48.779793+00:00
-- url     : https://prove2.me/submissions/e5a57710-5dc9-4435-8d9b-d06897603327

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Estimator
open MeasureTheory
open LeviSampling.BaseStock
theorem g69h2_fubini {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (jj : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F (Measure.pi ν)) :
    ∫ p, F p ∂(Measure.pi ν) =
      ∫ v, ∫ x, F (Fin.insertNth jj x v) ∂(ν jj) ∂(Measure.pi fun k => ν (jj.succAbove k)) := by
  have hmp := (measurePreserving_piFinSuccAbove ν jj).symm
  rw [← hmp.integral_comp' F]
  have hint : Integrable (fun z => F ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) jj).symm z))
      ((ν jj).prod (Measure.pi fun k => ν (jj.succAbove k))) := by
    exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hF
  rw [integral_prod_symm _ hint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rfl

theorem g69h2_extend_insert {n : ℕ} (jj : Fin (n + 1)) (x : ℝ) (v : Fin n → ℝ) :
    extendPath (Fin.insertNth jj x v) =
      Function.update (extendPath (Fin.insertNth jj 0 v)) jj.1 x := by
  funext k
  have hu : Function.update (Fin.insertNth (α := fun _ => ℝ) jj (0:ℝ) v) jj x =
      Fin.insertNth (α := fun _ => ℝ) jj x v :=
    Fin.update_insertNth (α := fun _ => ℝ) jj (0:ℝ) x v
  rw [← hu]
  unfold extendPath
  by_cases hk : k < n + 1
  · rw [dif_pos hk]
    by_cases hkj : k = jj.1
    · subst hkj; simp
    · have : (⟨k, hk⟩ : Fin (n+1)) ≠ jj := fun h => hkj (by rw [← h])
      rw [Function.update_of_ne this, Function.update_of_ne hkj, dif_pos hk]
  · rw [dif_neg hk, Function.update_of_ne (by omega), dif_neg hk]

theorem g69h2_cum_update (P : ℕ → ℝ) (j : ℕ) (x : ℝ) (t k : ℕ) (hk : k ≤ j) :
    cumDemand (Function.update P j x) t k = cumDemand P t k := by
  unfold cumDemand
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  rw [Function.update_of_ne (by omega)]

theorem g69h2_reach_update (L P : ℕ → ℝ) (j : ℕ) (x : ℝ) (t : ℕ) (y : ℝ) :
    reachEvent L (Function.update P j x) t j y ↔ reachEvent L P t j y := by
  unfold reachEvent
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [Finset.mem_Ioc] at hk
  rw [g69h2_cum_update P j x t k hk.2]

theorem g69h2_meas_ext {T : ℕ} (k : ℕ) : Measurable (fun p : Fin T → ℝ => extendPath p k) := by
  unfold extendPath
  by_cases hk : k < T
  · simp only [dif_pos hk]; exact measurable_pi_apply _
  · simp only [dif_neg hk]; exact measurable_const

theorem g69h2_meas_cum {T : ℕ} (t k : ℕ) :
    Measurable (fun p : Fin T → ℝ => cumDemand (extendPath p) t k) := by
  unfold cumDemand
  exact Finset.measurable_sum _ fun i _ => g69h2_meas_ext i

theorem g69h2_meas_reach {T : ℕ} (L : ℕ → ℝ) (t j : ℕ) (y : ℝ) :
    MeasurableSet {p : Fin T → ℝ | reachEvent L (extendPath p) t j y} := by
  unfold reachEvent
  have : {p : Fin T → ℝ | ∀ k ∈ Finset.Ioc t j, L k ≤ y - cumDemand (extendPath p) t k} =
      ⋂ k ∈ Finset.Ioc t j, {p | L k ≤ y - cumDemand (extendPath p) t k} := by
    ext p; simp
  rw [this]
  refine Finset.measurableSet_biInter _ fun k _ => ?_
  exact measurableSet_le measurable_const (measurable_const.sub (g69h2_meas_cum t k))

open Classical in
theorem g69h2_meas_term {T : ℕ} (h b L : ℕ → ℝ) (t j : ℕ) (y : ℝ) :
    Measurable (fun p : Fin T → ℝ => pathTerm h b L (extendPath p) t j y) := by
  unfold pathTerm
  refine Measurable.ite (g69h2_meas_reach L t j y) ?_ measurable_const
  refine measurable_const.add (measurable_const.mul ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (g69h2_meas_ext j) (measurable_const.sub (g69h2_meas_cum t j))

open Classical in
theorem g69h2_meas_rhs {T : ℕ} (μj : Measure ℝ) [IsProbabilityMeasure μj] (h b L : ℕ → ℝ)
    (t j : ℕ) (y : ℝ) :
    Measurable (fun p : Fin T → ℝ => if reachEvent L (extendPath p) t j y then
              nvRightDeriv μj (h j) (b j) (y - cumDemand (extendPath p) t j) else 0) := by
  refine Measurable.ite (g69h2_meas_reach L t j y) ?_ measurable_const
  unfold nvRightDeriv
  refine measurable_const.add (measurable_const.mul ?_)
  exact (ProbabilityTheory.cdf μj).mono.measurable.comp (measurable_const.sub (g69h2_meas_cum t j))

open Classical in
theorem solution (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h b : ℕ → ℝ) (L : ℕ → ℝ) (t j : ℕ) (htj : t < j) (hj : j < T) (y : ℝ) :
    ∫ p, pathTerm h b L (extendPath p) t j y ∂(pathLaw T μ) =
      ∫ p, (if reachEvent L (extendPath p) t j y then
              nvRightDeriv (μ j) (h j) (b j) (y - cumDemand (extendPath p) t j)
            else 0) ∂(pathLaw T μ) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  set jj : Fin (n + 1) := ⟨j, hj⟩
  have hC1 : ∀ p : Fin (n+1) → ℝ, ‖pathTerm h b L (extendPath p) t j y‖ ≤ |b j| + |h j + b j| := by
    intro p
    unfold pathTerm
    rw [Real.norm_eq_abs]
    split_ifs
    · calc |-b j + (h j + b j) * 1| ≤ |-b j| + |(h j + b j) * 1| := abs_add_le _ _
        _ = _ := by simp
    · calc |-b j + (h j + b j) * 0| ≤ |-b j| + |(h j + b j) * 0| := abs_add_le _ _
        _ ≤ _ := by simp
    · simp; positivity
  have hC2 : ∀ p : Fin (n+1) → ℝ, ‖(if reachEvent L (extendPath p) t j y then
              nvRightDeriv (μ j) (h j) (b j) (y - cumDemand (extendPath p) t j) else 0)‖
                ≤ |b j| + |h j + b j| := by
    intro p
    rw [Real.norm_eq_abs]
    split_ifs
    · unfold nvRightDeriv
      set c := ProbabilityTheory.cdf (μ j) (y - cumDemand (extendPath p) t j)
      have hc0 : 0 ≤ c := ProbabilityTheory.cdf_nonneg _ _
      have hc1 : c ≤ 1 := ProbabilityTheory.cdf_le_one _ _
      calc |-b j + (b j + h j) * c| ≤ |-b j| + |(b j + h j) * c| := abs_add_le _ _
        _ = |b j| + |h j + b j| * |c| := by rw [abs_neg, abs_mul, add_comm (b j)]
        _ ≤ |b j| + |h j + b j| * 1 := by
            gcongr; rw [abs_of_nonneg hc0]; exact hc1
        _ = _ := by ring
    · simp; positivity
  have hint1 : Integrable (fun p : Fin (n+1) → ℝ => pathTerm h b L (extendPath p) t j y)
      (Measure.pi fun k : Fin (n+1) => μ k) :=
    Integrable.of_bound (g69h2_meas_term h b L t j y).aestronglyMeasurable _
      (Filter.Eventually.of_forall hC1)
  have hint2 : Integrable (fun p : Fin (n+1) → ℝ => (if reachEvent L (extendPath p) t j y then
              nvRightDeriv (μ j) (h j) (b j) (y - cumDemand (extendPath p) t j) else 0))
      (Measure.pi fun k : Fin (n+1) => μ k) :=
    Integrable.of_bound (g69h2_meas_rhs (μ j) h b L t j y).aestronglyMeasurable _
      (Filter.Eventually.of_forall hC2)
  unfold pathLaw
  rw [g69h2_fubini (fun k : Fin (n+1) => μ k) jj _ hint1,
    g69h2_fubini (fun k : Fin (n+1) => μ k) jj _ hint2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨P0, hP0⟩ : ∃ P0 : ℕ → ℝ, ∀ x, extendPath (Fin.insertNth jj x v) =
      Function.update P0 j x := ⟨_, fun x => g69h2_extend_insert jj x v⟩
  have hjj : ((jj : ℕ)) = j := rfl
  simp only [hP0, hjj, g69h2_reach_update, g69h2_cum_update P0 j _ t j le_rfl]
  unfold pathTerm
  simp only [g69h2_reach_update, g69h2_cum_update P0 j _ t j le_rfl, Function.update_self]
  by_cases hA : reachEvent L P0 t j y
  · simp only [hA, if_true]
    rw [integral_const]
    simp only [probReal_univ, one_smul]
    have hind : ∀ x : ℝ, -b j + (h j + b j) * (if x ≤ y - cumDemand P0 t j then (1:ℝ) else 0) =
        -b j + Set.indicator (Set.Iic (y - cumDemand P0 t j)) (fun _ => h j + b j) x := by
      intro x; simp [Set.indicator, Set.mem_Iic]
    simp only [hind]
    rw [integral_add (integrable_const _) ((integrable_const _).indicator measurableSet_Iic),
      integral_const, integral_indicator measurableSet_Iic, integral_const]
    simp only [probReal_univ, one_smul, nvRightDeriv, ProbabilityTheory.cdf_eq_real]
    simp [Measure.real, smul_eq_mul]
    ring
  · simp [hA]
