-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonDistinctActiveTimesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:55:50.05163+00:00
-- url     : https://prove2.me/submissions/d8b14174-5ae1-4fb9-b1bf-bc2a3c0284e8

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonActivePieceNonzeroV1
import Theorems.Thm_AvramDividend_Classical_time_marginal_atomless_scaled_restrict_volume_prod
import Theorems.Thm_AvramDividend_Classical_ae_distinct_of_joint_product_atomless
import Theorems.Thm_AvramDividend_Classical_ae_injective_on_active_indices_of_pairwise_ae
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q) :
    ∀ᵐ w ∂Q, ∀ i j : ℕ × ℕ,
      i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j := by
  let m := (volume : Measure ℝ).prod Pi
  let U (i : ℕ × ℕ) (w : Lambda) := (Z i.1 i.2 w).1
  have hm (i : ℕ × ℕ) : Measurable (U i) := measurable_fst.comp (hd.measurable_point _ _)
  have hpair (i j : ℕ × ℕ) (hij : i ≠ j) :
      ∀ᵐ w ∂Q, i.2 < K i.1 w → j.2 < K j.1 w → U i w ≠ U j w := by
    by_cases hj : m (prmPiece m j.1) = 0
    · filter_upwards [positivePoissonActivePieceNonzeroV1 Q Pi K Z hd] with w hw
      exact fun _ h => (hw j.1 j.2 h hj).elim
    · have hi : IndepFun (Z i.1 i.2) (Z j.1 j.2) Q := by
        exact hd.indep.indepFun (show (Sum.inr i : ℕ ⊕ ℕ × ℕ) ≠ Sum.inr j from
          fun h => hij (Sum.inr.inj h))
      have hu : IndepFun (U i) (U j) Q := hi.comp measurable_fst measurable_fst
      have hjlaw : Q.map (U j) = (prmPieceLaw m j.1).map Prod.fst := by
        change Q.map (Prod.fst ∘ Z j.1 j.2) = _
        rw [← Measure.map_map measurable_fst (hd.measurable_point _ _),
          (hd.law_point j.1 j.2).map_eq]
      have hatom : NullSingletonClass (Q.map (U j)) := by
        rw [hjlaw]
        unfold prmPieceLaw
        rw [if_neg hj]
        exact AvramDividend.Classical.time_marginal_atomless_scaled_restrict_volume_prod Pi
          (prmPiece m j.1) (m (prmPiece m j.1))⁻¹
      letI := hatom
      have hprod := hu.map_prod_eq_prod_map_map (hm i).aemeasurable (hm j).aemeasurable
      filter_upwards [AvramDividend.Classical.ae_distinct_of_joint_product_atomless Q
        (U i) (U j) ((hm i).prodMk (hm j)) (Q.map (U i)) (Q.map (U j)) hprod] with w hw
      exact fun _ _ => hw
  exact AvramDividend.Classical.ae_injective_on_active_indices_of_pairwise_ae Q
    (fun i w => i.2 < K i.1 w) U hpair
