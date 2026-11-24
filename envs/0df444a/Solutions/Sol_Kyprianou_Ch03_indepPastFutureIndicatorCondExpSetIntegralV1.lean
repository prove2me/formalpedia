-- Prove2me | solution 1 for Kyprianou.Ch03.indepPastFutureIndicatorCondExpSetIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:58:41.375801+00:00
-- url     : https://prove2.me/submissions/24a3c5da-beae-43a9-84b9-d07a532f93e9

import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Theorems.Thm_Kyprianou_Ch03_indepRectangleIntegralFactorV1
import Theorems.Thm_Kyprianou_Ch03_pastFutureRectangleGeneratorV1
import Theorems.Thm_Kyprianou_Ch03_setIntegralEqualityPiSystemV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m g h : MeasurableSpace Omega)
    (hmg : m ≤ g) (hgh : g ≤ m ⊔ h) (hjoin : m ⊔ h ≤ mΩ)
    (hInd : @Indep Omega g h mΩ P)
    (A : Set Omega) (hA : MeasurableSet[g] A) :
    ∀ S : Set Omega, MeasurableSet[m ⊔ h] S →
      (∫ x in S, (P[A.indicator (fun _ => (1 : ℝ)) | m]) x ∂P) =
        ∫ x in S, A.indicator (fun _ => (1 : ℝ)) x ∂P := by
  classical
  letI : MeasurableSpace Omega := mΩ
  let f : Omega → ℝ := A.indicator (fun _ => 1)
  let q : Omega → ℝ := P[f | m]
  have hm : m ≤ mΩ := le_sup_left.trans hjoin
  have hg : g ≤ mΩ := hgh.trans hjoin
  have hh : h ≤ mΩ := le_sup_right.trans hjoin
  have hf : @Measurable Omega ℝ g _ f := measurable_const.indicator hA
  have hq : @Measurable Omega ℝ g _ q :=
    stronglyMeasurable_condExp.measurable.mono hmg le_rfl
  have hfi : Integrable f P := (integrable_const (1 : ℝ)).indicator (hg _ hA)
  have hmatch (B : Set Omega) (hB : MeasurableSet[m] B) :
      (∫ x in B, q x ∂P) = ∫ x in B, f x ∂P :=
    setIntegral_condExp hm hfi hB
  let R : Set (Set Omega) :=
    {S | ∃ B C : Set Omega, MeasurableSet[m] B ∧ MeasurableSet[h] C ∧ S = B ∩ C}
  have hR := Kyprianou.Ch03.pastFutureRectangleGeneratorV1 m h
  refine @Kyprianou.Ch03.setIntegralEqualityPiSystemV1 Omega mΩ P (m ⊔ h) hjoin R
    hR.1 hR.2 f q hfi integrable_condExp ?_ ?_
  · simpa only [Measure.restrict_univ] using hmatch Set.univ (show MeasurableSet[m] Set.univ from MeasurableSet.univ)
  · rintro S ⟨B, C, hB, hC, rfl⟩
    rw [Kyprianou.Ch03.indepRectangleIntegralFactorV1 P g h hg hh hInd q hq B C
      (hmg _ hB) hC, Kyprianou.Ch03.indepRectangleIntegralFactorV1 P g h hg hh hInd f hf B C
      (hmg _ hB) hC, hmatch B hB]
