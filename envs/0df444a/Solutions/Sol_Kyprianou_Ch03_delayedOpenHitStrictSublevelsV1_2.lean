-- Prove2me | solution 2 for Kyprianou.Ch03.delayedOpenHitStrictSublevelsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:28:02.235819+00:00
-- url     : https://prove2.me/submissions/04ab3eff-164f-45b0-92c2-fb1c39ae98b2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitRationalWitnessV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (a : NNReal) (B : Set ℝ) (hB : IsOpen B) (s : NNReal) :
    MeasurableSet[F s] {w | sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) < (s : WithTop NNReal)} := by
  let A : Set Omega := {w | sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | a ≤ t ∧ X t w ∈ B}) < (s : WithTop NNReal)}
  let U : Set Omega := ⋃ q : ℚ, ⋃ (_ : a ≤ Real.toNNReal q ∧ Real.toNNReal q < s),
    {w | X (Real.toNNReal q) w ∈ B}
  have hU : MeasurableSet[F s] U := by
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
    apply F.mono hq.2.le
    rw [hNatural (Real.toNNReal q)]
    apply (le_sup_left : PerfCorrMSQ.natFiltr X (Real.toNNReal q) ≤ _)
    exact (le_iSup₂ (f := fun v (_ : v ≤ Real.toNNReal q) =>
      MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace ℝ))
        (Real.toNNReal q) le_rfl) _ ⟨B, hB.measurableSet, rfl⟩
  have he : ∀ᵐ w ∂P, w ∈ A ↔ w ∈ U := by
    filter_upwards [hX.cadlag_ae] with w hw
    simp only [A, U, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [Kyprianou.Ch03.delayedOpenHitRationalWitnessV1 X B hB a w (fun t => (hw t).1) s]
    tauto
  rw [ae_iff] at he
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null he
  have hnull (C : Set Omega) (hC : C ⊆ N) : MeasurableSet[F s] C := by
    rw [hNatural s]
    exact (le_sup_right : _ ≤ PerfCorrMSQ.natFiltr X s ⊔ _) C
      (MeasurableSpace.measurableSet_generateFrom ⟨N, hNm, hN0, hC⟩)
  have hA : A = (U \ N) ∪ (A ∩ N) := by
    ext w
    by_cases hw : w ∈ N
    · simp [hw]
    · have hh : w ∈ A ↔ w ∈ U := by
        by_contra hn
        exact hw (hsub hn)
      simp [hw, hh]
  change MeasurableSet[F s] A
  rw [hA]
  exact (hU.diff (hnull N subset_rfl)).union (hnull _ Set.inter_subset_right)
