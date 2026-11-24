-- Prove2me | solution 1 for Kyprianou.Ch03.delayedOpenHitStrictSublevelsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:20:13.102124+00:00
-- url     : https://prove2.me/submissions/d3650097-a7b4-42d2-b7eb-5775719d75d1

import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitRationalWitnessV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
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
  -- a measurable null set outside of which paths are càdlàg
  have hae := hX.cadlag_ae
  rw [ae_iff] at hae
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hae
  have hgood : ∀ omega, omega ∉ N →
      ∀ t : NNReal, ContinuousWithinAt (fun u => X u omega) (Set.Ici t) t := by
    intro omega hom t
    by_contra hbad
    exact hom (hNsub (fun hc => hbad (hc t).1))
  -- null subsets belong to every `F s`
  have hnull : ∀ s : NNReal, ∀ A : Set Omega, A ⊆ N → MeasurableSet[F s] A := by
    intro s A hA
    rw [hNatural s]
    exact (le_sup_right : _ ≤ PerfCorrMSQ.natFiltr X s ⊔ _) A
      (MeasurableSpace.measurableSet_generateFrom ⟨N, hNm, hN0, hA⟩)
  -- `X q` is `F q`-measurable
  have hXm : ∀ u : NNReal, MeasurableSet[F u] {omega | X u omega ∈ B} := by
    intro u
    rw [hNatural u]
    refine (le_sup_left : PerfCorrMSQ.natFiltr X u ≤ _) _ ?_
    refine (le_iSup₂ (f := fun v (_ : v ≤ u) =>
      MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace ℝ)) u le_rfl) _ ?_
    exact ⟨B, hB.measurableSet, rfl⟩
  -- `{τ < s} ∈ F s`
  let U : Set Omega := ⋃ q : ℚ, ⋃ (_ : a ≤ Real.toNNReal q ∧ Real.toNNReal q < s),
    {w | X (Real.toNNReal q) w ∈ B}
  have hU : MeasurableSet[F s] U := by
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
    exact F.mono hq.2.le _ (hXm _)
  let A := {w | sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | a ≤ t ∧ X t w ∈ B}) < (s : WithTop NNReal)}
  have he : A = (U \ N) ∪ (A ∩ N) := by
    ext w
    by_cases hw : w ∈ N
    · simp [hw]
    · simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff, hw, not_false_eq_true,
        and_true, and_false, or_false, A, Set.mem_setOf_eq, U, Set.mem_iUnion, exists_prop]
      rw [Kyprianou.Ch03.delayedOpenHitRationalWitnessV1 X B hB a w (hgood w hw) s]
      aesop
  change MeasurableSet[F s] A
  rw [he]
  exact (hU.diff (hnull s N subset_rfl)).union (hnull s _ Set.inter_subset_right)
