-- Prove2me | solution 1 for Kyprianou.Ch04.openHitStoppingTimeOfAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:12:15.860587+00:00
-- url     : https://prove2.me/submissions/a97ca0c0-c2e8-4b2a-8547-20223fe9fdf5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_openHitLtRationalWitness
import Theorems.Thm_Kyprianou_Ch04_strictSublevelStoppingTime
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- Open-set hitting of an adapted a.s. right-continuous process is a stopping time
in a right-continuous filtration containing all subsets of ambient null sets. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (Y : NNReal → Omega → ℝ) (hY : Adapted F Y)
    (hPath : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => Y u w) (Set.Ici t) t)
    (B : Set ℝ) (hB : IsOpen B) :
    IsStoppingTime F (fun w => sInf {u : WithTop NNReal |
      ∃ r : NNReal, u = ↑r ∧ Y r w ∈ B}) := by
  rw [ae_iff] at hPath
  obtain ⟨N,hsub,hm,hzero⟩ := exists_measurable_superset_of_null hPath
  apply strictSublevelStoppingTime F hRC
  intro s
  let A : Set Omega := {w | sInf {u : WithTop NNReal |
    ∃ r : NNReal, u = ↑r ∧ Y r w ∈ B} < (s : WithTop NNReal)}
  let U : Set Omega := ⋃ q : ℚ, ⋃ (_ : 0 < q ∧ (q : ℝ) < s),
    {w | Y (Real.toNNReal q) w ∈ B}
  have hU : MeasurableSet[F s] U := by
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
    have hle : Real.toNNReal q ≤ s := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hq.2.le
    exact F.mono hle _ (hY _ hB.measurableSet)
  have he (w : Omega) (hw : w ∉ N) : w ∈ A ↔ w ∈ U := by
    have hgood : ∀ t : NNReal, ContinuousWithinAt (fun u => Y u w) (Set.Ici t) t :=
      not_not.mp (fun hbad => hw (hsub hbad))
    simp only [A,U,Set.mem_setOf_eq,Set.mem_iUnion,exists_prop]
    rw [openHitLtRationalWitness (fun u => Y u w) B hB hgood s]
    tauto
  change MeasurableSet[F s] A
  have hA : A = (U \ N) ∪ (A ∩ N) := by
    ext w
    by_cases hw : w ∈ N
    · simp [hw]
    · simp [hw,he w hw]
  rw [hA]
  exact (hU.diff (hNull s N N hm hzero subset_rfl)).union
    (hNull s N (A ∩ N) hm hzero Set.inter_subset_right)
