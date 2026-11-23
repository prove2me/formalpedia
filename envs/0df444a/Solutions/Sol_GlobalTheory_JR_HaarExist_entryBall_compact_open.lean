-- Prove2me | solution 1 for GlobalTheory.JR.HaarExist.entryBall_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:46.703553+00:00
-- url     : https://prove2.me/submissions/6378d178-964d-4ef8-9c50-826fff7b051c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HaarExist
variable (r : ℕ)
namespace GlobalTheory.JR.HaarExist
theorem _root_.solution (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ∧
      IsOpen {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have e : {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} =
      Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : K) 1 := by
    ext A
    exact ⟨fun h i _ j _ => mem_closedBall_zero_iff.2 (h i j),
      fun h i j => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))⟩
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero⟩
end GlobalTheory.JR.HaarExist
