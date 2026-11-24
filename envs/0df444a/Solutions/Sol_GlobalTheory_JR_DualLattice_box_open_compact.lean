-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.box_open_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:24.408674+00:00
-- url     : https://prove2.me/submissions/fdd541bf-6b1a-45fa-a1ce-c921b26f9513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Theorems.Thm_GlobalTheory_JR_DualLattice_box_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualLattice
variable {F : Type} [NontriviallyNormedField F]
variable {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.JR.DualLattice
theorem _root_.solution [IsUltrametricDist F] [LocallyCompactSpace F] [TopologicalSpace V]
    [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 < r) :
    IsOpen (box e r hr.le : Set V) ∧ IsCompact (box e r hr.le : Set V) := by
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  rw [box_eq]
  exact ⟨(IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (coordHomeo e).continuous,
    (coordHomeo e).isCompact_preimage.2 (isCompact_closedBall _ _)⟩
end GlobalTheory.JR.DualLattice
