-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.box_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:10.285834+00:00
-- url     : https://prove2.me/submissions/006a1339-028b-4bdd-bf08-c0dabc2ea1a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Theorems.Thm_GlobalTheory_JR_DualLattice_mem_box

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
theorem _root_.solution [IsUltrametricDist F] [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) :
    (box e r hr : Set V) = coordHomeo e ⁻¹' Metric.closedBall 0 r := by
  ext x
  rw [SetLike.mem_coe, mem_box, Set.mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
  rfl
end GlobalTheory.JR.DualLattice
