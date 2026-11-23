-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.stdChar_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:19.191861+00:00
-- url     : https://prove2.me/submissions/bff51213-04c3-465d-b5dd-96dcbc3c4148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices

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
namespace GlobalTheory.JR.DualLattice
theorem _root_.solution {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.1 (y - x) (by simpa [dist_eq_norm] using hy), mul_one]
end GlobalTheory.JR.DualLattice
