-- Prove2me | solution 1 for GlobalTheory.ArchMetric.deg_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:37.998261+00:00
-- url     : https://prove2.me/submissions/cc16a118-3f56-4175-b611-e4882a28c8f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A B : Submodule (𝓞 K) V}
namespace GlobalTheory.ArchMetric
theorem _root_.solution (A : Submodule (𝓞 K) V) : h.deg_sq A = 2 * h.degNorm A := by
  rw [deg_sq, lcv_sq]
  ring
end GlobalTheory.ArchMetric
