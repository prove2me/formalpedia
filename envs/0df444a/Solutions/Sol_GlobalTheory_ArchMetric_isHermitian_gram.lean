-- Prove2me | solution 1 for GlobalTheory.ArchMetric.isHermitian_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:48.168419+00:00
-- url     : https://prove2.me/submissions/4c532c9c-a019-4c38-81b9-3646b530840b

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
variable {K : Type*} [Field K] {V V' V'' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
variable (h : ArchMetric K V)
namespace GlobalTheory.ArchMetric
theorem _root_.solution (σ : K →+* ℂ) {ι : Type*} (e : ι → V) : (h.gram σ e).IsHermitian := by
  ext i j
  simp
end GlobalTheory.ArchMetric
