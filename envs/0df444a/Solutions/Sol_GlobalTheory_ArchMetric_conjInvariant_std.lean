-- Prove2me | solution 1 for GlobalTheory.ArchMetric.conjInvariant_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:23.015535+00:00
-- url     : https://prove2.me/submissions/7a564a7f-b5f7-4a4f-8c14-bbf23ab2730f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_conjInvariant_diag

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
theorem _root_.solution (ι : Type*) [Fintype ι] : (std K ι).ConjInvariant :=
  conjInvariant_diag _ fun _ => rfl
end GlobalTheory.ArchMetric
