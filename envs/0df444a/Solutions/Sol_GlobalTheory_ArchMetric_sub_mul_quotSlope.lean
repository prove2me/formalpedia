-- Prove2me | solution 1 for GlobalTheory.ArchMetric.sub_mul_quotSlope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:28.051237+00:00
-- url     : https://prove2.me/submissions/5fa9771a-f4a4-4429-9392-21acb2b1776f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_finrank_inf_restrictScalars_lt

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
theorem _root_.solution (hA : A.FG) {W : Submodule K V} (hW : ¬ A ≤ W.restrictScalars (𝓞 K)) :
    ((finrank (𝓞 K) A : ℝ) -
        finrank (𝓞 K) (A ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V)) *
      h.quotSlope A (A ⊓ W.restrictScalars (𝓞 K)) =
      h.degNorm A - h.degNorm (A ⊓ W.restrictScalars (𝓞 K)) :=
  mul_div_cancel₀ _ (sub_pos.2 (Nat.cast_lt.2 (finrank_inf_restrictScalars_lt hA hW))).ne'
end GlobalTheory.ArchMetric
