-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:17.265534+00:00
-- url     : https://prove2.me/submissions/28971036-876c-42af-ba1f-a0c55f060cf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_act_iff_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.UnfoldShape
namespace _root_.GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (g h : GL ι k) (M : Submodule 𝒪[k] (ι → k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act (g * h) M = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act h M) := by
  ext v
  simp only [_root_.GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
