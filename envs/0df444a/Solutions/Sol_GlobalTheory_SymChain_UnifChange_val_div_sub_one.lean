-- Prove2me | solution 1 for GlobalTheory.SymChain.UnifChange.val_div_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:39:32.178696+00:00
-- url     : https://prove2.me/submissions/d35ec77d-f45f-4041-964c-ae0953c8e03b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.SymChain.UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable {ϖ ϖ' : kˣ}
namespace GlobalTheory.SymChain.UnifChange
theorem _root_.solution (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k ((ϖ : k)⁻¹ * ϖ' - 1) < 1 := by
  have e : (ϖ : k)⁻¹ * ϖ' - 1 = (ϖ : k)⁻¹ * ((ϖ' : k) - ϖ) := by field_simp
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, map_mul, map_inv₀, inv_mul_lt_one₀ h0]
end GlobalTheory.SymChain.UnifChange
