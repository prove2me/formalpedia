-- Prove2me | solution 1 for GlobalTheory.SymChain.UnifChange.inv_sub_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:29.175887+00:00
-- url     : https://prove2.me/submissions/887b8998-d950-4f5a-95c7-81081e5fd2df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
import Theorems.Thm_GlobalTheory_SymChain_UnifChange_val_div_sub_one
import Theorems.Thm_GlobalTheory_SymChain_UnifChange_val_eq

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
theorem _root_.solution (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := by
  have h1 := (hϖ _).1 (val_div_sub_one h)
  have e : ((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k) = -((ϖ' : k)⁻¹ * ((ϖ : k)⁻¹ * ϖ' - 1)) := by
    simp only [Units.val_inv_eq_inv_val]; field_simp; ring
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, Valuation.map_neg, map_mul, map_inv₀, val_eq h, inv_mul_le_one₀ h0]
end GlobalTheory.SymChain.UnifChange
