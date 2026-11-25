-- Prove2me | solution 1 for GlobalTheory.SymChain.UnifChange.psi_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:33.382723+00:00
-- url     : https://prove2.me/submissions/c91bcd30-669e-4ceb-ba2b-56f54eb4ef59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
import Theorems.Thm_GlobalTheory_SymChain_UnifChange_inv_sub_inv_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one


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
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ)
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {x : k} (hx : x ∈ 𝒪[k]) :
    ψ ((ϖ'⁻¹ : kˣ) * x) = ψ ((ϖ⁻¹ : kˣ) * x) := by
  have hi : (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x ∈ 𝒪[k] := mul_mem (inv_sub_inv_mem hϖ h) hx
  have e : ((ϖ'⁻¹ : kˣ) : k) * x = (ϖ⁻¹ : kˣ) * x + (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x := by ring
  rw [e, AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi), mul_one]
end GlobalTheory.SymChain.UnifChange
