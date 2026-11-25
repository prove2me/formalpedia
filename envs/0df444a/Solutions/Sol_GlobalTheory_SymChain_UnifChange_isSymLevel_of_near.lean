-- Prove2me | solution 1 for GlobalTheory.SymChain.UnifChange.isSymLevel_of_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:15.917542+00:00
-- url     : https://prove2.me/submissions/e8256484-53ec-42d5-92c2-61a1a6635bac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
import Theorems.Thm_GlobalTheory_SymChain_UnifChange_psi_inv_mul
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO


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
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {ρ κ l : ℕ} {P : TypeDatum k (Fin κ ⊕ Fin l)}
    (hP : IsSymLevel ψ ϖ ρ P) : IsSymLevel ψ ϖ' ρ P := by
  refine ⟨hP.1, fun g => ?_⟩
  have hg := intM_of_mem_KO (P.le_KO g.2)
  rw [hP.2 g, psi_inv_mul hψ hϖ h, psi_inv_mul hψ hϖ h]
  · refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]
  · unfold simpleSum
    refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]
end GlobalTheory.SymChain.UnifChange
