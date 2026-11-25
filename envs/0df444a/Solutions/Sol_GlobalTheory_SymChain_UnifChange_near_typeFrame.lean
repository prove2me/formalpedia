-- Prove2me | solution 1 for GlobalTheory.SymChain.UnifChange.near_typeFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:52.882971+00:00
-- url     : https://prove2.me/submissions/d9eaea66-f604-471b-bcf0-fdd0cfa709e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
import Theorems.Thm_GlobalTheory_SymChain_UnifChange_val_pow_sub_one
import Theorems.Thm_GlobalTheory_SymChain_UnifChange_val_div_sub_one
import Theorems.Thm_GlobalTheory_StepData_mem_KOne
import Theorems.Thm_GlobalTheory_SymSupport_typeFrame_inv_val
import Theorems.Thm_GlobalTheory_SymSupport_typeFrame_val


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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) (o : ι ≃ n ⊕ Fin c) :
    Near (typeFrame ϖ o) (typeFrame ϖ' o) := by
  refine ⟨rfl, mem_KOne.2 fun i j => ?_⟩
  rw [Units.val_mul, GlobalTheory.SymSupport.typeFrame_inv_val, GlobalTheory.SymSupport.typeFrame_val, diagonal_mul_diagonal,
    ← diagonal_one, diagonal_sub, diagonal_apply]
  split_ifs
  · rcases i with i | i
    · simp
    · have := val_pow_sub_one (val_div_sub_one h) (i.val + 1)
      rwa [mul_pow, inv_pow] at this
  · simp
end GlobalTheory.SymChain.UnifChange
