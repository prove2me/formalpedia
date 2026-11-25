-- Prove2me | solution 1 for GlobalTheory.SymSupport.InR.conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:49.971052+00:00
-- url     : https://prove2.me/submissions/37484426-506d-49d3-8eb7-615e04c39d2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Theorems.Thm_GlobalTheory_SymSupport_typeFrame_val
import Theorems.Thm_GlobalTheory_SymSupport_typeFrame_inv_val

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
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymSupport
namespace InR
theorem _root_.solution {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) {g : GL (n ⊕ Fin c) k} (h : InR g.val) :
    InR ((typeFrame ϖ ord).bas * g * (typeFrame ϖ ord).bas⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, typeFrame_val, typeFrame_inv_val]
  refine ⟨fun l s => by simp [h.1], fun r i hl => ?_⟩
  rw [mul_diagonal, diagonal_mul, h.2 r i hl, Matrix.one_apply]
  split_ifs with e
  · subst e; simp
  · simp
end InR
end GlobalTheory.SymSupport
