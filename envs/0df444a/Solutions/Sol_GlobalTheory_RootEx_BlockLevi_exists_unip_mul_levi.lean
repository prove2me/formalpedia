-- Prove2me | solution 1 for GlobalTheory.RootEx.BlockLevi.exists_unip_mul_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:05.115173+00:00
-- url     : https://prove2.me/submissions/a753f2e0-98ed-4ea9-9e9b-6747ec648a4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_mul_diagPart_apply
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_diagPart_mul_diagPart
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_blockTriangular_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.BlockLevi
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.BlockLevi
theorem _root_.solution : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (b : GL (n ⊕ Fin c) k), b.val.BlockTriangular (lev p) → ∃ u ∈ N k n c p, ∃ m : GL (n ⊕ Fin c) k, (∀ r s, lev p r ≠ lev p s → m.val r s = 0) ∧ (∀ r s, lev p r = lev p s → m.val r s = b.val r s) ∧ b = u * m := by
  intro k _ n _ _ c p b hb
  have hi := blockTriangular_inv (lev p) b hb
  let m : GL (n ⊕ Fin c) k := ⟨diagPart (lev p) b.val, diagPart (lev p) (b⁻¹).val,
    diagPart_mul_diagPart _ hb hi b.mul_inv, diagPart_mul_diagPart _ hi hb b.inv_mul⟩
  refine ⟨b * m⁻¹, Subgroup.subset_closure ?_, m, ?_, ?_, by simp⟩
  · intro r s h
    have : (b * m⁻¹).val = b.val * diagPart (lev p) (b⁻¹).val := rfl
    rw [this, mul_diagPart_apply _ hb hi h, b.mul_inv]
  · intro r s h
    simp [m, diagPart, h]
  · intro r s h
    simp [m, diagPart, h]
end GlobalTheory.RootEx.BlockLevi
