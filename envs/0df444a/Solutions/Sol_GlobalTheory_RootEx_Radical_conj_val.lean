-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.conj_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:08.103812+00:00
-- url     : https://prove2.me/submissions/f24430d2-e3da-4ef8-83c7-61eb73a801bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    (embX c x * g * (embX c x)⁻¹).val =
      fromBlocks (x.val * g.val.toBlocks₁₁ * (x⁻¹).val) (x.val * g.val.toBlocks₁₂)
        (g.val.toBlocks₂₁ * (x⁻¹).val) g.val.toBlocks₂₂ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, embX_val, embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g.val]
  simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one]
end GlobalTheory.RootEx.Radical
