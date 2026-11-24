-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.conj_mkNel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:38.994828+00:00
-- url     : https://prove2.me/submissions/0136c9ef-229d-4d5d-852b-60da007c0d25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_matrixExtendByZero_mul
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_mkNel
import Theorems.Thm_GlobalTheory_RootEx_VolN_rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ =
      (mkNel p ((rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).mulVec e) : N k n c p) := by
  have hm : embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ ∈ N k n c p := by
    simpa using conj_mem (mkNel p e).2 x⁻¹
  have := mkNel_co p ⟨_, hm⟩
  refine (congrArg Subtype.val this).symm.trans ?_
  congr 2
  funext rs
  rw [← Matrix.mulVec_mulVec, ← matrixExtendByZero_mul, ← rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks, map_inv]
  have hne : rs.1.1 ≠ rs.1.2 := fun h => by have := rs.2; rw [h] at this; exact lt_irrefl _ this
  simp only [co, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv,
    Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
end GlobalTheory.RootEx.VolN
