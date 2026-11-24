-- Prove2me | solution 1 for GlobalTheory.DetFactor.map_diagGL_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:41:00.63826+00:00
-- url     : https://prove2.me/submissions/46579ea6-f8ca-4e7a-83b8-3df4e6e533d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
import Theorems.Thm_GlobalTheory_DetFactor_diagGL_val
import Theorems.Thm_GlobalTheory_DetFactor_toGL_val
import Theorems.Thm_GlobalTheory_DetFactor_det_perm_ne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DetFactor.toGL_val

set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory.DetFactor
theorem _root_.solution {n : ℕ} (c : GL (Fin n) k →* ℂˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → kˣ) :
    c (diagGL n (d ∘ σ)) = c (diagGL n d) := by
  set P := toGL _ (det_perm_ne (k := k) σ)
  have h1 : P * diagGL n d = diagGL n (d ∘ σ) * P := by
    apply Units.ext
    simp only [Units.val_mul, toGL_val, P, diagGL_val]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp [diagonal_apply, Equiv.eq_symm_apply]
  have e := congrArg c h1
  rw [map_mul, map_mul, mul_comm (c P)] at e
  exact (mul_right_cancel e).symm
end GlobalTheory.DetFactor
