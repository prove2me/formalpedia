-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:00.998359+00:00
-- url     : https://prove2.me/submissions/73f1d831-71b7-4806-8a98-6ccd1a3c891e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_dotProduct_congr_mulVec
import Theorems.Thm_GlobalTheory_HermWitt_isometry_iff_congr_eq
import Theorems.Thm_GlobalTheory_HermWitt_eq_zero_of_forall_dotProduct_eq_zero
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_comp_eq_of_nondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.HermWitt
theorem _root_.solution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a)
    {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix n m E}
    (hX : (Xᵀ * G * X.map c).det ≠ 0) (hXY : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : GL n E, (γ : Matrix n n E)ᵀ * G * (γ : Matrix n n E).map c = G ∧
      (γ : Matrix n n E) * X = Y := by
  obtain ⟨γ, hγ, e⟩ := exists_gl_isometry_comp_eq_of_nondegenerate h2 hc hG (g := X.mulVecLin)
    (f := Y.mulVecLin) (fun a b => by
      simp only [Matrix.mulVecLin_apply, ← dotProduct_congr_mulVec, hXY])
    (fun a ha => eq_zero_of_forall_dotProduct_eq_zero (c := c) hX fun b => by
      rw [dotProduct_congr_mulVec]
      exact ha b)
  refine ⟨γ, (isometry_iff_congr_eq c G _).1 hγ, Matrix.ext_of_mulVec_single fun a => ?_⟩
  rw [← Matrix.mulVec_mulVec]
  exact e _
end GlobalTheory.HermWitt
