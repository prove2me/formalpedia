-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.unipEquiv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:04:18.07625+00:00
-- url     : https://prove2.me/submissions/b3be833e-4db3-4ffe-beef-02f487389c8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_ent_mat_mul
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_mul_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable (e : (Σ a, m a) ≃ n)
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (g : Levi R m) (x : Idx e → R) :
    unipEquiv e (conj e g ((unipEquiv e).symm x)) = (cmat e g).mulVec x := by
  rw [cmat, ← mulVec_mulVec, ← ent_mat_mul, ← mul_mat e (leviEmb_mem_parab R e g), map_inv,
    ← ent_one_add e (_ * _ * _)]
  show ent e ((leviEmb R e g : Matrix n n R) * (1 + mat e x) * ((leviEmb R e g)⁻¹ : GL n R).val) = _
  rw [mul_add, mul_one, add_mul, Units.mul_inv]
end GlobalTheory.SmGL.UnipHaar
