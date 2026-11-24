-- Prove2me | solution 1 for GlobalTheory.QNorm.IsQuad.exists_embedding_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:42:37.568384+00:00
-- url     : https://prove2.me/submissions/1b698f3a-def2-4d25-b0fc-08f4ec4071d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_coord_indep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
namespace IsQuad
theorem _root_.solution {F E L : Type} [Field F] [Field E] [Algebra F E] [Field L]
    {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (φ : F →+* L) (r : L)
    (hr : φ δ = r * r) :
    ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  choose A B hAB using h.span
  have key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ →
      φ (A x) + φ (B x) * r = φ a + φ b * r := by
    intro x a b hx
    have := h.coord_indep (A x - a) (B x - b) (by
      rw [map_sub, map_sub]; linear_combination hx - hAB x)
    rw [sub_eq_zero.1 this.1, sub_eq_zero.1 this.2]
  refine ⟨{ toFun := fun x => φ (A x) + φ (B x) * r
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · rw [key 1 1 0 (by simp)]; simp
  · intro x y
    rw [key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by
      simp only [map_add, map_mul, ← h.sq]
      linear_combination y * hAB x + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hAB y)]
    simp only [map_add, map_mul, hr]; ring
  · rw [key 0 0 0 (by simp)]; simp
  · intro x y
    rw [key (x + y) (A x + A y) (B x + B y) (by
      simp only [map_add]
      linear_combination hAB x + hAB y)]
    simp only [map_add]; ring
  · intro a
    change φ (A _) + φ (B _) * r = _
    rw [key _ a 0 (by simp)]; simp
  · change φ (A _) + φ (B _) * r = _
    rw [key _ 0 1 (by simp)]; simp
end IsQuad
end GlobalTheory.QNorm
