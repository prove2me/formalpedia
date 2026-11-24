-- Prove2me | solution 1 for GlobalTheory.QNorm.isQuad_galois_and_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:44.422158+00:00
-- url     : https://prove2.me/submissions/cbf4dc16-f6d7-43d8-ab9a-0309b7c5d6fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionIsGaloisAndEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
private theorem quad_unique {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) {a b c d : F}
    (e : algebraMap F E a + algebraMap F E b * θ = algebraMap F E c + algebraMap F E d * θ) :
    a = c ∧ b = d := by
  have hbd : b = d := by
    by_contra hne
    have h0 : b - d ≠ 0 := sub_ne_zero.mpr hne
    have h0' : algebraMap F E (b - d) ≠ 0 := by
      exact (map_ne_zero _).2 h0
    have hθ : θ = algebraMap F E ((c - a) / (b - d)) := by
      rw [map_div₀, eq_div_iff h0', map_sub, map_sub]
      linear_combination e
    apply h.nonsq
    refine ⟨(c - a) / (b - d), (algebraMap F E).injective ?_⟩
    rw [map_mul, ← hθ, ← h.sq, sq]
  refine ⟨(algebraMap F E).injective ?_, hbd⟩
  rw [hbd] at e
  exact add_right_cancel e
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → IsGalois F E ∧ (∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ) ∧ ∀ (L : Type) [Field L] (φ : F →+* L) (r : L), r ^ 2 = φ δ → ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  intro F E _ _ _ _ δ θ σ h
  refine ⟨?_, ?_, ?_⟩
  · haveI : FiniteDimensional F E := by
      classical
      refine ⟨⟨{1, θ}, ?_⟩⟩
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Finset.coe_pair, Submodule.mem_span_pair]
      exact ⟨a, b, by simp [Algebra.smul_def]⟩
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    have h1 : σ (algebraMap F E a + algebraMap F E b * θ)
        = algebraMap F E a + algebraMap F E b * θ :=
      (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.mem_top _)
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj] at h1
    have h2 : algebraMap F E a + algebraMap F E (-b) * θ
        = algebraMap F E a + algebraMap F E b * θ := by
      rw [← h1, map_neg]; ring
    have h3 := (quad_unique h h2).2
    have hb : b = 0 := by linear_combination (-1/2 : F) * h3
    rw [hb, map_zero, zero_mul, add_zero]
    exact IntermediateField.algebraMap_mem _ a
  · intro τ
    have h1 : τ θ ^ 2 = θ ^ 2 := by
      rw [← map_pow, h.sq, AlgEquiv.commutes]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · left
      ext x
      obtain ⟨a, b, rfl⟩ := h.span x
      simp [e]
    · right
      ext x
      obtain ⟨a, b, rfl⟩ := h.span x
      simp [e, h.conj]
  · intro L _ φ r hr
    choose A B hAB using h.span
    have key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ →
        A x = a ∧ B x = b := fun x a b e => quad_unique h ((hAB x).symm.trans e)
    have hal : ∀ a : F, φ (A (algebraMap F E a)) + φ (B (algebraMap F E a)) * r = φ a := by
      intro a
      obtain ⟨h1, h2⟩ := key (algebraMap F E a) a 0 (by simp)
      simp [h1, h2]
    refine ⟨{ toFun := fun x => φ (A x) + φ (B x) * r
              map_one' := by simpa using hal 1
              map_zero' := by simpa using hal 0
              map_add' := ?_
              map_mul' := ?_ }, hal, ?_⟩
    · intro x y
      obtain ⟨h1, h2⟩ := key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by
        have hx := hAB x
        have hy := hAB y
        have hs := h.sq
        simp only [map_add, map_mul]
        linear_combination y * hx + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hy
          + algebraMap F E (B x) * algebraMap F E (B y) * hs)
      simp only [h1, h2, map_add, map_mul]
      linear_combination (-(φ (B x) * φ (B y))) * hr
    · intro x y
      obtain ⟨h1, h2⟩ := key (x + y) (A x + A y) (B x + B y) (by
        have hx := hAB x
        have hy := hAB y
        simp only [map_add]
        linear_combination hx + hy)
      simp only [h1, h2, map_add]
      ring
    · obtain ⟨h1, h2⟩ := key θ 0 1 (by simp)
      simp [h1, h2]
end GlobalTheory.QNorm
