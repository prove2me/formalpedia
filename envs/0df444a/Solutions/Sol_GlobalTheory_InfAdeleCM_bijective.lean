-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:25.964023+00:00
-- url     : https://prove2.me/submissions/6579ed32-1a86-4e1b-aaa8-fcd69b884a36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Theorems.Thm_GlobalTheory_InfAdeleCM_ext_eq_ofReal
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_delta
import Theorems.Thm_GlobalTheory_InfAdeleCM_eq_or_conj
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_decomp
import Theorems.Thm_GlobalTheory_InfAdeleCM_mk_eq_iff
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution [IsTotallyReal F] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    (θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (hθ : ∀ τ a x, θ τ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  obtain ⟨δ, h0, hcδ, hs⟩ := exists_delta c h2 hc hτ
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hτ τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact h0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ w : InfinitePlace F, w.Completion →+* ℝ := fun w =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
  have hr : ∀ w, Function.Bijective (r w) := fun w =>
    InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal _
  have hval : ∀ (τ : E →+* ℂ) (a b : InfiniteAdeleRing F), θ τ (a ⊗ₜ 1 + b ⊗ₜ δ) =
      ⟨r _ (a (InfinitePlace.mk (τ.comp (algebraMap F E)))),
        r _ (b (InfinitePlace.mk (τ.comp (algebraMap F E)))) * (τ δ).im⟩ := by
    intro τ a b
    rw [map_add, hθ, hθ, ext_eq_ofReal, ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, r]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, r]
  choose t ht htw using exists_over (F := F) Ψ hΨ
  constructor
  · intro z z' hz
    obtain ⟨a, b, rfl⟩ := exists_decomp hs z
    obtain ⟨a', b', rfl⟩ := exists_decomp hs z'
    have key : ∀ w, a w = a' w ∧ b w = b' w := by
      intro w
      have := congrFun hz ⟨t w, ht w⟩
      simp only [hval, Complex.mk.injEq] at this
      rw [htw w] at this
      exact ⟨(hr w).1 this.1, (hr w).1 (mul_right_cancel₀ (him _) this.2)⟩
    have ha : a = a' := funext fun w => (key w).1
    have hb : b = b' := funext fun w => (key w).2
    rw [ha, hb]
  · intro y
    choose a ha using fun w => (hr w).2 (y ⟨t w, ht w⟩).re
    choose b hb using fun w => (hr w).2 ((y ⟨t w, ht w⟩).im / (t w δ).im)
    refine ⟨(show InfiniteAdeleRing F from a) ⊗ₜ[F] (1 : E) + (show InfiniteAdeleRing F from b) ⊗ₜ[F] δ, ?_⟩
    funext τ
    obtain ⟨τ, hτΨ⟩ := τ
    have e : t (InfinitePlace.mk (τ.comp (algebraMap F E))) = τ := by
      rcases eq_or_conj c hτ h0 hcδ hs _ _ (mk_eq_iff (htw (InfinitePlace.mk (τ.comp (algebraMap F E))))) with e | e
      · exact e
      · exact absurd (e ▸ ht _) ((hΨ τ).1 hτΨ)
    have := hval τ a b
    simp only [ha, hb, e] at this
    refine this.trans ?_
    apply Complex.ext
    · rfl
    · exact div_mul_cancel₀ _ (him τ)
end GlobalTheory.InfAdeleCM
