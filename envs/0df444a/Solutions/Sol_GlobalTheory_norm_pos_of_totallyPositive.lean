-- Prove2me | solution 1 for GlobalTheory.norm_pos_of_totallyPositive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:38.579802+00:00
-- url     : https://prove2.me/submissions/13de7aaa-7ff6-46fc-b3e1-7f0fbcf9859d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormTotallyPositiveOfTotallyPositiveNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E E' : Type) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Algebra E E'] (a : E') (ha : a ≠ 0) (hpos : ∀ φ : E' →+* ℝ, 0 < φ a)
    (φ : E →+* ℝ) : 0 < φ (Algebra.norm E a) := by
  letI : Algebra E ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  have hmap : ∀ x, algebraMap E ℂ x = ((φ x : ℝ) : ℂ) := fun x => rfl
  have key := Algebra.norm_eq_prod_embeddings E ℂ a
  let g : (E' →ₐ[E] ℂ) → (E' →ₐ[E] ℂ) := fun σ =>
    { (starRingEnd ℂ).comp σ.toRingHom with
      commutes' := fun x => by
        show (starRingEnd ℂ) (σ (algebraMap E E' x)) = algebraMap E ℂ x
        rw [σ.commutes, hmap, Complex.conj_ofReal] }
  have hg : ∀ σ x, g σ x = (starRingEnd ℂ) (σ x) := fun σ x => rfl
  have hne : ∀ σ : E' →ₐ[E] ℂ, σ a ≠ 0 := fun σ => (map_ne_zero σ).2 ha
  have hnorm : ∀ σ : E' →ₐ[E] ℂ, ((‖σ a‖ : ℝ) : ℂ) ≠ 0 := fun σ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hne σ))
  have h1 : ∏ σ : E' →ₐ[E] ℂ, σ a / ((‖σ a‖ : ℝ) : ℂ) = 1 := by
    refine Finset.prod_involution (fun σ _ => g σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
    · intro σ _
      rw [hg, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, div_eq_one_iff_eq
        (mul_ne_zero (hnorm σ) (hnorm σ)), Complex.normSq_eq_norm_sq]
      push_cast; ring
    · intro σ _ hf hgs
      apply hf
      have hreal : ComplexEmbedding.IsReal σ.toRingHom := by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact congrArg (fun τ : E' →ₐ[E] ℂ => τ x) hgs
      have hc : σ a = ((hreal.embedding a : ℝ) : ℂ) := (hreal.coe_embedding_apply a).symm
      have hp := hpos hreal.embedding
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact div_self (by exact_mod_cast hp.ne')
    · intro σ _
      ext x
      simp [hg]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun σ _ => hnorm σ)]
    at h1
  rw [h1, hmap] at key
  have hr : φ (Algebra.norm E a) = ∏ σ : E' →ₐ[E] ℂ, ‖σ a‖ := by
    apply Complex.ofReal_injective
    rw [key]; push_cast; rfl
  rw [hr]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.2 (hne σ)
end GlobalTheory
