-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.norm_pos_of_not_extends
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:39.86879+00:00
-- url     : https://prove2.me/submissions/8bbcb834-6359-4282-a6fd-992623bc13f0

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck
namespace GlobalTheory.CyclicNormCheck
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
    [Module.Finite F E] (σ : F →+* ℝ) (hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ)
    {y : E} (hy : y ≠ 0) : 0 < σ (Algebra.norm F y) := by
  classical
  let : Algebra F ℂ := (Complex.ofRealHom.comp σ).toAlgebra
  have hm : ∀ a : F, algebraMap F ℂ a = (σ a : ℂ) := fun _ => rfl
  let c : (E →ₐ[F] ℂ) → (E →ₐ[F] ℂ) := fun φ =>
    { (starRingEnd ℂ).comp φ.toRingHom with
      commutes' := fun a => by
        change starRingEnd ℂ (φ (algebraMap F E a)) = _
        rw [φ.commutes, hm, Complex.conj_ofReal] }
  have hc : ∀ φ e, c φ e = starRingEnd ℂ (φ e) := fun _ _ => rfl
  have hne : ∀ φ, c φ ≠ φ := by
    intro φ h
    apply hσ
    have hr : ∀ e, ((φ e).re : ℂ) = φ e := fun e =>
      Complex.conj_eq_iff_re.1 (by rw [← hc, h])
    refine ⟨{ toFun := fun e => (φ e).re, map_one' := by simp, map_zero' := by simp,
              map_add' := by simp, map_mul' := fun a b => ?_ }, ?_⟩
    · apply Complex.ofReal_injective
      rw [Complex.ofReal_mul, hr, hr, hr, map_mul]
    · ext a
      change (φ (algebraMap F E a)).re = σ a
      rw [φ.commutes, hm, Complex.ofReal_re]
  have hφ : ∀ φ : E →ₐ[F] ℂ, φ y ≠ 0 := fun φ => (map_ne_zero _).2 hy
  have hn : ∀ φ : E →ₐ[F] ℂ, (‖φ y‖ : ℂ) ≠ 0 := fun φ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hφ φ))
  have h1 : ∏ φ : E →ₐ[F] ℂ, (φ y / (‖φ y‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun φ _ => c φ) (fun φ _ => ?_) (fun φ _ _ => hne φ)
      (fun _ _ => Finset.mem_univ _) (fun φ _ => ?_)
    · rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have := hn φ
      push_cast
      field_simp
    · ext e; simp [hc]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun φ _ => hn φ),
    ← Algebra.norm_eq_prod_embeddings F ℂ y, hm] at h1
  have h2 : σ (Algebra.norm F y) = ∏ φ : E →ₐ[F] ℂ, ‖φ y‖ := by exact_mod_cast h1
  rw [h2]
  exact Finset.prod_pos fun φ _ => norm_pos_iff.2 (hφ φ)
end GlobalTheory.CyclicNormCheck
