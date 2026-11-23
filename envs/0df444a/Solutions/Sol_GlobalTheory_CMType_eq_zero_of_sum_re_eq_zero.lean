-- Prove2me | solution 1 for GlobalTheory.CMType.eq_zero_of_sum_re_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:53.388409+00:00
-- url     : https://prove2.me/submissions/c9c67206-5f26-4b90-b049-5cc79f610a7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)
namespace GlobalTheory.CMType
theorem _root_.solution (δ : Φ → ℂ)
    (h : ∀ a : 𝓞 E, ∑ τ : Φ, (τ.1 (a : E) * δ τ).re = 0) : δ = 0 := by
  have hli : LinearIndependent ℂ (fun τ : E →+* ℂ => (fun a : 𝓞 E => τ (a : E))) := by
    have h1 := linearIndependent_monoidHom (𝓞 E) ℂ
    refine h1.comp (fun τ : E →+* ℂ => (τ.comp (algebraMap (𝓞 E) E)).toMonoidHom) ?_
    intro τ τ' hτ
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    exact DFunLike.congr_fun hτ a
  have h2 := Fintype.linearIndependent_iff.mp hli
    (fun τ => Sum.elim δ (fun σ => conj (δ σ)) (Φ.sumEquiv.symm τ)) (by
      funext a
      rw [Finset.sum_apply, ← Φ.sumEquiv.sum_comp, Fintype.sum_sum_type]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      rw [← Finset.sum_add_distrib]
      have h3 : ((∑ τ : Φ, 2 * (τ.1 (a : E) * δ τ).re : ℝ) : ℂ) = 0 := by
        rw [← Finset.mul_sum, h a]; simp
      rw [← h3, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Complex.add_conj, map_mul]
      change δ τ * τ.1 a + conj (δ τ) * ComplexEmbedding.conjugate τ.1 a = _
      rw [ComplexEmbedding.conjugate_coe_eq]
      ring)
  funext τ
  simpa using h2 (Φ.sumEquiv (.inl τ))
end GlobalTheory.CMType
