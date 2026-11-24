-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.exists_norm_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:16.332305+00:00
-- url     : https://prove2.me/submissions/4d618a90-d730-4611-ac1d-e427a93cb3be

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
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E]
    (τ : E →+* ℝ) : ∃ y : E, τ (algebraMap F E (Algebra.norm F y)) < 0 := by
  classical
  have : CharZero E := τ.charZero
  have : CharZero F := (τ.comp (algebraMap F E)).charZero
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hinj : Function.Injective fun g : E ≃ₐ[F] E => τ (g α) := by
    intro g h e
    have e' : g α = h α := τ.injective e
    have : (g : E →ₐ[F] E) = h := by
      apply (Field.primitive_element_iff_algHom_eq_of_eval' F E (fun x => IsGalois.splits F x) α).1 hα
      exact e'
    ext z
    exact DFunLike.congr_fun this z
  obtain ⟨g0, -, hg0⟩ := Finset.exists_max_image Finset.univ (fun g : E ≃ₐ[F] E => τ (g α))
    ⟨1, Finset.mem_univ _⟩
  have hlt : ∀ g, g ≠ g0 → τ (g α) < τ (g0 α) := fun g hg =>
    lt_of_le_of_ne (hg0 g (Finset.mem_univ _)) fun e => hg (hinj e)
  obtain ⟨b, hb, hb'⟩ : ∃ b < τ (g0 α), ∀ g, g ≠ g0 → τ (g α) ≤ b := by
    by_cases hne : (Finset.univ.erase g0).Nonempty
    · obtain ⟨g1, h1, h2⟩ := Finset.exists_max_image _ (fun g : E ≃ₐ[F] E => τ (g α)) hne
      exact ⟨_, hlt g1 (Finset.ne_of_mem_erase h1), fun g hg => h2 g (by simp [hg])⟩
    · exact ⟨τ (g0 α) - 1, by linarith, fun g hg => absurd ⟨g, by simp [hg]⟩ hne⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hb
  refine ⟨(q : E) - α, ?_⟩
  rw [Algebra.norm_eq_prod_automorphisms, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ g0)]
  apply mul_neg_of_neg_of_pos
  · simp only [map_sub, map_ratCast]; linarith
  · refine Finset.prod_pos fun g hg => ?_
    have := hb' g (Finset.ne_of_mem_erase hg)
    simp only [map_sub, map_ratCast]; linarith
end GlobalTheory.CyclicNormCheck
