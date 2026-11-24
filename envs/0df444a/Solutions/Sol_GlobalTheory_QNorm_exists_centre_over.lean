-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_centre_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:41.332268+00:00
-- url     : https://prove2.me/submissions/b7b9e526-ac06-40c0-bf3c-4c613afab4d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Theorems.Thm_GlobalTheory_QNorm_val_integer_le_one

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
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (u : Valuation E ℤᵐ⁰)
    (hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧
      ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ u (algebraMap (𝓞 E) E x) < 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {x | u (algebraMap (𝓞 E) E x) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add] at *
        exact u.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_integer_le_one u c)) hx }
  have hI : ∀ x : 𝓞 E, x ∈ I ↔ u (algebraMap (𝓞 E) E x) < 1 := fun x => Iff.rfl
  have hp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hI]; simp
    · intro a b hab
      rw [hI, map_mul, map_mul] at hab
      rw [hI, hI]
      by_contra hc
      push Not at hc
      exact absurd hab (not_lt.2 (one_le_mul hc.1 hc.2))
  have hc : ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ I ↔ a ∈ v.asIdeal := by
    intro a
    rw [hI, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, hu]
    exact v.valuation_lt_one_iff_mem a
  have hne : I ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    rw [eq_bot_iff]
    intro a ha
    have := (hc a).2 ha
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 this
  refine ⟨⟨I, hp, hne⟩, ?_, hI⟩
  ext a
  exact hc a
end GlobalTheory.QNorm
