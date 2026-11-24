-- Prove2me | solution 1 for GlobalTheory.EigDecomp.exists_integral_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:11.833368+00:00
-- url     : https://prove2.me/submissions/97f56441-f58a-4149-a95e-7ada08e6c7d5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField
open GlobalTheory GlobalTheory.EigDecomp
namespace GlobalTheory.EigDecomp
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ α : 𝓞 E, (∀ τ τ' : E →+* ℂ, τ (α : E) = τ' (α : E) → τ = τ') ∧
      ∀ a : 𝓞 E, ∃ N : ℤ, N ≠ 0 ∧ ∃ g : ℤ[X], aeval α g = N • a := by
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({α0} : Finset E)
  have hi : IsIntegral ℤ (d • α0) := hint α0 (Finset.mem_singleton_self _)
  let α : 𝓞 E := ⟨d • α0, hi⟩
  have hαE : (α : E) = d • α0 := rfl
  have hadjF : ℚ⟮(α : E)⟯ = ⊤ := by
    refine top_le_iff.mp (hα0 ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have h1 : α0 = ((d : ℚ)⁻¹) • (α : E) := by
      rw [hαE, zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap ℚ E) d, ← map_mul,
        inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), map_one, one_mul]
    rw [h1]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hadj : Algebra.adjoin ℚ {(α : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (α : E)), hadjF, IntermediateField.top_toSubalgebra]
  refine ⟨α, fun τ τ' h => ?_, fun a => ?_⟩
  · have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by rintro x rfl; exact h)
    ext x
    exact congrArg (fun f : E →ₐ[ℚ] ℂ => f x) this
  · have ha : (a : E) ∈ Algebra.adjoin ℚ {(α : E)} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
    refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors ℤ) g, ?_⟩
    apply RingOfIntegers.coe_injective
    have hg' : aeval (algebraMap (𝓞 E) E α) g = algebraMap (𝓞 E) E a := hg
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb, map_zsmul, hg', map_zsmul]
end GlobalTheory.EigDecomp
