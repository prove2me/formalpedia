-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.one_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:13.773899+00:00
-- url     : https://prove2.me/submissions/10c23950-53ca-4c7c-9299-78a31e7734b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_prod_type
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution (h : IsType Ψ) {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) :
    1 ≤ ∏ τ : Ψ, ‖τ.1 a‖ := by
  have h1 : (1 : ℝ) ≤ ∏ σ : E →+* ℂ, ‖σ a‖ := by
    have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    have h3 : ∏ σ : E →+* ℂ, σ a = ∏ σ : E →ₐ[ℚ] ℂ, σ a :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl
    rw [← norm_prod, h3, ← h2]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ ha)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact h0 (by simpa using hz.symm)
    rw [← hz]
    simp only [eq_intCast, map_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hz0
  rw [prod_type h] at h1
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, Finset.prod_mul_distrib] at h1
  have : 0 ≤ ∏ τ : Ψ, ‖τ.1 a‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith
end GlobalTheory.SW.MinkowskiProductBounds
