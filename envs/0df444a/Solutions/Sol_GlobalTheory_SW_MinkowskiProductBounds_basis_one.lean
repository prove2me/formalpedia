-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.basis_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:50.662808+00:00
-- url     : https://prove2.me/submissions/413f7d65-bdd1-4abe-8ac9-8dbae12d3c3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_card_type
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
theorem _root_.solution (h : IsType Ψ) : ∃ b : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (Ψ → ℂ),
    ∀ x, x ∈ span ℤ (Set.range b) ↔ ∃ a : E, IsIntegral ℤ a ∧ x = fun τ => τ.1 a := by
  classical
  let u : Free.ChooseBasisIndex ℤ (𝓞 E) → Ψ → ℂ := fun j τ => τ.1 (integralBasis E j)
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun j => (c j : ℂ)) ?_ j
    · exact_mod_cast h1
    have key : ∀ τ ∈ Ψ, ∑ j, (c j : ℂ) * τ (integralBasis E j) = 0 := fun τ hτ => by
      simpa [u] using congrFun hc ⟨τ, hτ⟩
    ext σ
    simp only [canonicalEmbedding.latticeBasis_apply, Finset.sum_apply, Pi.smul_apply,
      canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
    by_cases hσ : σ ∈ Ψ
    · exact key σ hσ
    · have h2 : ComplexEmbedding.conjugate σ ∈ Ψ := by
        have := h σ; tauto
      have := congrArg conj (key _ h2)
      simpa using this
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℝ (Ψ → ℂ) := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, card_type h,
      Module.finrank_pi_fintype]
    simp
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' u hli hcard, fun x => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  let φ : E →ₗ[ℤ] (Ψ → ℂ) := (AddMonoidHom.pi fun τ : Ψ => τ.1.toAddMonoidHom).toIntLinearMap
  have : Set.range u = φ '' Set.range (integralBasis E) := by
    rw [← Set.range_comp]; rfl
  rw [this, span_image, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_span_integralBasis E).1 ha
    exact ⟨_, z.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (mem_span_integralBasis E).2 ⟨⟨a, ha⟩, rfl⟩, rfl⟩
end GlobalTheory.SW.MinkowskiProductBounds
