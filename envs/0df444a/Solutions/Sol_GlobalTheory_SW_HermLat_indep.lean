-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:11.051595+00:00
-- url     : https://prove2.me/submissions/f1847697-ff5e-43bc-ad5a-0f1b8b96992c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HermLat
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (u v : Ψ → ℂ)
    (h : ∀ x : E, ∑ τ : Ψ, (τ.1 x * u τ + conj (τ.1 x) * v τ) = 0) : u = 0 := by
  let f : Ψ ⊕ Ψ → (E →* ℂ) := Sum.elim (fun τ => (τ.1 : E →* ℂ))
    (fun τ => (ComplexEmbedding.conjugate τ.1 : E →* ℂ))
  have inj : ∀ a b : E →+* ℂ, (a : E →* ℂ) = (b : E →* ℂ) → a = b := fun a b e =>
    RingHom.ext fun x => DFunLike.congr_fun e x
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) e
    · rw [Subtype.ext (inj _ _ e)]
    · exact absurd ((inj _ _ e) ▸ a.2) ((hΨ b.1).1 b.2)
    · exact absurd ((inj _ _ e).symm ▸ b.2) ((hΨ a.1).1 a.2)
    · have := congrArg ComplexEmbedding.conjugate (inj _ _ e)
      have e2 : a.1 = b.1 := (star_star a.1).symm.trans (this.trans (star_star b.1))
      rw [Subtype.ext e2]
  have li := (linearIndependent_monoidHom E ℂ).comp f hf
  have := Fintype.linearIndependent_iff.1 li (Sum.elim u v) (by
    funext x
    have := h x
    rw [Finset.sum_add_distrib] at this
    simpa [f, Fintype.sum_sum_type, Finset.sum_apply, mul_comm] using this)
  funext τ
  exact this (Sum.inl τ)
end GlobalTheory.SW.HermLat
