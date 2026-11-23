-- Prove2me | solution 1 for GlobalTheory.EigenNorm.eq_zero_of_sum_embedding_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:31.829623+00:00
-- url     : https://prove2.me/submissions/b25ec82a-2e69-4294-b9ad-2eefc817c4ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.EigenNorm
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
namespace GlobalTheory.EigenNorm
theorem _root_.solution {E : Type} [Field E] [NumberField E] (f : (E →+* ℂ) → ℂ)
    (hf : ∀ s : 𝓞 E, ∑ τ : E →+* ℂ, τ (s : E) * f τ = 0) (τ : E →+* ℂ) : f τ = 0 := by
  have hinj : Function.Injective
      (fun τ : E →+* ℂ => ((τ.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)) := by
    intro τ₁ τ₂ h12
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun s => ?_
    exact DFunLike.congr_fun h12 s
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ hinj
  refine Fintype.linearIndependent_iff.1 hli f ?_ τ
  funext s
  simpa [mul_comm] using hf s
end GlobalTheory.EigenNorm
