-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.rename_inl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:20:20.741578+00:00
-- url     : https://prove2.me/submissions/41393290-20c8-4563-bf55-3f47a162bf6d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₂] [∀ k, Fintype (ι₂ k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution {Ω : Type} [Field Ω] (y₁ : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {f : MRing ι}
    (hf : f ∈ mCoordIdeal y₁) : rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y₁ y₂) := by
  have key : ∀ g : MRing ι, mConeMap (joinVec y₁ y₂) (rename (joinInl ι ι₂) g) =
      rename (Sum.inl : K → K ⊕ K₂) (mConeMap y₁ g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X]
      rfl
  have hf' : mConeMap y₁ f = 0 := hf
  change mConeMap (joinVec y₁ y₂) (rename (joinInl ι ι₂) f) = 0
  rw [key, hf', map_zero]
end GlobalTheory.CompanionTheory.Ar.SegreChart
