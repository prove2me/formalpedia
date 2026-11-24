-- Prove2me | solution 1 for GlobalTheory.CuspBasis.expoMatch_of_basis_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:18.885238+00:00
-- url     : https://prove2.me/submissions/92a25e91-5b10-4d3d-a0ed-6a5e4578e87a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentMatchingIndependentOfCuspBasis
import Theorems.Thm_GlobalTheory_CuspBasis_isHerm_conj
import Theorems.Thm_GlobalTheory_CuspBasis_phase_change
import Theorems.Thm_GlobalTheory_CuspBasis_integral_change
import Theorems.Thm_GlobalTheory_CuspBasis_basis_inv
import Theorems.Thm_GlobalTheory_CuspBasis_conj_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.CuspBasis
open GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
variable {X : Data E r} {cu₀ cu : FJ.CuspFD X ρ} {P : Matrix (Fin ρ) (Fin ρ) E}
namespace GlobalTheory.CuspBasis
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ r ρ N X cu₀ cu P hP h H χ hχ
  have hQ := basis_inv hP h
  have H' := H _ (isHerm_conj P⁻¹ χ hχ)
  constructor
  · intro hA
    have := integral_change N h (H'.1 (phase_change hQ hA))
    rwa [conj_inv hP] at this
  · intro hB
    have := phase_change h (H'.2 (integral_change N hQ hB))
    rwa [conj_inv hP] at this
end GlobalTheory.CuspBasis
