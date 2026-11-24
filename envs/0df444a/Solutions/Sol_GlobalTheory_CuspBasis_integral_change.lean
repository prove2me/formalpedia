-- Prove2me | solution 1 for GlobalTheory.CuspBasis.integral_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:06.040521+00:00
-- url     : https://prove2.me/submissions/1ac17b9a-accd-45f6-ac8e-de206a0aa67c

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
import Theorems.Thm_GlobalTheory_CuspBasis_dualOE_change
import Theorems.Thm_GlobalTheory_CuspBasis_form_change

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
theorem _root_.solution (N : ℕ) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b)
    {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu),
      (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) :
    ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀),
      (N : E) * ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) ∈
        Set.range (algebraMap (𝓞 E) E) := fun u hu m hm => by
  rw [form_change]
  exact hχ _ (dualOE_change 1 h hu) _ (dualOE_change 1 h hm)
end GlobalTheory.CuspBasis
