-- Prove2me | solution 1 for GlobalTheory.PureType.exists_isThetaUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:24.899512+00:00
-- url     : https://prove2.me/submissions/79044e35-3ee5-4c20-af00-cbe6feb2625f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.PureType
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.PureType
theorem _root_.solution (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) :
    ∃ u : HolUnif P.A P.L P.g, IsThetaUnif u := by
  obtain ⟨rig, hr⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, h₁, -, h₂, h₃, -, h₄, h₅, h₆, -⟩ := hT P rig hr
  exact ⟨u, Hm, χ, Ef, h₁, h₂, h₃, h₄, h₅, h₆⟩
end GlobalTheory.PureType
