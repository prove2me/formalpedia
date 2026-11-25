-- Prove2me | solution 1 for GlobalTheory.FGAbove.isFiltered
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:53.373645+00:00
-- url     : https://prove2.me/submissions/f7d88c2c-8b67-449e-9c50-6bd02c2ba819

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_GlobalTheory_FGAbove_exists_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
namespace GlobalTheory
namespace FGAbove
theorem _root_.solution (h : R₀.FG) : IsFiltered (FGAbove R₀) :=
  have : Nonempty (FGAbove R₀) := ⟨⟨R₀, h, le_rfl⟩⟩
  have : IsDirectedOrder (FGAbove R₀) := ⟨FGAbove.exists_ge⟩
  inferInstance
end FGAbove
end GlobalTheory
