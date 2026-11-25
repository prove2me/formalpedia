-- Prove2me | solution 1 for GlobalTheory.FGAbove.exists_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:26:06.783359+00:00
-- url     : https://prove2.me/submissions/b08b07e4-e71f-42bb-85ce-5424af47c61e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution (R S : FGAbove R₀) : ∃ T : FGAbove R₀, R ≤ T ∧ S ≤ T :=
  ⟨⟨R.1 ⊔ S.1, R.2.1.sup S.2.1, R.2.2.trans le_sup_left⟩, le_sup_left (a := R.1), le_sup_right (a := R.1)⟩
end FGAbove
end GlobalTheory
