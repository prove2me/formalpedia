-- Prove2me | solution 1 for GlobalTheory.natCast_ne_zero_of_isUnit_of_fieldPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:48.229648+00:00
-- url     : https://prove2.me/submissions/2913e390-900e-4be7-b309-024305fd2ae0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedTorusExtensionOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfIsReducedOfRangeSubset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Scheme.{0}} {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ S) : (n : Ω) ≠ 0 := by
  have h := hn.map ((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.appTop.hom)
  rw [map_natCast] at h
  exact h.ne_zero
end GlobalTheory
