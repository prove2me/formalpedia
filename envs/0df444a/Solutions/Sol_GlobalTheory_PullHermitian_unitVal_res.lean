-- Prove2me | solution 1 for GlobalTheory.PullHermitian.unitVal_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:20.674838+00:00
-- url     : https://prove2.me/submissions/003b4416-d2e8-4cfa-9f27-97881fa882f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow

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
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.PullHermitian
theorem _root_.solution {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : unitVal x h (res hVU f) = unitVal x h' f := by
  ext
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    ((X.presheaf.map (homOfLE hVU).op ≫ x.appLE V ⊤ h).hom f.val) = _
  rw [Scheme.Hom.map_appLE]
  rfl
end GlobalTheory.PullHermitian
