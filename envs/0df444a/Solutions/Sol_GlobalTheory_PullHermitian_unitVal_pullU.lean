-- Prove2me | solution 1 for GlobalTheory.PullHermitian.unitVal_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:08.295481+00:00
-- url     : https://prove2.me/submissions/85815c00-b812-4f10-b72e-6bad6edb3ea6

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
theorem _root_.solution {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U))
    (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)ˣ) :
    unitVal x h (pullU φ U f) = unitVal (x ≫ φ) h' f := by
  ext
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
    ((φ.app U ≫ x.appLE _ ⊤ h).hom f.val) = _
  rw [← Scheme.Hom.comp_appLE x φ U ⊤ h']
  rfl
end GlobalTheory.PullHermitian
