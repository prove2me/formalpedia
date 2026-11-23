-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:58.14902+00:00
-- url     : https://prove2.me/submissions/38ba0506-66d1-4d3f-8da1-d80ea611c12d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ComplexPoints
namespace _root_.GlobalTheory.ComplexPoints
theorem _root_.solution (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt x U h f ≠ 0 := by
  have e : x ⁻¹ᵁ X.basicOpen f = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).basicOpen (x.appLE U ⊤ h f) := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  rw [e]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  constructor
  · intro hs h0
    have hz : x.appLE U ⊤ h f = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of ℂ)).inv.hom h0
      simpa using this
    rw [hz, Scheme.basicOpen_zero] at hs
    obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
    exact (hs (show a ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)).elim
  · intro hne
    have hu : IsUnit (x.appLE U ⊤ h f) := by
      have := (isUnit_iff_ne_zero.mpr hne).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
      simpa using this
    rw [Scheme.basicOpen_of_isUnit _ hu]
end _root_.GlobalTheory.ComplexPoints
end GlobalTheory.ComplexPoints
