-- Prove2me | solution 1 for GlobalTheory.OriginFrame.rigVal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:05.685801+00:00
-- url     : https://prove2.me/submissions/332d387e-dfc9-4e96-b6a6-4204f2182e6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsAppellHumbertFrameIsRig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.OriginFrame
namespace GlobalTheory.OriginFrame
theorem _root_.solution (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by
  intro h0
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have key := congrArg e s.val_inv
  rw [map_mul, map_one, ← he, h0, zero_mul] at key
  exact zero_ne_one key
end GlobalTheory.OriginFrame
