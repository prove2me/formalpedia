-- Prove2me | solution 1 for MazurCampaign.order_twenty_five_canonical_point
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:41.71153+00:00
-- url     : https://prove2.me/submissions/55c033d6-8fa2-4b39-81a6-2225146ef563

import Mathlib
import Theorems.Thm_MazurCampaign_hasRationalPointOfOrder_of_torsion
import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_TorsionDefs
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_tateCanonicalCoordinates25_nonzero
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_tateCanonicalCoordinates25_onCanonical
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_tateCanonicalCoordinates25_not_isCusp
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_RationalPointsN25QuotientAction
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_TateOrder25Factor_order25_to_explicit_obstruction

namespace MazurCampaign

open MazurProof

open MazurProof.RationalPointsN25CanonicalPoints

open MazurProof.RationalPointsN25QuotientAction

open MazurProof.RationalPointsN25CanonicalSourceBridge

/-- Exact order twenty-five gives a noncuspidal rational point of the canonical
quadric-cubic intersection, with the explicit Tate-to-canonical coordinates. -/
theorem _root_.solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : RationalTorsion E) (hx : addOrderOf x = 25) :
    ∃ b c : ℚ,
      NonzeroQuadruple (tateCanonicalCoordinates25 b c).x
        (tateCanonicalCoordinates25 b c).y (tateCanonicalCoordinates25 b c).z
        (tateCanonicalCoordinates25 b c).w ∧
      OnCanonical25 (tateCanonicalCoordinates25 b c) ∧
      ¬ IsCusp25 (tateCanonicalCoordinates25 b c) := by
  obtain ⟨b, c, _, hb, h5, hF⟩ :=
    TateOrder25Factor.order25_to_explicit_obstruction E
      (hasRationalPointOfOrder_of_torsion E x 25 hx)
  exact ⟨b, c, tateCanonicalCoordinates25_nonzero hb h5 hF,
    tateCanonicalCoordinates25_onCanonical hb h5 hF,
    tateCanonicalCoordinates25_not_isCusp hb h5 hF⟩

end MazurCampaign
