-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientAction.isCusp25_iff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:58.470221+00:00
-- url     : https://prove2.me/submissions/88687b35-4c3f-470f-8663-360a285a5e68

import Mathlib
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_RationalPointsN25QuotientAction

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_OrderFiveAction` and their helpers. -/

namespace MazurProof.RationalPointsN25QuotientAction

open RationalPointsN25CanonicalPoints

/-- The displayed disjunction in `IsCanonicalCusp25` is exactly the five
named cusp representatives. -/
theorem _root_.solution (p : Coordinates25) :
    IsCusp25 p ↔
      ProjectivelyEqual25 p cusp25A ∨
      ProjectivelyEqual25 p cusp25B ∨
      ProjectivelyEqual25 p cusp25C ∨
      ProjectivelyEqual25 p cusp25D ∨
      ProjectivelyEqual25 p cusp25E := by
  rfl

end MazurProof.RationalPointsN25QuotientAction
