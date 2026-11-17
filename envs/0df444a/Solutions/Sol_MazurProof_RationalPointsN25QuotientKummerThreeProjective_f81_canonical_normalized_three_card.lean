-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_canonical_normalized_three_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:23.229622+00:00
-- url     : https://prove2.me/submissions/c728b3c2-758e-4da8-b00f-48fc7c2874ba

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81FifthRoot25_isCyclotomic
import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeProjective_f81_segre_solutions_card

/-! Projective Kummer point counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientKummerThreeF81

open scoped BigOperators

noncomputable section

section Generic

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

end Generic

section CanonicalRestriction

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

end CanonicalRestriction

/-- The canonical normalized genus-four model has exactly 89 points over
`F81`, transported from the structural Kummer-Segre count. -/
theorem _root_.solution :
    Nat.card {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P} =
      89 := by
  calc
    Nat.card {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P} =
        Nat.card (SegreSolutions f81FifthRoot25) :=
      Nat.card_congr
        (segreSolutionsEquivCanonicalCurve
          f81FifthRoot25 f81FifthRoot25_isCyclotomic).symm
    _ = 89 := f81_segre_solutions_card

end

end MazurProof.RationalPointsN25QuotientKummerThreeProjective
