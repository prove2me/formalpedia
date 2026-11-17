-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_segre_solutions_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:22.477591+00:00
-- url     : https://prove2.me/submissions/9a66a9dd-a437-4eda-815e-aa5891a82a49

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81FifthRoot25_isCyclotomic
import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeProjective_f81_dense_solutions_card

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

/-- The normalized projective Segre model has 86 dense points and three
boundary points, hence 89 points in total. -/
theorem _root_.solution :
    Nat.card (SegreSolutions f81FifthRoot25) = 89 := by
  calc
    Nat.card (SegreSolutions f81FifthRoot25) =
        Nat.card (DenseSolutions f81FifthRoot25 ⊕
          LeftBoundarySolutions f81FifthRoot25 ⊕
          RightBoundarySolutions f81FifthRoot25 ⊕ Unit) :=
      Nat.card_congr (segreSolutionsEquivCharts f81FifthRoot25)
    _ = Nat.card (DenseSolutions f81FifthRoot25) +
        Nat.card (LeftBoundarySolutions f81FifthRoot25) +
        Nat.card (RightBoundarySolutions f81FifthRoot25) +
        Nat.card Unit := by
      simp only [Nat.card_sum, Nat.add_assoc]
    _ = 86 + 1 + 1 + 1 := by
      rw [f81_dense_solutions_card,
        Nat.card_congr (leftBoundaryEquivUnit f81FifthRoot25_isCyclotomic),
        Nat.card_congr (rightBoundaryEquivUnit f81FifthRoot25_isCyclotomic)]
      simp
    _ = 89 := by norm_num

section CanonicalRestriction

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

end CanonicalRestriction

end

end MazurProof.RationalPointsN25QuotientKummerThreeProjective
