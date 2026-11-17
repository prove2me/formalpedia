-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_kummer_solutions_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:17:35.553575+00:00
-- url     : https://prove2.me/submissions/55ead290-421e-4b20-ae3f-5e0604fb80fa

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_actual_fiber_sum
import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree

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

/-- The actual Kummer solution type has cardinality 87, by summing the
proved fifth-power root cardinalities over all quotient parameters. -/
theorem _root_.solution :
    Nat.card (KummerSolutions f81FifthRoot25) = 87 := by
  calc
    Nat.card (KummerSolutions f81FifthRoot25) =
        Nat.card (Σ t : F81,
          {r : F81 // canonicalKummerPolynomial25Three f81FifthRoot25 r t = 0}) :=
      Nat.card_congr (kummerSolutionsEquivSigma f81FifthRoot25)
    _ = ∑ t : F81,
        Nat.card {r : F81 //
          canonicalKummerPolynomial25Three f81FifthRoot25 r t = 0} :=
      Nat.card_sigma
    _ = 87 := f81_kummer_actual_fiber_sum

section CanonicalRestriction

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

end CanonicalRestriction

end

end MazurProof.RationalPointsN25QuotientKummerThreeProjective
