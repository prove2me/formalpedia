-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_dense_solutions_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:21.894144+00:00
-- url     : https://prove2.me/submissions/8b961ace-b94b-43aa-8b65-c6aa786074de

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81FifthRoot25_isCyclotomic
import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeProjective_f81_kummer_solutions_card

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

/-- Removing the single extraneous zero-fibre Kummer solution leaves 86
points on the dense Segre chart. -/
theorem _root_.solution :
    Nat.card (DenseSolutions f81FifthRoot25) = 86 := by
  have hdense : Nat.card (DenseSolutions f81FifthRoot25) =
      1 + Nat.card (DenseNonzeroSolutions f81FifthRoot25) := by
    calc
      Nat.card (DenseSolutions f81FifthRoot25) =
          Nat.card (DenseZeroSolutions f81FifthRoot25 ⊕
            DenseNonzeroSolutions f81FifthRoot25) :=
        Nat.card_congr (densePartitionEquiv f81FifthRoot25)
      _ = Nat.card (DenseZeroSolutions f81FifthRoot25) +
          Nat.card (DenseNonzeroSolutions f81FifthRoot25) := Nat.card_sum
      _ = 1 + Nat.card (DenseNonzeroSolutions f81FifthRoot25) := by
        rw [Nat.card_congr (denseZeroEquivUnit f81FifthRoot25_isCyclotomic)]
        simp
  have hkummer : Nat.card (KummerSolutions f81FifthRoot25) =
      2 + Nat.card (KummerNonzeroSolutions f81FifthRoot25) := by
    calc
      Nat.card (KummerSolutions f81FifthRoot25) =
          Nat.card (KummerZeroSolutions f81FifthRoot25 ⊕
            KummerNonzeroSolutions f81FifthRoot25) :=
        Nat.card_congr (kummerPartitionEquiv f81FifthRoot25)
      _ = Nat.card (KummerZeroSolutions f81FifthRoot25) +
          Nat.card (KummerNonzeroSolutions f81FifthRoot25) := Nat.card_sum
      _ = 2 + Nat.card (KummerNonzeroSolutions f81FifthRoot25) := by
        rw [Nat.card_congr (kummerZeroEquivBool f81FifthRoot25_isCyclotomic)]
        simp
  have hnz : Nat.card (DenseNonzeroSolutions f81FifthRoot25) =
      Nat.card (KummerNonzeroSolutions f81FifthRoot25) :=
    Nat.card_congr (denseNonzeroEquivKummerNonzero f81FifthRoot25)
  rw [hdense, hnz]
  rw [f81_kummer_solutions_card] at hkummer
  omega

section CanonicalRestriction

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

end CanonicalRestriction

end

end MazurProof.RationalPointsN25QuotientKummerThreeProjective
