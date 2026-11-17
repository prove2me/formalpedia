-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThree.unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:19.882987+00:00
-- url     : https://prove2.me/submissions/e3f388ba-7182-4dc5-9d08-241173e24919

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_ExplicitKummerThree
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty

/-! Segre factorization and eigencoordinate identities for the canonical curve in characteristic three. -/

namespace MazurProof.RationalPointsN25QuotientKummerThree

open RationalPointsN25QuotientF2

section StructuralModel

variable {K : Type*} [Field K] [CharP K 3]

end StructuralModel

section FifthPowerFibres

open scoped Pointwise

/-- In any field with 81 elements, a nonzero element is a fifth power if
and only if its sixteenth power is one.

This is the semantic criterion implemented by the terminal `F_81` Kummer
fibre table. -/
theorem _root_.solution
    {K : Type*} [Field K] [Finite K]
    (hcard : Nat.card K = 81) {c : K} (hc : c ≠ 0) :
    Units.mk0 c hc ∈ (powMonoidHom 5 : Kˣ →* Kˣ).range ↔
      c ^ 16 = 1 := by
  have hcard_units : Nat.card Kˣ = 80 := by
    rw [Nat.card_units, hcard]
  rw [fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty hcard_units,
    MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg (↑· : Kˣ → K) h
  · intro h
    apply Units.ext
    exact h

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
