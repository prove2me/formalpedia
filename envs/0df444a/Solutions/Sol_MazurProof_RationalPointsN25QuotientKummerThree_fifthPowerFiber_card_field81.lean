-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_field81
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:20.420215+00:00
-- url     : https://prove2.me/submissions/eeddbe7a-d5c9-474d-aec0-fb51c666ebfa

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_ExplicitKummerThree
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerFiber_card_of_not_mem_range
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerFiber_card_of_mem_range

/-! Segre factorization and eigencoordinate identities for the canonical curve in characteristic three. -/

namespace MazurProof.RationalPointsN25QuotientKummerThree

open RationalPointsN25QuotientF2

section StructuralModel

variable {K : Type*} [Field K] [CharP K 3]

end StructuralModel

section FifthPowerFibres

open scoped Pointwise

/-- The complete fifth-power fibre classifier over an 81-element field.

The zero target has the single root zero.  A nonzero target has five roots
when its sixteenth power is one, and no roots otherwise.  This theorem is the
abstract mathematical justification for the executable values `1`, `5`, and
`0` used in the one-dimensional Kummer certificate. -/
theorem _root_.solution
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hcard : Nat.card K = 81) (c : K) :
    Nat.card {r : K // r ^ 5 = c} =
      if c = 0 then 1 else if c ^ 16 = 1 then 5 else 0 := by
  by_cases hc : c = 0
  · subst c
    simp
  · rw [if_neg hc]
    have hcard_units : Nat.card Kˣ = 80 := by
      rw [Nat.card_units, hcard]
    by_cases hpow : c ^ 16 = 1
    · rw [if_pos hpow]
      have hrange :
          Units.mk0 c hc ∈ (powMonoidHom 5 : Kˣ →* Kˣ).range :=
        (unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one hcard hc).2 hpow
      calc
        Nat.card {r : K // r ^ 5 = c} =
            Nat.card {u : Kˣ // u ^ 5 = Units.mk0 c hc} :=
          Nat.card_congr (nonzeroFifthPowerFiberEquivUnits hc)
        _ = 5 := fifthPowerFiber_card_of_mem_range hcard_units hrange
    · rw [if_neg hpow]
      have hrange :
          Units.mk0 c hc ∉ (powMonoidHom 5 : Kˣ →* Kˣ).range := by
        intro hrange
        exact hpow
          ((unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one hcard hc).1 hrange)
      calc
        Nat.card {r : K // r ^ 5 = c} =
            Nat.card {u : Kˣ // u ^ 5 = Units.mk0 c hc} :=
          Nat.card_congr (nonzeroFifthPowerFiberEquivUnits hc)
        _ = 0 := fifthPowerFiber_card_of_not_mem_range hrange

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
