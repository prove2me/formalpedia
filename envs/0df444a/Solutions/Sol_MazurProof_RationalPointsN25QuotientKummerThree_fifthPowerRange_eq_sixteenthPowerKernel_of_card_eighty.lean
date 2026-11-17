-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:19.321475+00:00
-- url     : https://prove2.me/submissions/0a65e41a-370f-4e78-97f1-824f2d34f668

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_ExplicitKummerThree

/-! Segre factorization and eigencoordinate identities for the canonical curve in characteristic three. -/

namespace MazurProof.RationalPointsN25QuotientKummerThree

open RationalPointsN25QuotientF2

section StructuralModel

variable {K : Type*} [Field K] [CharP K 3]

end StructuralModel

section FifthPowerFibres

open scoped Pointwise

/-- In a cyclic group of order 80, the fifth powers are exactly the elements
whose sixteenth power is one.

Indeed, the fifth-power image is contained in the sixteenth-power kernel
because `(x⁵)¹⁶=x⁸⁰=1`.  Both subgroups have order 16, by the standard
image and kernel cardinality formulas for power maps on finite cyclic
groups. -/
theorem _root_.solution
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (hcard : Nat.card G = 80) :
    (powMonoidHom 5 : G →* G).range =
      (powMonoidHom 16 : G →* G).ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change (y ^ 5) ^ 16 = 1
    rw [← pow_mul]
    norm_num
    simpa [hcard] using (pow_card_eq_one' (x := y))
  · rw [IsCyclic.card_powMonoidHom_ker,
      IsCyclic.card_powMonoidHom_range, hcard]
    norm_num

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
