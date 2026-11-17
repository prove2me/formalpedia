-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_of_not_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:18.553283+00:00
-- url     : https://prove2.me/submissions/785d9bc3-b38e-4aa7-9532-bcc69d46dce5

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

/-- A point outside the image of the fifth-power map has an empty fibre. -/
theorem _root_.solution
    {G : Type*} [CommGroup G] [Finite G] {c : G}
    (hc : c ∉ (powMonoidHom 5 : G →* G).range) :
    Nat.card {u : G // u ^ 5 = c} = 0 := by
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun u => hc ⟨u, u.property⟩⟩

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
