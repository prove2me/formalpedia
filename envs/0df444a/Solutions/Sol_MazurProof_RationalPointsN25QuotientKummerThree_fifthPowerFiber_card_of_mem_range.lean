-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_of_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:17.904982+00:00
-- url     : https://prove2.me/submissions/38441259-743c-4a6a-ab85-240613eb8cd2

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

/-- Every nonempty fibre of the fifth-power map on a cyclic group of order
80 has five elements.

A chosen point identifies its fibre with the kernel of the homomorphism;
that kernel has order `gcd(80,5)=5`. -/
theorem _root_.solution
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (hcard : Nat.card G = 80) {c : G}
    (hc : c ∈ (powMonoidHom 5 : G →* G).range) :
    Nat.card {u : G // u ^ 5 = c} = 5 := by
  rcases hc with ⟨a, rfl⟩
  calc
    Nat.card {u : G // u ^ 5 = a ^ 5} =
        Nat.card (powMonoidHom 5 : G →* G).ker := by
      change Nat.card ↑((powMonoidHom 5 : G →* G) ⁻¹' {
          (powMonoidHom 5 : G →* G) a}) = _
      exact Nat.card_congr
        ((powMonoidHom 5 : G →* G).fiberEquivKer a)
    _ = 5 := by
      rw [IsCyclic.card_powMonoidHom_ker, hcard]
      norm_num

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
