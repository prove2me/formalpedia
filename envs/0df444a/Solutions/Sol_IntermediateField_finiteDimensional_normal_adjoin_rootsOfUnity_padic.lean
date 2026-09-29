-- Prove2me | solution 1 for IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f800c7cc-e87e-52e0-bdff-f6c42e197f37

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open Polynomial

theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N) :
    FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∧ Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := by
  classical
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hm : 0 < q ^ N - 1 := by
    have : 1 < q ^ N := Nat.one_lt_pow hN.ne' hq
    omega

  set P : (↥K)[X] := X ^ (q ^ N - 1) - 1 with hP
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact Polynomial.X_pow_sub_C_ne_zero hm 1
  have hset : {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} = P.rootSet (PadicAlgCl q) := by
    ext ζ
    rw [Polynomial.mem_rootSet, hP]
    simp only [Set.mem_setOf_eq, map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact ⟨fun h => ⟨hP0, h⟩, fun h => h.2⟩
  rw [hset]
  haveI : IsSplittingField K (IntermediateField.adjoin K (P.rootSet (PadicAlgCl q))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  exact ⟨IsSplittingField.finiteDimensional _ P, Normal.of_isSplittingField P⟩

end S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
end P2MW
export P2MW.S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic (solution)
