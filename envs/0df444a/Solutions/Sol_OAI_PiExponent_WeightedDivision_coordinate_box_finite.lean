-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.coordinate_box_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:02:05.514379+00:00
-- url     : https://prove2.me/submissions/8b232784-b656-43b4-b991-8ac2250c13ba

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) :
    {u : ι →₀ ℕ | ∀ i, u i ≤ N}.Finite := by
  let encode : {u : ι →₀ ℕ // ∀ i, u i ≤ N} → (ι → Fin (N + 1)) :=
    fun u i => ⟨u.1 i, Nat.lt_succ_of_le (u.2 i)⟩
  have hencode : Function.Injective encode := by
    intro u v huv
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun huv i)
  exact Set.finite_coe_iff.mp (Finite.of_injective encode hencode)
