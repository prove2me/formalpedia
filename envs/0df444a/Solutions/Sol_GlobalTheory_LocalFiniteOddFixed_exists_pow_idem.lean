-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.exists_pow_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:10.128832+00:00
-- url     : https://prove2.me/submissions/76b9fb8b-ce72-4110-915b-b93a2e5b250a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (M : Type) [Monoid M] [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
  have key : ∀ i j : ℕ, i < j → x ^ i = x ^ j → ∃ n : ℕ, 0 < n ∧ x ^ n * x ^ n = x ^ n := by
    intro i j hij h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : ∀ k : ℕ, x ^ (i + k * (d + 1)) = x ^ i := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : i + (k + 1) * (d + 1) = (i + d + 1) + k * (d + 1) := by ring
        rw [this, pow_add, ← h, ← pow_add, ih]
    refine ⟨(i + 1) * (d + 1), by positivity, ?_⟩
    have e1 : (i + 1) * (d + 1) = i + (i * d + d + 1) := by ring
    have e2 : (i + 1) * (d + 1) + (i + 1) * (d + 1)
        = (i + (i + 1) * (d + 1)) + (i * d + d + 1) := by ring
    rw [← pow_add, e2, pow_add, h1, ← pow_add, ← e1]
  obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i j hlt h
  · exact key j i hlt h.symm
end GlobalTheory.LocalFiniteOddFixed
