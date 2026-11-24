-- Prove2me | solution 1 for GlobalTheory.exists_invariant_nat_length_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:26.911019+00:00
-- url     : https://prove2.me/submissions/b5b0035e-f10e-4244-ab0a-1f48f4baf8e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Theorems.Thm_GlobalTheory_exists_nat_length_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) :
    ∃ p : Y → ℕ, (∀ x y, p (x - y) ≤ p x + p y) ∧ (∀ (m : ℕ) y, p (m • y) = m * p y) ∧
      (∀ y, p y = 0 → y = 0) ∧ ∀ y, p (σ y) = p y := by
  obtain ⟨q, h1, h2, h3⟩ := exists_nat_length_lattice Y
  refine ⟨fun y => ∑ j ∈ Finset.range n, q ((σ ^ j) y), ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub]
    exact h1 _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, h2]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    have := hy 0 (Finset.mem_range.mpr hn)
    exact h3 y (by simpa using this)
  · intro y
    have e1 := Finset.sum_range_succ (fun j => q ((σ ^ j) y)) n
    have e2 := Finset.sum_range_succ' (fun j => q ((σ ^ j) y)) n
    have e3 : ∑ j ∈ Finset.range n, q ((σ ^ j) (σ y)) =
        ∑ j ∈ Finset.range n, q ((σ ^ (j + 1)) y) :=
      Finset.sum_congr rfl fun j _ => by rw [pow_succ, Module.End.mul_apply]
    rw [hσ] at e1
    rw [pow_zero] at e2
    simp only [e3]
    omega
end GlobalTheory
