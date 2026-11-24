-- Prove2me | solution 1 for GlobalTheory.exists_nat_length_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:16.831911+00:00
-- url     : https://prove2.me/submissions/6fd95e4e-a605-4b16-a87f-17e23fab65ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice

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
theorem _root_.solution (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] :
    ∃ q : Y → ℕ, (∀ x y, q (x - y) ≤ q x + q y) ∧ (∀ (m : ℕ) y, q (m • y) = m * q y) ∧
      ∀ y, q y = 0 → y = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ Y
  refine ⟨fun y => ∑ i, (b.repr y i).natAbs, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub, Finsupp.sub_apply]
    exact Int.natAbs_sub_le _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    apply b.repr.injective
    ext i
    simpa using hy i (Finset.mem_univ i)
end GlobalTheory
