-- Prove2me | solution 1 for GlobalTheory.end_eq_one_of_pow_eq_one_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:02:24.616522+00:00
-- url     : https://prove2.me/submissions/d992464d-4323-4358-b0f3-c3c481e5ae54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Theorems.Thm_GlobalTheory_exists_invariant_nat_length_lattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n M : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) (hM : 3 ≤ M)
    (h : ∀ y, ∃ z, σ y = y + M • z) : σ = 1 := by
  obtain ⟨p, h1, h2, h3, h4⟩ := exists_invariant_nat_length_lattice Y σ n hn hσ
  have key : ∀ (k : ℕ) (y : Y), p y = k → σ y = y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro y hy
      obtain ⟨z, hz⟩ := h y
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have : y = 0 := h3 y (hy.trans hk)
        rw [this, map_zero]
      have hle : M * p z ≤ k + k := by
        have := h1 (σ y) y
        rw [h4, hy, hz, add_sub_cancel_left, h2] at this
        exact this
      have hlt : p z < k := by nlinarith
      have hzz : σ z = z := ih _ hlt z rfl
      have hj : ∀ j : ℕ, (σ ^ j) y = y + (j * M) • z := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ', Module.End.mul_apply, ihj, map_add, map_nsmul, hzz, hz, add_mul, one_mul,
            add_smul]
          abel
      have h0 : (n * M) • z = 0 := by
        have := hj n
        rw [hσ, Module.End.one_apply] at this
        exact left_eq_add.mp this
      have h00 : p z = 0 := by
        have e := h2 (n * M) z
        have e0 := h2 0 z
        rw [zero_smul, zero_mul] at e0
        rw [h0, e0] at e
        have : 0 < n * M := Nat.mul_pos hn (by omega)
        rcases Nat.mul_eq_zero.mp e.symm with h' | h'
        · omega
        · exact h'
      rw [hz, h3 z h00, smul_zero, add_zero]
  ext y
  exact key _ y rfl
end GlobalTheory
