-- Prove2me | solution 1 for GlobalTheory.SimultaneousDiophantineApprox.simultaneous_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:11.211795+00:00
-- url     : https://prove2.me/submissions/8dd0831b-06c5-49d9-809c-81b666f60d5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimultaneousDiophantineApprox
open NumberField
namespace GlobalTheory.SimultaneousDiophantineApprox
theorem _root_.solution {ι : Type} [Fintype ι] (N : ℕ) (hN : 0 < N) (a : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ,
      ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N := by
  classical
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN

  have hbox : ∀ (j : ℕ) (i : ι), (⌊Int.fract ((j : ℚ) * a i) * N⌋).toNat < N := by
    intro j i
    have h0 : 0 ≤ Int.fract ((j : ℚ) * a i) * N := mul_nonneg (Int.fract_nonneg _) hNq.le
    have h1 : Int.fract ((j : ℚ) * a i) * N < N := by
      have := Int.fract_lt_one ((j : ℚ) * a i)
      nlinarith
    have hlt : ⌊Int.fract ((j : ℚ) * a i) * N⌋ < (N : ℤ) := Int.floor_lt.mpr (by exact_mod_cast h1)
    have hnn : 0 ≤ ⌊Int.fract ((j : ℚ) * a i) * N⌋ := Int.floor_nonneg.mpr h0
    omega
  let f : Fin (N ^ Fintype.card ι + 1) → (ι → Fin N) := fun j i => ⟨_, hbox j i⟩

  have key : ∀ x y : Fin (N ^ Fintype.card ι + 1), x < y → f x = f y →
      ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ,
        ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N := by
    intro x y hxy hf
    have hxy' : (x : ℕ) < y := hxy
    have hy := y.2
    refine ⟨y - x, by omega, by omega, fun i => ⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋, fun i => ?_⟩
    have hv := congrArg Fin.val (congrFun hf i)
    simp only [f] at hv
    have hx0 : 0 ≤ Int.fract ((x : ℕ) * a i) * (N : ℚ) := mul_nonneg (Int.fract_nonneg _) hNq.le
    have hy0 : 0 ≤ Int.fract ((y : ℕ) * a i) * (N : ℚ) := mul_nonneg (Int.fract_nonneg _) hNq.le
    have hfl : ⌊Int.fract (((x : ℕ) : ℚ) * a i) * N⌋ = ⌊Int.fract (((y : ℕ) : ℚ) * a i) * N⌋ := by
      have := Int.floor_nonneg.mpr hx0
      have := Int.floor_nonneg.mpr hy0
      omega
    have hclose := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    have heq : (((y - x : ℕ) : ℕ) : ℚ) * a i - ((⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋ : ℤ) : ℚ) =
        Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i) := by
      rw [Nat.cast_sub hxy'.le]
      unfold Int.fract
      push_cast
      ring
    rw [heq, le_div_iff₀ hNq]
    have hm : |Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i)| * N =
        |Int.fract (((x : ℕ) : ℚ) * a i) * N - Int.fract (((y : ℕ) : ℚ) * a i) * N| := by
      rw [← sub_mul, abs_mul, abs_of_pos hNq, abs_sub_comm]
    rw [hm]
    exact hclose.le
  obtain ⟨x, y, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h hf
  · exact key y x h hf.symm
end GlobalTheory.SimultaneousDiophantineApprox
