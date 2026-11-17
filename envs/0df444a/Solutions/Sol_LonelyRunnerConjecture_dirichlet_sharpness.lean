-- Prove2me | solution 1 for LonelyRunnerConjecture.dirichlet_sharpness
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:12:09.526918+00:00
-- url     : https://prove2.me/submissions/c182a5e1-d0ca-442b-9bd3-ac0a39d9526d

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs
set_option autoImplicit false
namespace LonelyRunnerConjecture

theorem distToNearestInt_le_abs_sub_int (x : ℝ) (m : ℤ) : distToNearestInt x ≤ |x - m| := by
  unfold distToNearestInt
  rcases le_or_gt m ⌊x⌋ with h | h
  · apply min_le_of_left_le
    have : (m : ℝ) ≤ ⌊x⌋ := by exact_mod_cast h
    rw [Int.fract, abs_of_nonneg (by linarith [Int.floor_le x])]
    linarith
  · apply min_le_of_right_le
    have : (⌊x⌋ : ℝ) + 1 ≤ m := by exact_mod_cast h
    have hlt := Int.lt_floor_add_one x
    rw [Int.fract, abs_of_neg (by linarith)]
    linarith

theorem dirichlet_sharpness (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ∃ v ∈ Finset.Icc 1 k, distToNearestInt (t * (v : ℝ)) ≤ (1 : ℝ) / (k + 1 : ℝ) := by
  have hK : (0:ℝ) < k + 1 := by positivity
  let a : Fin (k+1) → ℝ := fun i => Int.fract (t * (i : ℕ))
  have ha0 : ∀ i, 0 ≤ a i := fun i => Int.fract_nonneg _
  have ha1 : ∀ i, a i < 1 := fun i => Int.fract_lt_one _
  have hfl0 : ∀ i, 0 ≤ ⌊a i * (k+1)⌋ := fun i => Int.floor_nonneg.2 (by have := ha0 i; positivity)
  have hflk : ∀ i, ⌊a i * (k+1)⌋ < k + 1 := by
    intro i
    rw [Int.floor_lt]
    push_cast
    nlinarith [ha1 i]
  let f : Fin (k+1) → Fin (k+1) := fun i => ⟨(⌊a i * (k+1)⌋).toNat, by
    have := hflk i; have := hfl0 i; omega⟩
  have hfeq : ∀ i j, f i = f j → ⌊a i * (k+1)⌋ = ⌊a j * (k+1)⌋ := by
    intro i j h
    have h' := congrArg Fin.val h
    simp only [f] at h'
    have := hfl0 i; have := hfl0 j
    omega
  by_cases hinj : Function.Injective f
  · obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hinj) (Fin.last k)
    have hfi : ⌊a i * (k+1)⌋ = k := by
      have h' := congrArg Fin.val hi
      simp only [f, Fin.val_last] at h'
      have := hfl0 i
      omega
    have hi0 : (i : ℕ) ≠ 0 := by
      intro h0
      have : a i = 0 := by simp [a, h0]
      rw [this, zero_mul, Int.floor_zero] at hfi
      omega
    refine ⟨i, Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hi0, Nat.lt_succ_iff.1 i.2⟩, ?_⟩
    have hle : (k:ℝ) ≤ a i * (k+1) := by
      have := Int.floor_le (a i * (k+1)); rw [hfi] at this; exact_mod_cast this
    refine (distToNearestInt_le_abs_sub_int _ (⌊t * (i:ℕ)⌋ + 1)).trans ?_
    have hfr : t * ((i : ℕ) : ℝ) - ((⌊t * (i:ℕ)⌋ + 1 : ℤ) : ℝ) = a i - 1 := by
      simp only [a, Int.fract]; push_cast; ring
    rw [hfr, abs_of_neg (by linarith [ha1 i]), le_div_iff₀ hK]
    nlinarith
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have hfl := hfeq i j hij
    have habs : |a i * (k+1) - a j * (k+1)| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    -- WLOG i < j
    have key : ∀ i j : Fin (k+1), (i:ℕ) < j → |a i * (k+1) - a j * (k+1)| < 1 →
        ∃ v ∈ Finset.Icc 1 k, distToNearestInt (t * (v : ℝ)) ≤ (1 : ℝ) / (k + 1 : ℝ) := by
      intro i j hlt hab
      refine ⟨(j:ℕ) - i, Finset.mem_Icc.2 ⟨by omega, by have := j.2; omega⟩, ?_⟩
      refine (distToNearestInt_le_abs_sub_int _ (⌊t * (j:ℕ)⌋ - ⌊t * (i:ℕ)⌋)).trans ?_
      have hfr : t * (((j:ℕ) - (i:ℕ) : ℕ) : ℝ) - ((⌊t * (j:ℕ)⌋ - ⌊t * (i:ℕ)⌋ : ℤ) : ℝ) = a j - a i := by
        simp only [a, Int.fract]; rw [Nat.cast_sub hlt.le]; push_cast; ring
      rw [hfr, le_div_iff₀ hK]
      have : |a j - a i| * (k+1) = |a i * (k+1) - a j * (k+1)| := by
        rw [← abs_of_pos hK, ← abs_mul, abs_of_pos hK, ← abs_neg]; congr 1; ring
      linarith
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact key i j h habs
    · exact key j i h (by rw [abs_sub_comm]; exact habs)

end LonelyRunnerConjecture

theorem solution (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    ∃ v ∈ Finset.Icc 1 k, LonelyRunnerConjecture.distToNearestInt (t * (v : ℝ)) ≤ (1 : ℝ) / (k + 1 : ℝ) :=
  LonelyRunnerConjecture.dirichlet_sharpness k hk t
