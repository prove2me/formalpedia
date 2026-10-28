-- Prove2me | solution 1 for NonconvexCost.Complexity.thm_4_3_shortening_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:18:53.669241+00:00
-- url     : https://prove2.me/submissions/c9d64dd1-b46e-4b32-9bd3-f44d2ba5b1bc

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

open scoped RealInnerProductSpace

namespace Aux_NC_thm43
open NonconvexCost.Complexity

theorem l42 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (L : ℝ) (hL : 0 < L) (g g' g'' : X) (hg : ‖g‖ ≤ L) (hg' : ‖g'‖ ≤ L)
    (hinner : ⟪g', g⟫ ≤ ‖g‖ ^ 2 / 2) (hshort : IsShortestIn g g' g'') :
    ‖g''‖ ^ 2 ≤ ‖g‖ ^ 2 * (1 - ‖g‖ ^ 2 / (16 * L ^ 2)) := by
  set t : ℝ := ‖g‖ ^ 2 / (8 * L ^ 2) with ht
  have hL2 : 0 < L ^ 2 := by positivity
  have hn0 : 0 ≤ ‖g‖ := norm_nonneg _
  have hn2 : ‖g‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hn0 hg 2
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    linarith
  have hmem : (1 - t) • g + t • g' ∈ segment ℝ g g' :=
    ⟨1 - t, t, by linarith, ht0, by ring, rfl⟩
  have hle := hshort.2 _ hmem
  have hv : (1 - t) • g + t • g' = g + t • (g' - g) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hv] at hle
  have hsq : ‖g''‖ ^ 2 ≤ ‖g + t • (g' - g)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hexp : ‖g + t • (g' - g)‖ ^ 2 =
      ‖g‖ ^ 2 + 2 * t * (⟪g', g⟫ - ‖g‖ ^ 2) + t ^ 2 * ‖g' - g‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm g g', Real.norm_eq_abs, abs_of_nonneg ht0]
    ring
  have hd : ‖g' - g‖ ≤ 2 * L := by
    have := norm_sub_le g' g
    linarith
  have hd2 : ‖g' - g‖ ^ 2 ≤ 4 * L ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hd 2
    nlinarith
  have h1 : 2 * t * (⟪g', g⟫ - ‖g‖ ^ 2) ≤ -(t * ‖g‖ ^ 2) := by nlinarith
  have h2 : t ^ 2 * ‖g' - g‖ ^ 2 ≤ t ^ 2 * (4 * L ^ 2) :=
    mul_le_mul_of_nonneg_left hd2 (by positivity)
  have h3 : ‖g‖ ^ 2 - t * ‖g‖ ^ 2 + t ^ 2 * (4 * L ^ 2) =
      ‖g‖ ^ 2 * (1 - ‖g‖ ^ 2 / (16 * L ^ 2)) := by
    rw [ht]
    field_simp
    ring
  linarith

end Aux_NC_thm43

open NonconvexCost.Complexity in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε) (g g' : ℕ → X) (hg0 : ‖g 0‖ ≤ L)
    (hg' : ∀ i, ‖g' i‖ ≤ L) (hinner : ∀ i, ⟪g' i, g i⟫ < ‖g i‖ ^ 2 / 2)
    (hshort : ∀ i, IsShortestIn (g i) (g' i) (g (i + 1))) (k : ℕ) (hk : ε < ‖g k‖) :
    (k : ℝ) < 16 * (L ^ 2 / ε ^ 2 - 1) := by
  have hL2 : 0 < 16 * L ^ 2 := by positivity
  have hN : ∀ i, ‖g i‖ ≤ L := by
    intro i
    induction i with
    | zero => exact hg0
    | succ i ih =>
      have := (hshort i).2 (g i) (left_mem_segment ℝ (g i) (g' i))
      linarith
  set ρ : ℕ → ℝ := fun i => ‖g i‖ ^ 2 / (16 * L ^ 2) with hρ
  have hρ0 : ∀ i, 0 ≤ ρ i := fun i => by positivity
  have hrec : ∀ i, ρ (i + 1) ≤ ρ i * (1 - ρ i) := by
    intro i
    have := Aux_NC_thm43.l42 L hL (g i) (g' i) (g (i + 1)) (hN i) (hg' i) (hinner i).le (hshort i)
    simp only [hρ]
    rw [div_le_iff₀ hL2]
    have e : ‖g i‖ ^ 2 / (16 * L ^ 2) * (1 - ‖g i‖ ^ 2 / (16 * L ^ 2)) * (16 * L ^ 2) =
        ‖g i‖ ^ 2 * (1 - ‖g i‖ ^ 2 / (16 * L ^ 2)) := by
      field_simp
    rw [e]
    exact this
  have hP : ∀ i : ℕ, ρ i * (16 + (i : ℝ)) ≤ 1 := by
    intro i
    induction i with
    | zero =>
      simp only [hρ, Nat.cast_zero, add_zero]
      have := pow_le_pow_left₀ (norm_nonneg _) hg0 2
      rw [div_mul_eq_mul_div, div_le_one hL2]
      linarith
    | succ i ih =>
      set r := ρ i with hr
      set m : ℝ := 16 + (i : ℝ) with hm
      have hm16 : 16 ≤ m := by rw [hm]; have := Nat.cast_nonneg (α := ℝ) i; linarith
      have r0 : 0 ≤ r := hρ0 i
      have A : r * (1 - r) * m ^ 2 ≤ m - 1 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - r * m) (by nlinarith : (0:ℝ) ≤ m - 1 - r * m)]
      have r1 : 0 ≤ r * (1 - r) := by
        apply mul_nonneg r0
        nlinarith
      have B : r * (1 - r) * (m + 1) * m ^ 2 ≤ 1 * m ^ 2 := by
        have : r * (1 - r) * (m + 1) * m ^ 2 = (m + 1) * (r * (1 - r) * m ^ 2) := by ring
        rw [this]
        nlinarith
      have C : r * (1 - r) * (m + 1) ≤ 1 := le_of_mul_le_mul_right B (by positivity)
      have e : (16 + ((i + 1 : ℕ) : ℝ)) = m + 1 := by rw [hm]; push_cast; ring
      rw [e]
      have := hrec i
      have hm1 : 0 ≤ m + 1 := by linarith
      calc ρ (i + 1) * (m + 1) ≤ r * (1 - r) * (m + 1) := mul_le_mul_of_nonneg_right this hm1
        _ ≤ 1 := C
  have hk2 : ε ^ 2 < ‖g k‖ ^ 2 := pow_lt_pow_left₀ hk hε.le (by norm_num)
  have h1 := hP k
  simp only [hρ] at h1
  rw [div_mul_eq_mul_div, div_le_one hL2] at h1
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : ε ^ 2 * (16 + (k : ℝ)) < 16 * L ^ 2 := by nlinarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have h3 : (16 + (k : ℝ)) < 16 * (L ^ 2 / ε ^ 2) := by
    rw [mul_div_assoc', lt_div_iff₀ hε2]
    linarith
  linarith
