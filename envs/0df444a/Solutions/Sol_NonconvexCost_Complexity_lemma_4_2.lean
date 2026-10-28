-- Prove2me | solution 1 for NonconvexCost.Complexity.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:16:31.652534+00:00
-- url     : https://prove2.me/submissions/a0d1e450-760e-4aab-ac62-864cc52737f7

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

open scoped RealInnerProductSpace

open NonconvexCost.Complexity in
theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
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
