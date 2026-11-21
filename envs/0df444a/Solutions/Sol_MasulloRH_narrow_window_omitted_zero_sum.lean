-- Prove2me | solution 1 for MasulloRH.narrow_window_omitted_zero_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @klatvanen
-- created : 2026-11-20T22:40:01.179946+00:00
-- url     : https://prove2.me/submissions/a3ccfc3c-a495-4803-b87a-4c5e3a1f492c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_summatory_rpow_bound
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound
import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs

open MeasureTheory Set MasulloRH ConnesRZ

theorem solution (α : ℝ) (hα : 0 < α) (hsmall : α < 1/2)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by
  dsimp only
  -- Under the Mertens-type bound with exponent `1/2 + α/2`, every critical zero
  -- lies within `α/2` of the critical line.
  have hstrip : ∀ z : ℂ, ConnesRZ.IsCriticalZero z → |z.re - 1/2| ≤ α / 2 := by
    intro z hz
    obtain ⟨hz0, hre0, hre1⟩ := hz
    have hM := moebius_summatory_rpow_bound (α / 2) (by linarith)
    have hr : (0 : ℝ) ≤ 1 / 2 + α / 2 := by linarith
    have hnt : ¬∃ n : ℕ, z = -2 * (↑n + 1) := by
      rintro ⟨n, rfl⟩
      have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [hre] at hre0
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h1 : z ≠ 1 := by
      rintro rfl
      simp at hre1
    obtain ⟨hlo, hhi⟩ :=
      nontrivial_zero_strip_of_moebius_summatory_power_bound hr hM hz0 hnt h1
    rw [abs_le]
    constructor <;> linarith
  -- Hence no critical zero is omitted by the window of half-width `α`.
  have hempty : IsEmpty {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|} := by
    refine ⟨fun r => ?_⟩
    have h1 : α ≤ |r.val.val.re - 1/2| := r.2
    have h2 := hstrip r.val.val r.val.2
    linarith
  exact tsum_empty
