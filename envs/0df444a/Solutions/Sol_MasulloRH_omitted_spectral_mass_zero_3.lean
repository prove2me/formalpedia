-- Prove2me | solution 3 for MasulloRH.omitted_spectral_mass_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:16:44.988941+00:00
-- url     : https://prove2.me/submissions/57ffd169-3bc3-402f-a7c9-d1551defd5b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

open Set MeasureTheory

namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∑' ρ : {z : {w : ℂ // ConnesRZ.IsCriticalZero w} // ¬ |z.val.re - 1/2| < α},
      (ConnesRZ.zeroMult ρ.val.val : ℂ) * mellin φ (ρ.val.val - 1/2) = 0 :=
  by
    have hstrip : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
    have hempty :
        IsEmpty {z : {w : ℂ // ConnesRZ.IsCriticalZero w} // ¬ |z.val.re - 1/2| < α} := by
      refine ⟨fun ρ => ρ.2 ?_⟩
      obtain ⟨hzero, hpos, hlt⟩ := ρ.val.2
      rw [hstrip _ hzero hpos hlt, sub_self, abs_zero]
      exact hα
    exact tsum_empty
