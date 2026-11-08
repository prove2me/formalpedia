-- Prove2me | solution 1 for OAI.SharpPlanar.disk_frequency_distance_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:16:43.706059+00:00
-- url     : https://prove2.me/submissions/c3126cf7-640f-4853-b2a9-dd783e7ab914

import Mathlib
import Definitions.Def_OAIQ098G072

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open MeasureTheory Set


lemma disk_frequency_distance_g_oai {j : ℕ} (hj : j < 6) {l : ℕ}
    (hl : l ∈ Finset.Icc (j+1) 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖(l:ℂ)/6-t‖ ≤ 13/12 := by
  have hjr : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
  have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg l
  have hl1 : (l:ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hl).2
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hh : ‖(l:ℂ)/6-(diskCenter j:ℂ)‖ ≤ 11/12 := by
    rw [show (l:ℂ)/6-(diskCenter j:ℂ) = (((l:ℝ)/6-diskCenter j:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
    unfold diskCenter
    constructor <;> linarith
  have hn := norm_sub_le ((l:ℂ)/6-(diskCenter j:ℂ)) (t-(diskCenter j:ℂ))
  rw [sub_sub_sub_cancel_right] at hn
  linarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_frequency_distance_g_oai := @OAI.SharpPlanar.disk_frequency_distance_g_oai
