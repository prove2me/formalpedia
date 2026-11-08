-- Prove2me | solution 1 for OAI.SharpPlanar.disk_z_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:18:36.994563+00:00
-- url     : https://prove2.me/submissions/b3a01e56-b186-4a16-986f-84ab732c332c

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_disk_denominator_lower_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g

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

theorem B_pos : 0 < B := by norm_num [B]

end SharpPlanar

namespace SharpPlanar
open Complex

lemma disk_z_bound_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖complexZ t‖ < 31/5 := by
  have hd := disk_denominator_lower_g hj ht
  have hm := norm_sub_le (-(B:ℂ)/(t+Complex.I*(h:ℂ))) (Complex.I*(h:ℂ))
  simp only [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,norm_mul,
    Complex.norm_I,one_mul,abs_of_pos B_pos,abs_of_pos h_pos_g] at hm
  have hb : B/‖t+Complex.I*(h:ℂ)‖ ≤ (40:ℝ)/7 := by
    apply (div_le_iff₀ (by linarith : 0 < ‖t+Complex.I*(h:ℂ)‖)).mpr
    norm_num [B]
    linarith
  change ‖-(B:ℂ)/(t+Complex.I*(h:ℂ))-Complex.I*(h:ℂ)‖ < _
  norm_num [h] at hm hb ⊢
  linarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_z_bound_g_oai := @OAI.SharpPlanar.disk_z_bound_g_oai
