-- Prove2me | solution 1 for OAI.ShortEgyptian.phase_increment_inv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:06:03.471621+00:00
-- url     : https://prove2.me/submissions/0e625a8b-1257-4093-875c-c3c478aa95ff

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/FirstDerivative.lean:L60-L86
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.phase_increment_inv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative

-- ---- from OAI.NumberTheory.ShortEgyptian.FirstDerivative ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem phase_increment_inv {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (phase x - 1)⁻¹ = (-1 / 2 : ℂ) -
      (↑(Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x))) : ℂ) * Complex.I := by
  have hs : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  let b : ℂ := (-1 / 2 : ℂ) -
    (↑(Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x))) : ℂ) * Complex.I
  have hmul : b * (phase x - 1) = 1 := by
    apply Complex.ext <;> simp only [b, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.div_re, Complex.div_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, phase_re, phase_im]
    all_goals
      norm_num
      rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
        Real.sin_two_mul, Real.cos_two_mul]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x),
        congrArg (fun t : ℝ => Real.cos (Real.pi * x) * t)
          (Real.sin_sq_add_cos_sq (Real.pi * x))]
  have hne : phase x - 1 ≠ 0 := by
    intro hh
    rw [hh, mul_zero] at hmul
    exact zero_ne_one hmul
  change (phase x - 1)⁻¹ = b
  rw [← one_div]
  exact (div_eq_iff hne).mpr hmul.symm

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.phase_increment_inv := @_root_.OAI.ShortEgyptian.phase_increment_inv
