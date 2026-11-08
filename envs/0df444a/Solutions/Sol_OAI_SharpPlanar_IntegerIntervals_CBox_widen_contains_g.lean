-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:19:35.949234+00:00
-- url     : https://prove2.me/submissions/4fd68702-a316-44d5-94f0-d4c760e0b638

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

lemma CBox.widen_contains_g_oai {a c : CBox} {z w : ℂ} {n : ℤ} (hz : a.Contains z)
    (herr : (precision:ℝ)*‖w-z‖ ≤ (n:ℝ)) (hc : a.WidenCheck c n) : c.Contains w := by
  have hr : (precision:ℝ)*|(w-z).re| ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (w-z)) precision_pos_g.le).trans herr
  have hi : (precision:ℝ)*|(w-z).im| ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm (w-z)) precision_pos_g.le).trans herr
  have hra : |(precision:ℝ)*(w-z).re| ≤ (n:ℝ) := by simpa [abs_mul,abs_of_pos precision_pos_g] using hr
  have hia : |(precision:ℝ)*(w-z).im| ≤ (n:ℝ) := by simpa [abs_mul,abs_of_pos precision_pos_g] using hi
  rcases abs_le.mp hra with ⟨hrl,hru⟩
  rcases abs_le.mp hia with ⟨hil,hiu⟩
  have h₁ : (c.re.lo:ℝ) ≤ (a.re.lo:ℝ)-n := by exact_mod_cast hc.1
  have h₂ : (a.re.hi:ℝ)+n ≤ (c.re.hi:ℝ) := by exact_mod_cast hc.2.1
  have h₃ : (c.im.lo:ℝ) ≤ (a.im.lo:ℝ)-n := by exact_mod_cast hc.2.2.1
  have h₄ : (a.im.hi:ℝ)+n ≤ (c.im.hi:ℝ) := by exact_mod_cast hc.2.2.2
  simp only [Complex.sub_re] at hrl hru
  simp only [Complex.sub_im] at hil hiu
  exact ⟨⟨by nlinarith only [hz.1.1,hrl,h₁],by nlinarith only [hz.1.2,hru,h₂]⟩,
    ⟨by nlinarith only [hz.2.1,hil,h₃],by nlinarith only [hz.2.2,hiu,h₄]⟩⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.widen_contains_g_oai
