-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/766010c5-5d2a-5ca8-bdac-c6181f7f90aa

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

open LanglandsTunnell in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ)
    (w : InfinitePlace K) (u : ℂ) (a : ℤ) (h : IsArchCompAt K μ w u a) :
    u.re = 0 := by

  have hiso : Isometry (NumberField.InfinitePlace.Completion.extensionEmbedding w) :=
    NumberField.InfinitePlace.Completion.isometry_extensionEmbedding (v := w)
  have hnorm : ∀ z : w.Completion, ‖NumberField.InfinitePlace.Completion.extensionEmbedding w z‖ = ‖z‖ := by
    intro z
    have hd := hiso.dist_eq z 0
    rwa [map_zero, dist_zero_right, dist_zero_right] at hd
  have h2e : NumberField.InfinitePlace.Completion.extensionEmbedding w (2 : w.Completion) = (2 : ℂ) := map_ofNat _ 2
  have h2norm : ‖(2 : w.Completion)‖ = 2 := by
    rw [← hnorm, h2e]
    norm_num
  have h2ne : (2 : w.Completion) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h2norm
    norm_num at h2norm
  set x₀ : (w.Completion)ˣ := Units.mk0 (2 : w.Completion) h2ne with hx₀
  have hx₀val : ((x₀ : (w.Completion)ˣ) : w.Completion) = (2 : w.Completion) := by simp [hx₀]

  have hunit : ‖((NumberField.TateGlobal.archLocalChar μ w x₀ : ℂˣ) : ℂ)‖ = 1 :=
    hμ (NumberField.TateGlobal.archUnitHom w x₀)
  rw [h x₀, hx₀val, h2norm] at hunit

  have hq :
      ‖(NumberField.InfinitePlace.Completion.extensionEmbedding w (2 : w.Completion) / ((2 : ℝ) : ℂ)) ^ a‖ = 1 := by
    rw [norm_zpow, norm_div, hnorm, h2norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), div_self (by norm_num : (2 : ℝ) ≠ 0), one_zpow]
  rw [norm_mul, hq, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)] at hunit

  have ht : ((w.mult : ℂ) * u).re = 0 := by
    have hlog := congrArg Real.log hunit
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_one] at hlog
    rcases mul_eq_zero.mp hlog with h0 | h0
    · exact h0
    · exact absurd h0 (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hmul : (w.mult : ℝ) * u.re = 0 := by simpa [Complex.mul_re] using ht
  rcases mul_eq_zero.mp hmul with h0 | h0
  · exact absurd h0 NumberField.InfinitePlace.mult_coe_ne_zero
  · exact h0

end S_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar (solution)
