-- Prove2me | solution 1 for MasulloRH.unit_gaussian_theta_mellin_vertical_shift_separation
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:29:44.846316+00:00
-- url     : https://prove2.me/submissions/3ec5c1b6-effd-4949-ba8a-6da20303dd62

import Theorems.Thm_MasulloRH_entire_theta_mellin_multiplier
import Theorems.Thm_MasulloRH_theta_mellin_zeros_on_line_one
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MasulloRH.RationalThetaGrid Set Filter
open scoped Topology

private lemma phase_add (u t : ℝ) : phase (u+t) = phase u * phase t := by
  unfold phase vertical
  rw [← Complex.exp_add,Complex.ofReal_add]
  ring_nf

private lemma period_phase : phase (2*Real.pi/Real.log 2) = 1 := by
  have hL : ((Real.log 2 : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  unfold phase vertical logTwo
  push_cast
  rw [show -((Real.log 2:ℝ):ℂ) * (2 * (Real.pi:ℂ) / ((Real.log 2:ℝ):ℂ) * Complex.I) =
        -(2 * (Real.pi:ℂ) * Complex.I) by field_simp,
      Complex.exp_neg,Complex.exp_two_pi_mul_I,inv_one]

theorem solution (c b t : ℝ) (hb : 0 < b) (ht : 0 < t) (z : ℂ) (hz : z ≠ 0) :
    ∃ s : ℂ, |s.re-c| < b ∧ defect s t z ≠ 0 := by
  by_contra! h
  have hd := MasulloRH.entire_theta_mellin_multiplier.1
  have ha : Differentiable ℂ (fun s => defect s t z) := by
    unfold defect gaussian
    fun_prop
  have ho : IsOpen {s : ℂ | |s.re-c| < b} :=
    isOpen_lt ((Complex.continuous_re.sub (continuous_const (y:=c))).abs) continuous_const
  have hh : (fun s : ℂ => defect s t z) =ᶠ[𝓝 (c:ℂ)] (fun _ => 0) := by
    have hx : (c:ℂ) ∈ {s : ℂ | |s.re-c| < b} := by change |(c:ℂ).re-c| < b;simpa using hb
    filter_upwards [ho.mem_nhds hx] with w hw
    exact h w hw
  have ident := AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => ha.analyticAt w) analyticOnNhd_const hh
  have zeros (s : ℂ) : thetaMultiplier (s+vertical t) = 0 ↔ thetaMultiplier s = 0 := by
    have e := sub_eq_zero.mp (congrFun ident s : defect s t z = 0)
    constructor
    · intro he
      rw [he,mul_zero,zero_mul] at e
      exact (mul_eq_zero.mp e).resolve_right (Complex.exp_ne_zero _)
    · intro he
      rw [he,zero_mul] at e
      exact (mul_eq_zero.mp ((mul_eq_zero.mp e.symm).resolve_right (Complex.exp_ne_zero _))).resolve_left hz
  have one : thetaMultiplier 1 ≠ 0 := by
    rw [MasulloRH.entire_theta_mellin_multiplier.2.2]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne') (by norm_num)
  have hnot : phase t ≠ 1 := fun e =>
    one ((zeros 1).mp ((MasulloRH.theta_mellin_zeros_on_line_one t).2 ⟨ht.ne',e⟩))
  let u := 2*Real.pi/Real.log 2
  have hu : 0 < u := div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos (by norm_num))
  have hzero := (MasulloRH.theta_mellin_zeros_on_line_one u).2 ⟨hu.ne',period_phase⟩
  have hpt : point u + vertical t = point (u+t) := by
    unfold point vertical
    push_cast
    ring
  have hnext := (zeros (point u)).mpr hzero
  rw [hpt] at hnext
  have hp := ((MasulloRH.theta_mellin_zeros_on_line_one (u+t)).1 hnext).2
  rw [phase_add,show phase u = 1 from period_phase,one_mul] at hp
  exact hnot hp
