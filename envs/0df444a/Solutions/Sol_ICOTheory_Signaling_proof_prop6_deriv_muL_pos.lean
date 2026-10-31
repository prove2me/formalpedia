-- Prove2me | solution 1 for ICOTheory.Signaling.proof_prop6_deriv_muL_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:06:48.490444+00:00
-- url     : https://prove2.me/submissions/daa7a3c5-16b1-4a68-bef7-98b3b23b0f13

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar
open ICOTheory.Signaling

theorem solution{μH μL σ γ : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ) :
    0 < deriv (fun x => alphaStar μH x σ γ) μL := by
  have hA : 0 < 4 * μH - 4 * μL := by linarith
  have hx : 0 < σ ^ 2 * γ := by positivity
  have hin : 0 < (4 * μH - 4 * μL) * (4 * μH - 4 * μL + 2 * σ ^ 2 * γ) :=
    mul_pos hA (by linarith)
  have hlin : HasDerivAt (fun x : ℝ => 4 * μH - 4 * x) (-4) μL := by
    simpa using ((hasDerivAt_id μL).const_mul 4).const_sub (4 * μH)
  have hg := hlin.mul (hlin.add_const (2 * σ ^ 2 * γ))
  have hsq := hg.sqrt hin.ne'
  have hN := ((hlin.add_const (σ ^ 2 * γ)).sub hsq).div_const (σ ^ 2 * γ)
  have hf : HasDerivAt (fun x => alphaStar μH x σ γ) _ μL := hN
  rw [hf.deriv]
  simp only [Pi.mul_apply]
  set S := Real.sqrt ((4 * μH - 4 * μL) * (4 * μH - 4 * μL + 2 * σ ^ 2 * γ)) with hSdef
  have hS : 0 < S := Real.sqrt_pos.mpr hin
  have hS2 : S ^ 2 = (4 * μH - 4 * μL) * (4 * μH - 4 * μL + 2 * σ ^ 2 * γ) :=
    Real.sq_sqrt hin.le
  have key : S < 4 * μH - 4 * μL + σ ^ 2 * γ := by nlinarith
  apply div_pos _ hx
  rw [sub_pos, div_lt_iff₀ (by positivity)]
  nlinarith [key]
