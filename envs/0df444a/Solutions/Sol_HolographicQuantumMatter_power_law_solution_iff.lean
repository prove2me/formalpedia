-- Prove2me | solution 1 for HolographicQuantumMatter.power_law_solution_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:25:34.108986+00:00
-- url     : https://prove2.me/submissions/017c9ffa-07d9-4540-ab20-dc7e4f170a61

import Definitions.Def_HolographicQuantumMatter_ScalarAdS
import Mathlib.Tactic
open HolographicQuantumMatter

private theorem radial_power (d : ℕ) (msq L p r : ℝ) (hr : 0 < r) :
    radialOperator d 0 0 msq L (fun r => r^p) r =
      (p*(p-((d : ℝ)+1))-msq*L^2)*r^p/r^2 := by
  have hd : deriv (deriv (fun r : ℝ => r^p)) r = p*((p-1)*r^(p-1-1)) := by
    rw [Real.deriv_rpow_const']
    exact ((Real.hasDerivAt_rpow_const (Or.inl hr.ne') :
      HasDerivAt (fun r : ℝ => r^(p-1)) ((p-1)*r^(p-1-1)) r).const_mul p).deriv
  unfold radialOperator
  rw [hd,Real.deriv_rpow_const,Real.rpow_sub_one hr.ne',Real.rpow_sub_one hr.ne']
  field_simp
  <;> ring

theorem solution (d : ℕ) (msq L : ℝ) (hL : 0 < L) (p : ℝ) :
    IsRadialSolution d 0 0 msq L (fun r => r^p) ↔
      p*(p-((d : ℝ)+1))=msq*L^2 := by
  constructor
  · intro h
    have hh := h.2 1 (by norm_num)
    rw [radial_power d msq L p 1 (by norm_num)] at hh
    simpa only [Real.one_rpow,one_pow,mul_one,div_one,sub_eq_zero] using hh
  · intro h
    refine ⟨?_,?_⟩
    · intro r hr
      exact (Real.contDiffAt_rpow_const_of_ne hr.ne').contDiffWithinAt
    · intro r hr
      rw [radial_power d msq L p r hr,h]
      simp

