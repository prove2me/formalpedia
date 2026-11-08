-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:48:21.397338+00:00
-- url     : https://prove2.me/submissions/990fecff-ceb5-4606-b0fe-35921173f5f6

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open NahmiasPerishable.Inventory in
theorem solution (a beta Q rate t : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hQ : 0 ≤ Q) (hrate : 0 ≤ rate) (ht : 0 < t ∨ (t = 0 ∧ 1 ≤ beta))
    (hphysical : ∀ u, 0 ≤ u → u ≤ t →
      0 ≤ survivalStock (fun s => Real.exp (-a*s^beta)) Q rate u) :
    HasDerivAt (survivalStock (fun s => Real.exp (-a*s^beta)) Q rate)
      (-rate-a*beta*t^(beta-1)*survivalStock (fun s => Real.exp (-a*s^beta)) Q rate t) t := by
  have hc : Continuous (fun u : ℝ => rate / Real.exp (-a*u^beta)) :=
    continuous_const.div (Real.continuous_exp.comp
      (continuous_const.mul (Real.continuous_rpow_const hbeta.le))) (fun _ => (Real.exp_pos _).ne')
  have hI : HasDerivAt (fun t => ∫ u in (0:ℝ)..t, rate / Real.exp (-a*u^beta))
      (rate / Real.exp (-a*t^beta)) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hp : HasDerivAt (fun s : ℝ => s^beta) (beta * t^(beta-1)) t := by
    apply Real.hasDerivAt_rpow_const
    rcases ht with h | h
    · left; exact h.ne'
    · right; exact h.2
  have hS : HasDerivAt (fun s : ℝ => Real.exp (-a*s^beta))
      (Real.exp (-a*t^beta) * (-a * (beta*t^(beta-1)))) t := (hp.const_mul (-a)).exp
  refine (hS.mul ((hasDerivAt_const t Q).sub hI)).congr_deriv ?_
  simp only [survivalStock, Pi.sub_apply]
  have hE : Real.exp (-a*t^beta) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring
