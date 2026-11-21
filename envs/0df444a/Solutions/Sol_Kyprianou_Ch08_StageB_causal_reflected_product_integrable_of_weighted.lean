-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.causal_reflected_product_integrable_of_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:21:41.366676+00:00
-- url     : https://prove2.me/submissions/36a4b767-1220-426b-8f77-959a83725732

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_integrableOn_reflect_Ioc_of_halfline
set_option autoImplicit false

open MeasureTheory Set

theorem solution (f g : ℝ → ℝ) (β x : ℝ) (hx : 0 ≤ x)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-(β * t)) * f t)
      (Set.Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ))) :
    IntegrableOn (fun s : ℝ => g s * f (x - s))
      (Set.Ioc (0 : ℝ) x) volume := by
  have href : IntegrableOn
      (fun s : ℝ => Real.exp (-(β * (x - s))) * f (x - s))
      (Set.Ioc (0 : ℝ) x) volume := by
    exact Kyprianou.Ch08.StageB.integrableOn_reflect_Ioc_of_halfline
      (fun t : ℝ => Real.exp (-(β * t)) * f t) x hx hf
  have hInt : IntervalIntegrable
      (fun s : ℝ => Real.exp (-(β * (x - s))) * f (x - s))
      volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 href
  have hg' : ContinuousOn g (Set.Icc (0 : ℝ) x) :=
    hg.mono (by intro s hs; exact hs.1)
  have hcont : ContinuousOn
      (fun s : ℝ => g s * Real.exp (β * (x - s)))
      (Set.Icc (0 : ℝ) x) :=
    hg'.mul ((Real.continuous_exp.comp ((continuous_const.sub continuous_id).const_mul β)).continuousOn)
  have hprod : IntervalIntegrable
      (fun s : ℝ => (Real.exp (-(β * (x - s))) * f (x - s)) *
        (g s * Real.exp (β * (x - s)))) volume 0 x := by
    exact hInt.mul_continuousOn (by simpa [Set.uIcc_of_le hx] using hcont)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1
  convert hprod using 1
  ext s
  have he : Real.exp (-(β * (x - s))) * Real.exp (β * (x - s)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    g s * f (x - s) =
        (Real.exp (-(β * (x - s))) * Real.exp (β * (x - s))) *
          (g s * f (x - s)) := by rw [he]; ring
    _ = (Real.exp (-(β * (x - s))) * f (x - s)) *
          (g s * Real.exp (β * (x - s))) := by ring
