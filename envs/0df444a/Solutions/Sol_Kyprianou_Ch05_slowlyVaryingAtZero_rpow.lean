-- Prove2me | solution 1 for Kyprianou.Ch05.slowlyVaryingAtZero_rpow
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T05:47:47.380628+00:00
-- url     : https://prove2.me/submissions/5b2287aa-2c03-4d45-aea9-206d5ba95e67

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_slowlyVaryingAtInfinity_rpow
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- H1-zero: the slowly-varying power bound at zero, by reduction to H1
applied to L'(x) = L(1/x), using the second (diverging) conclusion of H1
composed with s = 1/x. -/
theorem solution
    (L : Real → Real)
    (hpos : ∀ x : Real, 0 < x → 0 < L x)
    (hslow : ∀ a : Real, 0 < a →
      Tendsto (fun x : Real => L (a * x) / L x)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1))
    (hcont : ContinuousOn L (Set.Ioi (0 : Real))) :
    ∀ eps : Real, 0 < eps →
      Tendsto (fun x : Real => L x / x ^ eps)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop := by
  intro eps heps
  set L' : Real → Real := fun x => L (1 / x) with hL'
  have hpos' : ∀ x : Real, 0 < x → 0 < L' x := by
    intro x hx
    simp only [hL']
    exact hpos _ (one_div_pos.mpr hx)
  have hslow' : ∀ a : Real, 0 < a →
      Tendsto (fun x : Real => L' (a * x) / L' x) atTop (nhds 1) := by
    intro a ha
    have h := hslow (1 / a) (one_div_pos.mpr ha)
    have hcomp : Tendsto (fun x : Real => (1 : Real) / x) atTop
        (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
      simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero
    have h2 := h.comp hcomp
    apply h2.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hx0 : x ≠ 0 := ne_of_gt hx
    simp only [hL', Function.comp_def]
    have h1 : (1 : Real) / a * (1 / x) = 1 / (a * x) := by field_simp
    rw [h1]
  have hcont' : ContinuousOn L' (Set.Ioi (0 : Real)) := by
    have hinv : ContinuousOn (fun x : Real => (1 : Real) / x) (Set.Ioi (0 : Real)) := by
      have h : ContinuousOn (fun x : Real => x⁻¹) (Set.Ioi (0 : Real)) :=
        continuousOn_id.inv₀ (fun x hx => ne_of_gt hx)
      simpa only [one_div] using h
    simp only [hL']
    show ContinuousOn (L ∘ fun x : Real => (1 : Real) / x) (Set.Ioi (0 : Real))
    exact ContinuousOn.comp hcont hinv
      (fun x hx => Set.mem_Ioi.mpr (one_div_pos.mpr (Set.mem_Ioi.mp hx)))
  have hH1 := (slowlyVaryingAtInfinity_rpow L' hpos' hslow' hcont' eps heps).2
  have hcomp : Tendsto (fun s : Real => (1 : Real) / s)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  have h3 := hH1.comp hcomp
  apply h3.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [hL', Function.comp_def]
  rw [one_div_one_div, Real.div_rpow zero_le_one hs.le, Real.one_rpow, one_div,
    div_eq_mul_inv]
