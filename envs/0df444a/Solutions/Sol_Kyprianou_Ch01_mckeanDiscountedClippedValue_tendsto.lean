-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedClippedValue_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:02:50.741352+00:00
-- url     : https://prove2.me/submissions/8aa1b423-ee3d-43ee-893a-1847792493b8

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_natTendstoZero
import Theorems.Thm_Kyprianou_Ch01_clippedFiniteClockEventuallyEq

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Stopped payoff convergence follows from finite clipping and discount decay. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (tau : Ω → WithTop ℝ≥0)
    (ω : Ω) :
    let barrier := Real.log (K * phi / (1 + phi))
    let clip (n : ℕ) : ℝ≥0 :=
      (min (tau ω) ((n : ℝ≥0) : WithTop ℝ≥0)).untopD (n : ℝ≥0)
    let terminal : ℝ :=
      match tau ω with
      | none => 0
      | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K barrier phi (x + X t ω)
    Filter.Tendsto (fun n : ℕ =>
      Real.exp (-q * (clip n : ℝ)) *
        mckeanValue K barrier phi (x + X (clip n) ω))
      Filter.atTop (nhds terminal) := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  let clip (n : ℕ) : ℝ≥0 :=
    (min (tau ω) ((n : ℝ≥0) : WithTop ℝ≥0)).untopD (n : ℝ≥0)
  change Tendsto (fun n : ℕ =>
    Real.exp (-q * (clip n : ℝ)) *
      mckeanValue K b phi (x + X (clip n) ω))
    atTop (nhds (match tau ω with
      | none => 0
      | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K b phi (x + X t ω)))
  cases ht : tau ω with
  | top =>
      have hc (n : ℕ) : clip n = (n : ℝ≥0) := by
        simp [clip, ht, WithTop.untopD_coe]
      have hlim := Kyprianou.Ch01.mckeanDiscountedValue_natTendstoZero
        X x K q phi hK hq hphi ω
      have hh : Tendsto (fun n : ℕ =>
          Real.exp (-q * (clip n : ℝ)) *
            mckeanValue K b phi (x + X (clip n) ω))
          atTop (nhds 0) := by
        simpa [hc, b] using hlim
      simpa only [ht] using hh
  | coe t =>
      have hevent := Kyprianou.Ch01.clippedFiniteClockEventuallyEq t
      have heq : (fun n : ℕ =>
          Real.exp (-q * (clip n : ℝ)) *
            mckeanValue K b phi (x + X (clip n) ω)) =ᶠ[atTop]
          (fun _ : ℕ =>
            Real.exp (-q * (t : ℝ)) *
              mckeanValue K b phi (x + X t ω)) := by
        filter_upwards [hevent] with n hn
        have hc : clip n = t := by
          simpa only [clip, ht] using hn
        simp only [hc]
      have hh : Tendsto (fun n : ℕ =>
          Real.exp (-q * (clip n : ℝ)) *
            mckeanValue K b phi (x + X (clip n) ω))
          atTop (nhds (Real.exp (-q * (t : ℝ)) *
            mckeanValue K b phi (x + X t ω))) :=
        Filter.Tendsto.congr' heq.symm tendsto_const_nhds
      simpa only [ht] using hh
