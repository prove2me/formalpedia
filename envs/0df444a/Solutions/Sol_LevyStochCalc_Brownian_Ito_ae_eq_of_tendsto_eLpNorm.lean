-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:00.960256+00:00
-- url     : https://prove2.me/submissions/55ef47a3-a4e8-4d52-9005-62fdad993af3

import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral in the driver

The elementary integral of a simple integrand against a linear combination of Brownian motions is
the corresponding combination of the elementary integrals, and both sides of the resulting
identity are `L²`-limits along the same approximating sequence, so the identity passes to the
`L²` Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}


omit [IsProbabilityMeasure P] in

theorem _root_.solution {f g : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) P)
    (hfm : AEStronglyMeasurable f P) (hgm : AEStronglyMeasurable g P)
    (hFf : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - f ω) 2 P) Filter.atTop (nhds 0))
    (hFg : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - g ω) 2 P) Filter.atTop (nhds 0)) :
    f =ᵐ[P] g := by
  have hle (n : ℕ) : eLpNorm (f - g) 2 P ≤
      eLpNorm (fun ω => F n ω - f ω) 2 P + eLpNorm (fun ω => F n ω - g ω) 2 P := by
    have heq : f - g = (f - F n) + (F n - g) := by
      ext ω
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    have h := eLpNorm_add_le (hfm.sub (hFm n)) ((hFm n).sub hgm) (p := 2) (by norm_num)
    rw [eLpNorm_sub_comm f (F n), ← heq] at h
    exact h
  have ht := hFf.add hFg
  rw [add_zero] at ht
  have hz : eLpNorm (f - g) 2 P = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds ht hle) bot_le
  have h := (eLpNorm_eq_zero_iff (hfm.sub hgm) (by norm_num)).mp hz
  filter_upwards [h] with ω hω
  exact sub_eq_zero.mp hω
