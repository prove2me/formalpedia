-- Prove2me | solution 1 for LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:03:55.293175+00:00
-- url     : https://prove2.me/submissions/162f0827-b431-47c9-a2bc-6784c38cad36

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingales on the right-continuation of a filtration

An `ℱ`-martingale on `ℝ` whose time slices are right-continuous in `L¹` is a martingale on
the right-continuation `ℱ₊` of `ℱ`, `ℱ₊ s = ⨅ r > s, ℱ r` (no null sets are added): an
`ℱ₊ s`-measurable set lies in every `ℱ r` with `r > s`, so the martingale identity holds on it
from every later time, and right-`L¹`-continuity carries it down to `s`.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ}



theorem _root_.solution (hmart : Martingale F ℱ P)
    (hrc : ∀ s : ℝ, Tendsto (fun r => eLpNorm (F r - F s) 1 P) (𝓝[>] s) (𝓝 0)) :
    Martingale F ℱ.rightCont P := by
  refine ⟨fun i => (hmart.1 i).mono (ℱ.le_rightCont i), fun s t hst => ?_⟩
  have hFs : StronglyMeasurable[ℱ.rightCont s] (F s) := (hmart.1 s).mono (ℱ.le_rightCont s)
  have hself : P[F s | ℱ.rightCont s] = F s :=
    condExp_of_stronglyMeasurable (ℱ.rightCont.le s) hFs (hmart.integrable s)
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [hself]
  set G := P[F t | ℱ.rightCont s] with hG
  have key : ∀ r, s < r → r ≤ t → eLpNorm (G - F s) 1 P ≤ eLpNorm (F r - F s) 1 P := by
    intro r hsr hrt
    have hle : ℱ.rightCont s ≤ ℱ r := by
      rw [Filtration.rightCont_eq]; exact iInf₂_le r hsr
    have h1 : P[F r | ℱ.rightCont s] =ᵐ[P] G := by
      have a1 : P[F r | ℱ.rightCont s] =ᵐ[P] P[P[F t | ℱ r] | ℱ.rightCont s] :=
        condExp_congr_ae (hmart.2 r t hrt).symm
      exact a1.trans (condExp_condExp_of_le hle (ℱ.le r))
    have h2 : P[F r - F s | ℱ.rightCont s] =ᵐ[P] G - F s := by
      have a2 := condExp_sub (m := ℱ.rightCont s) (hmart.integrable r) (hmart.integrable s)
      rw [hself] at a2
      filter_upwards [a2, h1] with ω h2a h2b
      rw [h2a, Pi.sub_apply, Pi.sub_apply, h2b]
    rw [← eLpNorm_congr_ae h2]
    exact eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hev : ∀ᶠ r in 𝓝[>] s, eLpNorm (G - F s) 1 P ≤ eLpNorm (F r - F s) 1 P := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with r hr
    exact key r hr.1 hr.2.le
  have h0 : eLpNorm (G - F s) 1 P ≤ 0 := ge_of_tendsto (hrc s) hev
  have h00 : eLpNorm (G - F s) 1 P = 0 := le_antisymm h0 zero_le
  have hae : G - F s =ᵐ[P] 0 :=
    (eLpNorm_eq_zero_iff ((stronglyMeasurable_condExp.mono (ℱ.rightCont.le s)).aestronglyMeasurable.sub
      (hmart.integrable s).aestronglyMeasurable) one_ne_zero).1 h00
  filter_upwards [hae] with ω hω
  simpa [sub_eq_zero] using hω
