-- Prove2me | solution 1 for Kyprianou.Ch04.normalizedDeficitMomentCharacterisationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:07:49.29111+00:00
-- url     : https://prove2.me/submissions/aa09ec7c-fe3d-430b-bc86-528fb2cd42d5

import Mathlib
open MeasureTheory Filter
open scoped ENNReal Topology
set_option autoImplicit false
open Set

theorem solution
    (nu : Measure Real) (d : Real) :
    (∫⁻ y : Real, ENNReal.ofReal (-y) ∂nu) ≤ ENNReal.ofReal d ↔
      ∀ a : Real, 0 < a →
        (∫⁻ y : Real, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂nu) ≤
          ENNReal.ofReal d := by
  let D : Real → Real → ENNReal := fun a y => ENNReal.ofReal ((1 - Real.exp (a*y))/a)
  change (∫⁻ y, ENNReal.ofReal (-y) ∂nu) ≤ ENNReal.ofReal d ↔
    ∀ a : Real, 0 < a → (∫⁻ y, D a y ∂nu) ≤ ENNReal.ofReal d
  constructor
  · intro hM a ha
    apply le_trans _ hM
    apply lintegral_mono
    intro y
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ ha).mpr
    linarith [Real.add_one_le_exp (a*y)]
  · intro hbound
    let l : Filter Real := nhdsWithin 0 (Set.Ioi 0)
    have hlim (y : Real) : Tendsto (fun a => D a y) l (𝓝 (ENNReal.ofReal (-y))) := by
      have hder : HasDerivAt (fun a : Real => Real.exp (a*y)) y 0 := by
        simpa [Function.comp_def] using
          (Real.hasDerivAt_exp (0*y)).comp 0 ((hasDerivAt_id 0).mul_const y)
      have ht : Tendsto (fun a : Real => (1 - Real.exp (a*y))/a)
          (𝓝[({0} : Set Real)ᶜ] 0) (𝓝 (-y)) := by
        simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
          (hder.const_sub 1).tendsto_slope_zero
      have hs : l ≤ 𝓝[({0} : Set Real)ᶜ] 0 :=
        nhdsWithin_mono _ (fun a ha => by simpa using (ne_of_gt ha))
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht.mono_left hs)
    have hmeas (a : Real) : Measurable (D a) := by dsimp [D]; fun_prop
    have hf := lintegral_liminf_le (μ := nu) (u := l) hmeas
    have he : (∫⁻ y, ENNReal.ofReal (-y) ∂nu) =
        ∫⁻ y, liminf (fun a => D a y) l ∂nu :=
      lintegral_congr (fun y => (hlim y).liminf_eq.symm)
    rw [he]
    refine hf.trans (liminf_le_of_frequently_le ?_)
    apply Filter.Eventually.frequently
    have hev : ∀ᶠ a in l, 0 < a := eventually_mem_nhdsWithin
    filter_upwards [hev] with a ha
    exact hbound a ha
