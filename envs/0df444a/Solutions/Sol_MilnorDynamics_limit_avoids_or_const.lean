-- Prove2me | solution 1 for MilnorDynamics.limit_avoids_or_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:06:10.068577+00:00
-- url     : https://prove2.me/submissions/0fcb2b5e-456f-48f7-a0d2-44971a9f2c92

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_sphere_ne_zero_of_analytic
import Theorems.Thm_MilnorDynamics_ne_of_sphere_ne_zero_of_tendsto

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Hurwitz's theorem for limits, reduced to its two obligations: a circle on
which the limit is nonzero (isolated zeros), and the minimum-modulus argument
that turns such a circle into the conclusion that the limit avoids `c`. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ) (c : ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({c}ᶜ : Set ℂ))
    (g : ℂ → ℂ) (hg : ContinuousOn g U)
    (hc : TendstoLocallyUniformlyOn f g atTop U) :
    (∀ z ∈ U, g z ≠ c) ∨ (∀ z ∈ U, g z = c) := by
  by_cases hconst : ∀ z ∈ U, g z = c
  · exact Or.inr hconst
  · push_neg at hconst
    obtain ⟨w, hwU, hwc⟩ := hconst
    have hgd : DifferentiableOn ℂ g U :=
      hc.differentiableOn (Eventually.of_forall fun n => (hf n).1) hU
    have hana : AnalyticOnNhd ℂ (fun z => g z - c) U :=
      (hgd.sub (differentiableOn_const c)).analyticOnNhd hU
    refine Or.inl fun z0 hz0 hz0c => ?_
    obtain ⟨r, hr, hball, hcirc⟩ :=
      exists_sphere_ne_zero_of_analytic U hU hUc (fun z => g z - c) hana z0 hz0
        ⟨w, hwU, sub_ne_zero.mpr hwc⟩
    exact ne_of_sphere_ne_zero_of_tendsto U hU f c g hf hc z0 r hr hball hcirc hz0c
