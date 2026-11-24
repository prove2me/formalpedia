-- Prove2me | solution 1 for GlobalTheory.InjHol.deriv_ne_zero_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:42.612939+00:00
-- url     : https://prove2.me/submissions/ccd795a6-989b-49e4-a340-937a39b50b5c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_InjHol_exists_zero_of_norm_lt
import Theorems.Thm_GlobalTheory_InjHol_not_injOn_of_fderiv_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) {s : Set ℂ}
    (hs : s ∈ 𝓝 a) (hinj : InjOn f s) : deriv f a ≠ 0 := by
  intro h0
  obtain ⟨r, hr, hb⟩ := nhds_basis_closedBall.eventually_iff.mp (hf.eventually_analyticAt.and hs)
  have hd : DifferentiableOn ℂ f (closedBall a r) := fun x hx =>
    (hb hx).1.differentiableAt.differentiableWithinAt
  have hsym : ∀ w, dslope f w a = dslope f a w := by
    intro w
    by_cases hw : w = a
    · rw [hw]
    · rw [dslope_of_ne _ hw, dslope_of_ne _ (Ne.symm hw), slope_comm]
  have h1 : ∀ᶠ w in 𝓝 a, ∀ z ∈ sphere a r, ‖dslope f w a‖ < ‖dslope f w z‖ := by
    refine (isCompact_sphere a r).eventually_forall_of_forall_eventually fun z hz => ?_
    have hza : z ≠ a := ne_of_mem_sphere hz hr.ne'
    have hzc := (hb (sphere_subset_closedBall hz))
    have c1 : ContinuousAt (fun p : ℂ × ℂ => ‖dslope f a p.1‖) (a, z) :=
      (ContinuousAt.comp (f := Prod.fst) (x := (a, z))
        (continuousAt_dslope_same.mpr hf.differentiableAt) continuousAt_fst).norm
    have c2 : ContinuousAt (fun p : ℂ × ℂ => ‖(p.2 - p.1)⁻¹ * (f p.2 - f p.1)‖) (a, z) := by
      refine ContinuousAt.norm (ContinuousAt.mul (ContinuousAt.inv₀ (by fun_prop)
        (sub_ne_zero.mpr hza)) (ContinuousAt.sub ?_ ?_))
      · exact ContinuousAt.comp (f := Prod.snd) (x := (a, z)) hzc.1.continuousAt continuousAt_snd
      · exact ContinuousAt.comp (f := Prod.fst) (x := (a, z)) hf.continuousAt continuousAt_fst
    have hlt : ‖dslope f a a‖ < ‖(z - a)⁻¹ * (f z - f a)‖ := by
      rw [dslope_same, h0, norm_zero, norm_pos_iff]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hza))
        (sub_ne_zero.mpr fun h => hza (hinj hzc.2 (mem_of_mem_nhds hs) h))
    have hne : ∀ᶠ p : ℂ × ℂ in 𝓝 (a, z), p.2 ≠ p.1 :=
      (isOpen_ne_fun continuous_snd continuous_fst).mem_nhds hza
    filter_upwards [c1.eventually_lt c2 hlt, hne] with p hp hp'
    rw [hsym, dslope_of_ne _ hp', slope_def_module, smul_eq_mul]
    exact hp
  have h2 : ∀ᶠ w in 𝓝 a, fderiv ℂ f w = 0 := by
    filter_upwards [h1, ball_mem_nhds a hr] with w hw hwb
    obtain ⟨z, hz, hz0⟩ := exists_zero_of_norm_lt hr
      ((Complex.differentiableOn_dslope (mem_of_superset (isOpen_ball.mem_nhds hwb)
        ball_subset_closedBall)).mpr hd) hw
    by_cases hzw : z = w
    · rw [hzw, dslope_same] at hz0
      ext
      simpa using hz0
    · rw [dslope_of_ne _ hzw, slope_def_module, smul_eq_zero] at hz0
      rcases hz0 with h | h
      · exact absurd (sub_eq_zero.mp (inv_eq_zero.mp h)) hzw
      · exact absurd (hinj (hb hz).2 (hb (ball_subset_closedBall hwb)).2 (sub_eq_zero.mp h)) hzw
  exact not_injOn_of_fderiv_eq_zero hf h2 hs hinj
end GlobalTheory.InjHol
