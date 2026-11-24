-- Prove2me | solution 1 for GlobalTheory.LogExt.isLittleO_inv_of_log_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:51:57.769349+00:00
-- url     : https://prove2.me/submissions/194a7534-ef2c-46e9-abff-faacceae0d6b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
namespace GlobalTheory.LogExt
theorem _root_.solution {f g : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c)
    (hne : ¬ ∀ᶠ z in 𝓝 c, g z = 0) {C : ℝ} {k : ℕ}
    (hb : ∀ᶠ z in 𝓝 c, g z ≠ 0 → ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k) :
    (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
  obtain ⟨m, h, hh, hh0, hgh⟩ := hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hT : Tendsto (fun z : ℂ => ‖z - c‖) (𝓝[≠] c) (𝓝[>] 0) := tendsto_norm_sub_self_nhdsNE c
  have hlog : Tendsto (fun z : ℂ => |Real.log ‖z - c‖|) (𝓝[≠] c) atTop :=
    tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hT)
  have hhc : ContinuousAt (fun z => |Real.log ‖h z‖|) c :=
    (hh.continuousAt.norm.log (norm_ne_zero_iff.mpr hh0)).abs
  have hhb : ∀ᶠ z in 𝓝 c, |Real.log ‖h z‖| < |Real.log ‖h c‖| + 1 :=
    hhc.eventually (gt_mem_nhds (lt_add_one _))
  have hhne : ∀ᶠ z in 𝓝 c, h z ≠ 0 := hh.continuousAt.eventually_ne hh0
  have h1 : f =O[𝓝[≠] c] fun z => |Real.log ‖z - c‖| ^ k := by
    refine IsBigO.of_bound (|C| * (1 + m) ^ k) ?_
    filter_upwards [nhdsWithin_le_nhds hb, nhdsWithin_le_nhds hgh, nhdsWithin_le_nhds hhb,
      nhdsWithin_le_nhds hhne, self_mem_nhdsWithin,
      hlog.eventually (eventually_ge_atTop (|Real.log ‖h c‖| + 2))] with z hz1 hz2 hz3 hz4 hz5 hz6
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz5
    have hgz : g z ≠ 0 := by
      rw [hz2]; exact smul_ne_zero (pow_ne_zero _ hzc) hz4
    have hl : Real.log ‖g z‖ = m * Real.log ‖z - c‖ + Real.log ‖h z‖ := by
      rw [hz2, smul_eq_mul, norm_mul, norm_pow,
        Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hzc)) (norm_ne_zero_iff.mpr hz4),
        Real.log_pow]
    have hle : 1 + |Real.log ‖g z‖| ≤ (1 + m) * |Real.log ‖z - c‖| := by
      rw [hl]
      have := abs_add_le (m * Real.log ‖z - c‖) (Real.log ‖h z‖)
      rw [abs_mul, Nat.abs_cast] at this
      nlinarith
    calc ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k := hz1 hgz
      _ ≤ |C| * (1 + |Real.log ‖g z‖|) ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + m) * |Real.log ‖z - c‖|) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle k) (abs_nonneg C)
      _ = |C| * (1 + m) ^ k * ‖|Real.log ‖z - c‖| ^ k‖ := by
          rw [mul_pow, Real.norm_eq_abs, abs_pow, abs_abs]; ring
  have h2 : (fun z : ℂ => |Real.log ‖z - c‖| ^ k) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
    have := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ) (s := -1) (by norm_num)).comp_tendsto hT
    refine IsLittleO.of_norm_right ?_
    refine this.congr (fun z => ?_) (fun z => ?_)
    · simp
    · simp [Real.rpow_neg_one]
  have h3 : (fun _ : ℂ => f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
    refine isLittleO_const_left.mpr (Or.inr ?_)
    have := tendsto_inv_nhdsGT_zero.comp hT
    refine this.congr fun z => ?_
    simp
  exact (h1.trans_isLittleO h2).sub h3
end GlobalTheory.LogExt
