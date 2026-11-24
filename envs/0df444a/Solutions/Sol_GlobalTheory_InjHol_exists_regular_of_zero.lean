-- Prove2me | solution 1 for GlobalTheory.InjHol.exists_regular_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:48.678597+00:00
-- url     : https://prove2.me/submissions/a4355c6a-f98a-4faf-be4c-a19f1187ab42

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {h : E → ℂ} {a : E} (hh : AnalyticAt ℂ h a) (ha : h a = 0) (hne : ¬ ∀ᶠ z in 𝓝 a, h z = 0)
    {W : Set E} (hW : W ∈ 𝓝 a) :
    ∃ b ∈ W, h b = 0 ∧ AnalyticAt ℂ h b ∧ ∃ g : E → ℂ, AnalyticAt ℂ g b ∧ fderiv ℂ g b ≠ 0 ∧
      ∀ᶠ z in 𝓝 b, h z = 0 → g z = 0 := by
  classical
  obtain ⟨U, hU, hUo, haU⟩ := _root_.eventually_nhds_iff.mp (hh.eventually_analyticAt.and hW)
  have hUa : AnalyticOnNhd ℂ h U := fun z hz => (hU z hz).1
  have hex : ∃ k, ∃ z ∈ U, h z = 0 ∧ iteratedFDeriv ℂ k h z ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨p, r, hp⟩ := hh
    apply hne
    filter_upwards [eball_mem_nhds a hp.r_pos] with z hz
    have hz' : z - a ∈ Metric.eball (0 : E) r := by
      simpa [Metric.mem_eball, edist_eq_enorm_sub] using hz
    have := hp.hasSum_iteratedFDeriv hz'
    simp only [hc _ a haU ha, ContinuousMultilinearMap.zero_apply, smul_zero,
      add_sub_cancel] at this
    exact this.unique hasSum_zero
  obtain ⟨b, hbU, hb, hk⟩ := Nat.find_spec hex
  have hmin := fun j => Nat.find_min hex (m := j)
  generalize Nat.find hex = k at hk hmin
  cases k with
  | zero => exact absurd (by ext; simp [hb]) hk
  | succ j =>
    obtain ⟨m, hm⟩ : ∃ m, iteratedFDeriv ℂ (j + 1) h b m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hk (ContinuousMultilinearMap.ext hc)
    let A := ContinuousMultilinearMap.apply ℂ (fun _ : Fin j => E) ℂ (Fin.tail m)
    have hj := hUa.iteratedFDeriv j b hbU
    refine ⟨b, (hU b hbU).2, hb, hUa b hbU, fun z => A (iteratedFDeriv ℂ j h z),
      (A.analyticAt _).comp hj, fun h0 => hm ?_, ?_⟩
    · have := (A.hasFDerivAt.comp b hj.differentiableAt.hasFDerivAt).fderiv
      have h2 : A.comp (fderiv ℂ (iteratedFDeriv ℂ j h) b) = 0 := this.symm.trans h0
      rw [iteratedFDeriv_succ_apply_left]
      exact congrArg (fun T => T (m 0)) h2
    · filter_upwards [hUo.mem_nhds hbU] with z hz hz0
      have := hmin j (Nat.lt_succ_self j)
      push Not at this
      simp [this z hz hz0]
end GlobalTheory.InjHol
