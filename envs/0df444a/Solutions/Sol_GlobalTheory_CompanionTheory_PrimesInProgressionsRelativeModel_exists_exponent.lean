-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.exists_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:35:11.655353+00:00
-- url     : https://prove2.me/submissions/4f57a441-0613-4a37-8586-dcf0b42b8ec2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_InvLogIntervalIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
namespace GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
theorem _root_.solution {C c : ℝ} (C₀ : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, C₀ ≤ L ∧ 2 ≤ L ∧ C * Real.exp (-(c * L)) + C * Real.exp (-(c * Real.sqrt L)) < 1 := by
  have t1 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * L))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hc)
  have t2 : Filter.Tendsto (fun L : ℝ => Real.exp (-(c * Real.sqrt L))) Filter.atTop (nhds 0) :=
    t1.comp Real.tendsto_sqrt_atTop
  have t3 := (t1.const_mul C).add (t2.const_mul C)
  simp only [mul_zero, add_zero] at t3
  have := (t3.eventually (gt_mem_nhds zero_lt_one)).and
    ((Filter.eventually_ge_atTop C₀).and (Filter.eventually_ge_atTop 2))
  obtain ⟨L, h, h1, h2⟩ := this.exists
  exact ⟨L, h1, h2, h⟩
end GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
