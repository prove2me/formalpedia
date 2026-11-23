-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.expand_simple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:58.077523+00:00
-- url     : https://prove2.me/submissions/4988f709-e6ec-4921-a2a0-6230dfd858a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
import Theorems.Thm_GlobalTheory_ExplicitRect_analyticAt_dslope
import Theorems.Thm_GlobalTheory_ExplicitRect_eq_add_dslope
import Theorems.Thm_GlobalTheory_ExplicitRect_analyticAt_cpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution {φ g : ℂ → ℂ} {p k : ℂ} {u : ℝ} (hu : 0 < u) (hp : p ≠ 0)
    (hg : AnalyticAt ℂ g p) (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G p ∧ ∀ᶠ s in 𝓝[≠] p,
      -(φ s) * (u : ℂ) ^ s / s = a / (s - p) ^ 2 + (-(k * ((u : ℂ) ^ p / p))) / (s - p) + G s := by
  have hW : AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s / s) p :=
    (analyticAt_cpow hu p).div analyticAt_id hp
  refine ⟨0, fun s => -(k * dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s) - g s * ((u : ℂ) ^ s / s),
    ((analyticAt_const.mul (analyticAt_dslope hW)).neg).sub (hg.mul hW), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hexp : (u : ℂ) ^ s / s = (u : ℂ) ^ p / p + (s - p) * dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s :=
    eq_add_dslope (fun s : ℂ => (u : ℂ) ^ s / s) p s
  rw [hs, mul_div_assoc, hexp]
  field_simp
  ring
end GlobalTheory.ExplicitRect
