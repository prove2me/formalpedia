-- Prove2me | solution 1 for GlobalTheory.taylorDir_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:34.449121+00:00
-- url     : https://prove2.me/submissions/ac0e3399-f38d-4e8c-8466-b974a8197c9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_coeff_taylorDir_eq_zero_iff
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}
namespace GlobalTheory
theorem _root_.solution (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) : taylorDir u f = 0 ↔ f =ᶠ[𝓝 0] 0 := by
  refine ⟨fun h => ?_, fun h => by rw [taylorDir_congr u h, taylorDir_zero]⟩
  have h1 : ∀ n, iteratedFDeriv ℂ n f 0 = 0 := fun n =>
    (coeff_taylorDir_eq_zero_iff u hu hf n).1 fun m _ => by rw [h, map_zero]
  obtain ⟨p, r, hp⟩ := hf
  filter_upwards [Metric.eball_mem_nhds (0 : W) hp.r_pos] with y hy
  have h2 := hp.hasSum_iteratedFDeriv hy
  simp only [h1, ContinuousMultilinearMap.zero_apply, smul_zero, zero_add] at h2
  exact h2.unique hasSum_zero
end GlobalTheory
