-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.norm_deriv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:04.582672+00:00
-- url     : https://prove2.me/submissions/a8b78db6-8b8f-4c3a-b1d3-8683ebe5bbfc

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_deriv_sq_quot
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hm : ∀ s, h s = 0 → deriv h s = 0) {r M δ : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) (hδ : 0 < δ)
    (hM : ∀ t ∈ closedBall (0 : ℂ) 1, ‖h t‖ ≤ M) (hl : ∀ t ∈ sphere (0 : ℂ) r, δ ≤ ‖h t‖) :
    ‖deriv h 0 ^ 2‖ ≤ (2 * M) ^ 2 / δ * ‖h 0‖ := by
  obtain ⟨k, hk, hk'⟩ := exists_deriv_sq_quot hh
    ⟨r, norm_pos_iff.1 (hδ.trans_le (hl _ (by simp [hr.le])))⟩ hm
  rw [← hk', norm_mul]
  gcongr
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball 0 r) isBounded_ball
    hk.diffContOnCl (fun t ht => ?_) (subset_closure (mem_ball_self hr))
  rw [frontier_ball _ hr.ne'] at ht
  have h1 : ‖deriv h t‖ ≤ M / (1 / 2) := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hh.diffContOnCl
      fun z hz => hM z ?_
    rw [mem_sphere] at ht hz
    rw [mem_closedBall]
    linarith [dist_triangle z t 0]
  rw [le_div_iff₀ hδ]
  calc ‖k t‖ * δ ≤ ‖k t‖ * ‖h t‖ := by gcongr; exact hl t ht
    _ = ‖deriv h t‖ ^ 2 := by rw [← norm_mul, hk', norm_pow]
    _ ≤ _ := by gcongr; linarith
end GlobalTheory.ThetaGauss
