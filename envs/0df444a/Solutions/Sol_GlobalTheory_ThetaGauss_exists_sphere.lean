-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.exists_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:57.254073+00:00
-- url     : https://prove2.me/submissions/1b73932b-7442-44ae-8bc6-100a03bd0f0f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {p : ℂ → Prop} (hp : ∀ᶠ t in 𝓝[≠] (0 : ℂ), p t) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∀ t ∈ sphere (0 : ℂ) r, p t := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hp
  obtain ⟨ε, hε, h⟩ := hp
  refine ⟨min (ε / 2) (1 / 2), by positivity, min_le_right _ _, fun t ht => h ?_ ?_⟩
  · rw [mem_sphere] at ht
    rw [ht]; exact (min_le_left _ _).trans_lt (by linarith)
  · rintro rfl
    simp only [mem_sphere, dist_self] at ht
    exact absurd ht (ne_of_lt (by positivity))
end GlobalTheory.ThetaGauss
