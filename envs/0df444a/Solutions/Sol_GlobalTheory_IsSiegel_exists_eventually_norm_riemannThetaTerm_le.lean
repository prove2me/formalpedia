-- Prove2me | solution 1 for GlobalTheory.IsSiegel.exists_eventually_norm_riemannThetaTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:50.875371+00:00
-- url     : https://prove2.me/submissions/dc2b3eff-722e-4e30-b0c9-ab7cd9c030e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_exists_eventually_mul_dotProduct_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : ∃ c > 0, ∃ S, ∀ᶠ p : (ι → ℂ) × Matrix ι ι ℂ in 𝓝 (v, Ω),
      ∀ n, ‖riemannThetaTerm a b p.2 p.1 n‖ ≤ riemannThetaBound a c S n := by
  obtain ⟨c, hc, hY⟩ := h.exists_eventually_mul_dotProduct_le
  refine ⟨c, hc, ‖v‖ + 1, ?_⟩
  have h1 : ∀ᶠ w : ι → ℂ in 𝓝 v, ‖w‖ < ‖v‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [h1.prod_nhds hY] with p hp n
  exact norm_riemannThetaTerm_le a b hp.2 (fun i => (abs_im_apply_le_norm _ i).trans hp.1.le) n
end IsSiegel
end GlobalTheory
