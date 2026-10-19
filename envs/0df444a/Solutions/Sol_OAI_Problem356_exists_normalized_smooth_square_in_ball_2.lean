-- Prove2me | solution 2 for OAI.Problem356.exists_normalized_smooth_square_in_ball
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:27:54.960095+00:00
-- url     : https://prove2.me/submissions/78acdf0f-d2f6-4d46-a45e-c0d9c02f000f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/Density.lean:L48-L88
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_normalized_smooth_square_in_ball. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap

-- ---- from OAI.Analysis.CoulombTransport.Density ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A normalized nonnegative smooth square can be placed in any positive-radius ball. -/
theorem exists_normalized_smooth_square_in_ball (c : E3) {r : ℝ} (hr : 0 < r) :
    ∃ g : E3 → ℝ,
      (∀ x, 0 ≤ g x) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
      HasCompactSupport g ∧
      tsupport g ⊆ Metric.ball c r ∧
      (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by
  let b : ContDiffBump c := ⟨r / 4, r / 2, by linarith, by linarith⟩
  have hb_compact : HasCompactSupport (fun x : E3 => (b x) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using
      b.hasCompactSupport.mul_left (f := fun x => b x)
  have hb_center : b c = 1 := by
    exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hm : 0 < ∫ x : E3, (b x) ^ 2 ∂(volume : Measure E3) := by
    apply (b.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := c) hb_compact (fun x => sq_nonneg (b x))
    change (b c) ^ 2 ≠ 0
    rw [hb_center]
    norm_num
  let g : E3 → ℝ := fun x => b x /
    Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3))
  refine ⟨g, fun x => div_nonneg b.nonneg (Real.sqrt_nonneg _),
    b.contDiff.div_const _, ?_, ?_, ?_⟩
  · simpa only [g, div_eq_mul_inv, Pi.mul_def] using
      b.hasCompactSupport.mul_right (f' := fun _ =>
        (Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3)))⁻¹)
  · have hs : tsupport g ⊆ tsupport (fun x : E3 => b x) := by
      simpa only [g, div_eq_mul_inv, Pi.mul_def] using
        (tsupport_mul_subset_left (f := fun x : E3 => b x)
          (g := fun _ => (Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3)))⁻¹))
    apply hs.trans
    rw [b.tsupport_eq]
    intro x hx
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    change dist x c ≤ r / 2 at hx'
    linarith
  · dsimp only [g]
    simp_rw [div_pow]
    rw [integral_div, Real.sq_sqrt hm.le, div_self hm.ne']

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.exists_normalized_smooth_square_in_ball := @_root_.OAI.Problem356.exists_normalized_smooth_square_in_ball
