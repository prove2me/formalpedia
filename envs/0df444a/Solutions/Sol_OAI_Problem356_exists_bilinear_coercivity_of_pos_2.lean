-- Prove2me | solution 2 for OAI.Problem356.exists_bilinear_coercivity_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:20:02.307765+00:00
-- url     : https://prove2.me/submissions/01e0a191-c7da-4ac9-8362-5a0354b66745

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/HessianCoercivity.lean:L48-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_bilinear_coercivity_of_pos. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.HessianCoercivity ----
namespace OAI

universe uE uX

open Filter
open scoped Topology

namespace Problem356

/-- In finite dimension, strict positivity of a continuous bilinear form gives
one uniform positive quadratic lower bound. -/
theorem exists_bilinear_coercivity_of_pos
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ a : ℝ, 0 < a ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  | inr h =>
    have := h
    obtain ⟨u, hu⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
    have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨u, by simpa using hu⟩
    have hcont : Continuous (fun v => B v v) := B.continuous.clm_apply continuous_id
    obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
      hcont.continuousOn
    have hwNorm : ‖w‖ = 1 := by simpa using hw
    have hwne : w ≠ 0 := by intro hw0; simp [hw0] at hwNorm
    refine ⟨B w w, hpos w hwne, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hynorm : ‖(‖v‖)⁻¹ • v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
    have hy : (‖v‖)⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by simpa using hynorm
    have hmin : B w w ≤ B ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) := hwmin hy
    have hscale : B ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) * ‖v‖ ^ 2 = B v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      field_simp
    have hmul := mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖v‖)
    rwa [hscale] at hmul

end Problem356

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Filter
open scoped Topology


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.exists_bilinear_coercivity_of_pos.{uE} := @_root_.OAI.Problem356.exists_bilinear_coercivity_of_pos.{uE}
