-- Prove2me | solution 2 for OAI.Problem356.CenterCertificate.strict_of_not_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:40:46.621594+00:00
-- url     : https://prove2.me/submissions/273df96b-10eb-4e3e-aff8-db64922a0500

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CenterCertificate.lean:L95-L111
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.CenterCertificate.strict_of_not_good. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.CenterCertificate ----
namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.CenterCertificate

theorem norm_sub_point (i j : Fin 5) : ‖point i - point j‖ = distance i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [point, distance, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.ext_iff]

theorem invDistance_point (i j : Fin 5) :
    invDistance (point i) (point j) = (ENNReal.ofReal (distance i j))⁻¹ := by
  rw [invDistance, norm_sub_point]

theorem cross_pair_gap :
    (5 / 2 : ℝ≥0∞) < 2 + (ENNReal.ofReal (Real.sqrt 2))⁻¹ := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hsE : ENNReal.ofReal (Real.sqrt 2) < (2 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg (2 : ℝ))).2 hs
  calc
    (5 / 2 : ℝ≥0∞) = 2 + (2 : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add]
    _ < 2 + (ENNReal.ofReal (Real.sqrt 2))⁻¹ :=
      ENNReal.add_lt_add_left (by norm_num) (ENNReal.inv_lt_inv.2 hsE)

/-- Every undesired component type has a strict supporting gap at its centers. -/
theorem strict_of_not_good (i j k : Fin 5) (h : ¬ Good i j k) :
    potential i + potential j + potential k <
      coulombCost (point i, (point j, point k)) := by
  have hgap := cross_pair_gap
  have hgap' : (5 / 2 : ℝ≥0∞) < 1 + (1 + (ENNReal.ofReal (Real.sqrt 2))⁻¹) := by
    simpa only [← add_assoc, one_add_one_eq_two] using hgap
  have hpos : 0 < (ENNReal.ofReal (Real.sqrt 2))⁻¹ := ENNReal.inv_pos.2 (by simp)
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try exact False.elim (h (by unfold Good; decide))
  all_goals norm_num [potential, coulombCost, tripleFst, tripleSnd, tripleThd,
      invDistance_point, distance, Fin.ext_iff]
  all_goals first
    | exact hgap
    | simpa only [add_comm, add_left_comm, add_assoc] using hgap'
    | positivity
    | finiteness

end Problem356.CenterCertificate

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.CenterCertificate
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.CenterCertificate.strict_of_not_good := @_root_.OAI.Problem356.CenterCertificate.strict_of_not_good
