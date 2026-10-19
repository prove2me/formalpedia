-- Prove2me | solution 2 for OAI.Problem356.FiveComponentGeometry.strict_center_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:59:18.060285+00:00
-- url     : https://prove2.me/submissions/5d216c1a-7fa7-4944-80b1-e19b49b18106

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/FiveComponentGeometry.lean:L103-L122
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FiveComponentGeometry.strict_center_gap. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Theorems.Thm_OAI_Problem356_CenterCertificate_strict_of_not_good

-- ---- from OAI.Analysis.CoulombTransport.CoulombLocalCertificate ----
namespace OAI

universe uE

noncomputable section

open Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.LocalGeometry

open StationaryMap CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem statePotential_center_value {a : E} (ha : ‖a‖ = 1) :
    statePotential a a (0, -a) = 0 := by
  have hvec : -a - a = (-2 : ℝ) • a := by module
  have hnorm : ‖-a - a‖ = 2 := by rw [hvec, norm_smul, ha]; norm_num
  simp [statePotential, pairCost, ha, hnorm]
  norm_num

/-- The branch value vanishes at the center, as required to glue the five
local potentials with values `5/2,0,0,0,0`. -/
theorem localSupporting_value_center {a : E} (ha : ‖a‖ = 1)
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)) :
    C.value a = 0 := by
  rw [C.value_base]
  exact statePotential_center_value ha

end Problem356.LocalGeometry

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FiveComponentGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

lemma norm_point_one : ‖point 1‖ = 1 := by
  change ‖(!₂[1, 0, 0] : E3)‖ = 1
  norm_num [point, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

lemma norm_point_three : ‖point 3‖ = 1 := by
  change ‖(!₂[0, 1, 0] : E3)‖ = 1
  norm_num [point, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

lemma point_two_eq_neg : point 2 = -point 1 := by
  change (!₂[-1, 0, 0] : E3) = -(!₂[1, 0, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma point_four_eq_neg : point 4 = -point 3 := by
  change (!₂[0, -1, 0] : E3) = -(!₂[0, 1, 0] : E3)
  ext i
  fin_cases i <;> norm_num [point]

lemma potentials_center_values (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, potentials C₁ C₂ i (point i) = if i = 0 then (5 / 2 : ℝ) else 0 := by
  intro i
  fin_cases i
  · norm_num [potentials, point]
  · exact localSupporting_value_center norm_point_one C₁
  · change (5 : ℝ) / 4 * ⟪point 1, point 2 + point 1⟫_ℝ -
      10 * ‖point 2 + point 1‖ ^ 2 = 0
    rw [point_two_eq_neg]
    simp
  · exact localSupporting_value_center norm_point_three C₂
  · change (5 : ℝ) / 4 * ⟪point 3, point 4 + point 3⟫_ℝ -
      10 * ‖point 4 + point 3‖ ^ 2 = 0
    rw [point_four_eq_neg]
    simp

/-- The actual potentials have the strict bad-type gap supplied by the
finite center certificate. -/
lemma strict_center_gap (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (h : ¬ Good i j k) :
    ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) <
      coulombCost (point i, (point j, point k)) := by
  have he (l : Fin 5) : ENNReal.ofReal (potentials C₁ C₂ l (point l)) = potential l := by
    rw [potentials_center_values]
    by_cases hl : l = 0
    · simp only [hl, ite_eq_left, potential]
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    · simp [potential, hl]
  have hn (l : Fin 5) : 0 ≤ potentials C₁ C₂ l (point l) := by
    rw [potentials_center_values]
    split_ifs <;> norm_num
  rw [ENNReal.ofReal_add (add_nonneg (hn i) (hn j)) (hn k),
    ENNReal.ofReal_add (hn i) (hn j), he i, he j, he k]
  exact strict_of_not_good i j k h

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal InnerProductSpace
open LocalGeometry StationaryMap CenterCertificate


theorem solution : type_of% @_root_.OAI.Problem356.FiveComponentGeometry.strict_center_gap := @_root_.OAI.Problem356.FiveComponentGeometry.strict_center_gap
