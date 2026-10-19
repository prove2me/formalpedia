-- Prove2me | solution 2 for OAI.Problem356.FiveComponentGeometry.ennreal_local_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:01:34.623144+00:00
-- url     : https://prove2.me/submissions/e45919bd-7e9e-4ad1-add5-ecf5e2bc2982

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/FiveComponentGeometry.lean:L124-L151
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FiveComponentGeometry.ennreal_local_certificate. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.CoulombEstimates ----
namespace OAI

universe uE uA

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.CoulombEstimates

/-- The real formula agrees with the extended-valued cost away from collisions. -/
theorem coulombCost_eq_ofReal_realCost {x y z : E3}
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    coulombCost (x, (y, z)) = ENNReal.ofReal (realCost x y z) := by
  unfold realCost
  rw [ENNReal.ofReal_add (add_nonneg (inv_nonneg.mpr dist_nonneg)
        (inv_nonneg.mpr dist_nonneg)) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_add (inv_nonneg.mpr dist_nonneg) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_inv_of_pos hxy, ENNReal.ofReal_inv_of_pos hxz,
    ENNReal.ofReal_inv_of_pos hyz]
  rfl

end Problem356.CoulombEstimates

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CostTopology ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma invDistance_pos (x y : E3) : 0 < invDistance x y := by
  simp [invDistance]

lemma coulombCost_pos (t : Triple) : 0 < coulombCost t := by
  unfold coulombCost
  exact lt_of_lt_of_le (invDistance_pos _ _)
    ((le_add_right le_rfl).trans (le_add_right le_rfl))

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombLocalCertificate ----
namespace OAI

universe uE

noncomputable section

open Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.LocalGeometry

open StationaryMap CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restore the central and opposite quadratic potentials in the local
supporting inequality. This is the literal three-point Coulomb formula. -/
theorem local_coulomb_supporting {a : E}
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a))
    {x y z : E}
    (hy : y ∈ Metric.ball a C.parameterRadius)
    (hx : x ∈ Metric.ball (0 : E) C.stateRadius)
    (hz : z ∈ Metric.ball (-a) C.stateRadius) :
    ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫ - 10 * ‖z + a‖ ^ 2) ≤
      ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹ := by
  have hy' : y ∈ C.charts.central.source := C.source_ball ▸ hy
  have hs : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, ← ball_prod_same]
    exact ⟨hx, hz⟩
  have h := C.supporting y hy' (x, z) hs
  simp only [jointPotential, statePotential, pairCost, norm_sub_rev z y] at h
  linarith

/-- Equality in the supporting inequality is exactly the stationary branch,
not merely inclusion of the branch in the contact set. -/
theorem local_coulomb_contact {a : E}
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a))
    {x y z : E}
    (hy : y ∈ Metric.ball a C.parameterRadius)
    (hx : x ∈ Metric.ball (0 : E) C.stateRadius)
    (hz : z ∈ Metric.ball (-a) C.stateRadius) :
    (‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹ =
      ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫ - 10 * ‖z + a‖ ^ 2)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y := by
  have hy' : y ∈ C.charts.central.source := C.source_ball ▸ hy
  have hs : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, ← ball_prod_same]
    exact ⟨hx, hz⟩
  have h := C.contact y hy' (x, z) hs
  simp only [jointPotential, statePotential, pairCost, norm_sub_rev z y, Prod.mk.injEq] at h
  rw [← h]
  constructor <;> intro heq <;> linarith

end Problem356.LocalGeometry

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FiveComponentGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

/-- The real local certificate has the exact extended-valued interpretation
on any collision-free triple in its three component balls. -/
theorem ennreal_local_certificate {a : E3} (C : ChartsAt a) {x y z : E3}
    (hy : y ∈ ball a C.parameterRadius)
    (hx : x ∈ ball (0 : E3) C.stateRadius)
    (hz : z ∈ ball (-a) C.stateRadius)
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) = coulombCost (x, (y, z)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y) := by
  let R : ℝ := ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖y - z‖⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hc : coulombCost (x, (y, z)) = ENNReal.ofReal R := by
    simpa only [CoulombEstimates.realCost, dist_eq_norm] using
      CoulombEstimates.coulombCost_eq_ofReal_realCost hxy hxz hyz
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact ENNReal.ofReal_le_ofReal (local_coulomb_supporting C hy hx hz)
  · constructor
    · intro heq
      have hs := (ENNReal.ofReal_pos.mp (heq.symm ▸ coulombCost_pos (x, (y, z)))).le
      have heqR := (ENNReal.ofReal_eq_ofReal_iff hs hR).mp (heq.trans hc)
      exact (local_coulomb_contact C hy hx hz).mp heqR.symm
    · intro hbranch
      have heqR := (local_coulomb_contact C hy hx hz).mpr hbranch
      exact (congrArg ENNReal.ofReal heqR).symm.trans hc.symm

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal InnerProductSpace
open LocalGeometry StationaryMap CenterCertificate


theorem solution : type_of% @_root_.OAI.Problem356.FiveComponentGeometry.ennreal_local_certificate := @_root_.OAI.Problem356.FiveComponentGeometry.ennreal_local_certificate
