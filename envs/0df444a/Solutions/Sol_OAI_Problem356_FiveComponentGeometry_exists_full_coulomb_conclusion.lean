-- Prove2me | solution 1 for OAI.Problem356.FiveComponentGeometry.exists_full_coulomb_conclusion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:16:30.540083+00:00
-- url     : https://prove2.me/submissions/5eb521f2-53b3-4499-a929-f8271352ac13

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/ActualGeometryConclusion.lean:L186-L206
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FiveComponentGeometry.exists_full_coulomb_conclusion. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterAxis
import Theorems.Thm_OAI_Problem356_CoulombSupportExistence_nonempty_coulombLocalSupportingCharts
import Theorems.Thm_OAI_Problem356_FiveComponentGeometry_exists_global_certificate
import Theorems.Thm_OAI_Problem356_FiveComponentGeometry_fullConclusion_of_five_component_certificate
import Theorems.Thm_OAI_Problem356_LocalGeometry_LocalSupportingCharts_exists_shrink

-- ---- from OAI.Analysis.CoulombTransport.ComponentPotential ----
namespace OAI

universe uIndex

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.ComponentPotential

variable {ι : Type uIndex} [Fintype ι]

theorem glue_eq {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) {i : ι} {x : E3}
    (hx : x ∈ U i) : glue U u x = u i x := by
  classical
  unfold glue
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_notMem
    intro hxj
    exact Set.disjoint_left.mp (hdisj hji) hxj hx
  · simp

end Problem356.ComponentPotential

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombSupportExistence ----
namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.CoulombSupportExistence

open CoulombCalculus GeometryJets LocalGeometry

/-- The two explicit conventions for the stationary field coincide. -/
theorem stationary_eq (a : E3) :
    StationaryMap.stationary a = stationaryEquation 20 a := by
  funext p
  apply Prod.ext
  · rfl
  · simp only [StationaryMap.stationary, stationaryEquation]
    have hn (x y : E3) : pairGradient (x - y) = -pairGradient (y - x) := by
      rw [← neg_sub y x, pairGradient_neg]
    rw [hn p.2.2 p.2.1, hn p.2.2 p.1]
    module

/-- The supporting charts in the scalar-potential stationary convention. -/
theorem nonempty_coulombLocalSupportingCharts_stationary (k : Fin 3) :
    Nonempty (LocalSupportingCharts
      (StationaryMap.jointPotential (axisVector k))
      (StationaryMap.stationary (axisVector k))
      (axisVector k) (0, -axisVector k)) := by
  rw [stationary_eq]
  exact nonempty_coulombLocalSupportingCharts k

end Problem356.CoulombSupportExistence

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombSupportSeparated ----
namespace OAI

noncomputable section

open Set Metric

namespace Problem356.CoulombSupportExistence

open LocalGeometry StationaryMap CoulombCalculus

private theorem outside_central_ball {a y : E3} (ha : ‖a‖ = 1)
    (hy : y ∈ ball a (1 / 4 : ℝ)) : y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  intro hx
  have htri := dist_triangle a y (0 : E3)
  rw [dist_zero_right, ha, dist_comm a y] at htri
  have hy' := mem_ball.mp hy
  have hx' := mem_ball.mp hx
  linarith

/-- Shrink both local domains before forming the global contact predicate.
Every parameter of the entire retained graph, not just parameters in a later
component ball, has both outer coordinates outside the fixed central ball. -/
theorem exists_separated_shrink {a : E3} (ha : ‖a‖ = 1)
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)) :
    ∃ D : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a),
      ∀ y ∈ D.charts.central.source,
        y ∉ ball (0 : E3) (1 / 4 : ℝ) ∧
          D.charts.opposite y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  obtain ⟨D, hsource, hstate, _, _, _⟩ :=
    C.exists_shrink (1 / 4) (1 / 4) (by norm_num) (by norm_num)
  refine ⟨D, ?_⟩
  intro y hy
  refine ⟨outside_central_ball ha (hsource hy).2, ?_⟩
  have hs := (hstate (D.charts.mapsTo_state hy)).2
  have hz : D.charts.opposite y ∈ ball (-a) (1 / 4 : ℝ) := by
    rw [← ball_prod_same] at hs
    exact hs.2
  exact outside_central_ball (by simpa only [norm_neg] using ha) hz

/-- Unconditional actual Coulomb supporting charts with graph-wide exclusion
of both outer coordinates from a common fixed central neighborhood. -/
theorem exists_coulombLocalSupportingCharts_separated (k : Fin 3) :
    ∃ C : LocalSupportingCharts (jointPotential (axisVector k))
      (stationary (axisVector k)) (axisVector k) (0, -axisVector k),
      ∀ y ∈ C.charts.central.source,
        y ∉ ball (0 : E3) (1 / 4 : ℝ) ∧
          C.charts.opposite y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  obtain ⟨C⟩ := nonempty_coulombLocalSupportingCharts_stationary k
  exact exists_separated_shrink (norm_axisVector k) C

end Problem356.CoulombSupportExistence

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.ActualGeometryConclusion ----
namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry CenterCertificate

/-- The unconditional witness: the actual separated local Coulomb charts
and their global certificate supply all inputs of the construction. -/
theorem exists_full_coulomb_conclusion :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  have hp1 : point 1 = CoulombCalculus.axisVector 0 := by
    ext i; fin_cases i <;> norm_num [point, CoulombCalculus.axisVector]
  have hp3 : point 3 = CoulombCalculus.axisVector 1 := by
    change (!₂[0, 1, 0] : E3) = CoulombCalculus.axisVector 1
    ext i; fin_cases i <;> norm_num [CoulombCalculus.axisVector]
  have h₁ := CoulombSupportExistence.exists_coulombLocalSupportingCharts_separated 0
  have h₂ := CoulombSupportExistence.exists_coulombLocalSupportingCharts_separated 1
  rw [← hp1] at h₁
  rw [← hp3] at h₂
  obtain ⟨C₁, hout₁⟩ := h₁
  obtain ⟨C₂, hout₂⟩ := h₂
  obtain ⟨R, M, hR, hM, _, hdisj, hu, _, hubound, hcert⟩ :=
    exists_global_certificate C₁ C₂
  apply fullConclusion_of_five_component_certificate C₁ C₂ hout₁ hout₂ hR hdisj hu
    hM.le hubound ?_ hcert
  intro i x hx
  exact ComponentPotential.glue_eq hdisj hx

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace
open LocalGeometry CenterCertificate


theorem solution : type_of% @_root_.OAI.Problem356.FiveComponentGeometry.exists_full_coulomb_conclusion := @_root_.OAI.Problem356.FiveComponentGeometry.exists_full_coulomb_conclusion
