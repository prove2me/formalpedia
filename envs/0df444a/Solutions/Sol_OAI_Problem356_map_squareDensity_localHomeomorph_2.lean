-- Prove2me | solution 2 for OAI.Problem356.map_squareDensity_localHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:31:03.718384+00:00
-- url     : https://prove2.me/submissions/1c90559d-a2be-4eeb-8d99-e47bec9e53b0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SmoothPushforward.lean:L130-L159
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.map_squareDensity_localHomeomorph. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_map_withDensity_localHomeomorph

-- ---- from OAI.Analysis.CoulombTransport.SmoothPushforward ----
namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Problem356

/-- The local inverse-Jacobian formula carries a square density to a
square density, exactly as required by the five-component construction. -/
theorem map_squareDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (g : E3 → ℝ)
    (hgs : tsupport g ⊆ e.source)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y =>
        localTransportAmplitude e g (fun z => Real.sqrt |(D z).det|) y ^ 2) := by
  have hsource : densityMeasure (fun x => g x ^ 2) =
      ((volume : Measure E3).restrict e.source).withDensity
        (fun x => ENNReal.ofReal (g x ^ 2)) := by
    rw [densityMeasure, ← withDensity_indicator e.open_source.measurableSet]
    congr 1
    ext x
    by_cases hx : x ∈ e.source
    · simp [hx]
    · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hgs h))
      simp [hx, hgx]
  rw [hsource, map_withDensity_localHomeomorph e _ D hD, densityMeasure,
    ← withDensity_indicator e.open_target.measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ e.target
  · simp only [indicator_of_mem hy, localTransportAmplitude, mul_pow,
      Real.sq_sqrt (abs_nonneg _)]
    rw [mul_comm (g (e.symm y) ^ 2), ENNReal.ofReal_mul (abs_nonneg _)]
  · simp [localTransportAmplitude, hy]

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory Set Filter
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.map_squareDensity_localHomeomorph := @_root_.OAI.Problem356.map_squareDensity_localHomeomorph
