-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.LinearChart.map_mul_right_haar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:02.686268+00:00
-- url     : https://prove2.me/submissions/2f099ab8-ad27-4f9d-89b9-ba5766c656fe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
open GroundTheory.Automorphic.Measures.LinearChart
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] (C : LinearChart F ι G)
variable (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]
variable [LocallyCompactSpace G]
variable [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic.Measures.LinearChart
theorem _root_.solution (h : G) :
    map (· * h) (C.haar μ₀) = (C.leftModulus h / C.rightModulus h) • C.haar μ₀ := by
  rw [haar, map_withDensity_of_scale (continuous_mul_const h).measurable C.measurable_density
    (C.map_mul_right_comap μ₀ h) (b := C.leftModulus h) fun x => ?_, div_eq_mul_inv, mul_comm]
  rw [← ENNReal.coe_mul, ENNReal.coe_inj, C.leftModulus_mul, mul_inv, mul_comm, mul_assoc,
    inv_mul_cancel₀ (C.leftModulus_pos h).ne', mul_one]
end GroundTheory.Automorphic.Measures.LinearChart
