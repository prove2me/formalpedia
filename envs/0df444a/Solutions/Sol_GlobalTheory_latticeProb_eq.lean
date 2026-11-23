-- Prove2me | solution 1 for GlobalTheory.latticeProb_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:29.8198+00:00
-- url     : https://prove2.me/submissions/ef5238e3-6bb9-4200-957f-eb9d5abcf0e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] :
    latticeProb L = (ENNReal.ofReal (ZLattice.covolume L μ))⁻¹ • μ.restrict (latticeDomain L) := by
  have h := Measure.isAddLeftInvariant_eq_smul (Measure.addHaar : Measure E) μ
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (Measure.addHaar : Measure E) μ
  set c := Measure.addHaarScalarFactor (Measure.addHaar : Measure E) μ
  rw [← measure_latticeDomain, latticeProb, h]
  have hc0 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Measure.restrict_smul, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_smul,
    smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_right_comm,
    ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]
end GlobalTheory
