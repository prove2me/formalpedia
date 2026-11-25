-- Prove2me | solution 1 for GroundTheory.LocalField.unitsMeasureOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:52:41.67485+00:00
-- url     : https://prove2.me/submissions/e28b02e8-8987-432d-afc1-5af99b6ad2ed

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (μ : Measure K) [μ.IsAddHaarMeasure] :
    unitsMeasureOf μ = ((1 - ((residueCard K : ℝ≥0∞))⁻¹) * μ (𝒪[K] : Set K)) • multHaar K := by
  have h : unitsMeasureOf μ = (multHaarConst K)⁻¹ • multHaarOf μ := by
    rw [multHaarOf, smul_smul, ENNReal.inv_mul_cancel multHaarConst_ne_zero multHaarConst_ne_top,
      one_smul]
  rw [h, multHaarOf_eq, smul_smul, multHaarConst, inv_inv]
end GroundTheory.LocalField
