-- Prove2me | solution 1 for GroundTheory.LocalField.lintegral_multHaar_le_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:00.86898+00:00
-- url     : https://prove2.me/submissions/c1e6f68c-b6a5-452a-89da-dc24b504e86d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Theorems.Thm_GroundTheory_LocalField_measurableSet_ordShell
import Theorems.Thm_GroundTheory_LocalField_lintegral_multHaar_eq_tsum

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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (g : Kˣ → ℝ≥0∞) (a : ℤ → ℝ≥0∞)
    (h : ∀ u, g u ≤ a (ord (u : K))) : ∫⁻ u, g u ∂multHaar K ≤ ∑' k, a k := by
  rw [lintegral_multHaar_eq_tsum]
  refine ENNReal.tsum_le_tsum fun k => ?_
  calc ∫⁻ u in ordShell K k, g u ∂multHaar K ≤ ∫⁻ _ in ordShell K k, a k ∂multHaar K :=
        setLIntegral_mono' (measurableSet_ordShell k) fun u hu => (h u).trans_eq (by rw [hu])
    _ = a k := by rw [setLIntegral_const, multHaar_ordShell, mul_one]
end GroundTheory.LocalField
