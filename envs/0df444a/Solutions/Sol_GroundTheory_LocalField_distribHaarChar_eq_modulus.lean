-- Prove2me | solution 1 for GroundTheory.LocalField.distribHaarChar_eq_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:34.630422+00:00
-- url     : https://prove2.me/submissions/6774263b-907a-4e68-9363-d163eedbe144

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_modulus_of_ne_zero
import Theorems.Thm_GroundTheory_LocalField_measure_valBall
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall


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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure]
namespace GroundTheory.LocalField
theorem _root_.solution (u : Kˣ) : distribHaarChar K u = modulus (u : K) := by
  have h0 : haarIntegers K (valBall K 0) ≠ 0 :=
    ((isOpen_valBall 0).measure_pos (haarIntegers K) ⟨0, zero_mem _⟩).ne'
  have ht : haarIntegers K (valBall K 0) ≠ ∞ := (isCompact_valBall 0).measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := haarIntegers K) h0 ht ?_
  have hu : ((u : K)) ≠ 0 := u.ne_zero
  have : u • (valBall K 0 : Set K) = (u : K) • (valBall K 0 : Set K) := rfl
  rw [this, smul_valBall hu, zero_add, measure_valBall (haarIntegers K), modulus_of_ne_zero hu]
end GroundTheory.LocalField
