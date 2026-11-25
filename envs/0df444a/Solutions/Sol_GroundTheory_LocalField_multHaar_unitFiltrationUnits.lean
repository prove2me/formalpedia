-- Prove2me | solution 1 for GroundTheory.LocalField.multHaar_unitFiltrationUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:02:57.05529+00:00
-- url     : https://prove2.me/submissions/64ceb979-bac5-40b0-9f62-9635792735a9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits
import Theorems.Thm_GroundTheory_LocalField_localZeta_oneAddValBallIndicator
import Theorems.Thm_GroundTheory_LocalField_oneAddValBallIndicator_apply


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
theorem _root_.solution {c : ℕ} (hc : 1 ≤ c) :
    (multHaar K (unitFiltrationUnits K c)).toReal =
      (multHaarConst K).toReal * (haarIntegers K).real (valBall K c) := by
  classical
  have h := localZeta_oneAddValBallIndicator (χ := (1 : Kˣ →* ℂˣ)) hc
    (fun _ _ => MonoidHom.mem_ker.mpr rfl) 0
  have hpt : ∀ u : Kˣ, oneAddValBallIndicator (c : ℤ) (u : K) * (((1 : Kˣ →* ℂˣ) u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ (0 : ℂ) =
      (unitFiltrationUnits K c : Set Kˣ).indicator (fun _ => (1 : ℂ)) u := by
    intro u
    rw [oneAddValBallIndicator_apply, MonoidHom.one_apply, Units.val_one, Complex.cpow_zero,
      mul_one, mul_one]
    by_cases hu : (u : K) - 1 ∈ valBall K c
    · rw [if_pos hu, Set.indicator_of_mem ((mem_unitFiltrationUnits_iff_valBall hc).mpr hu)]
    · rw [if_neg hu, Set.indicator_of_notMem (mt (mem_unitFiltrationUnits_iff_valBall hc).mp hu)]
  unfold localZeta at h
  rw [show (fun u : Kˣ => oneAddValBallIndicator (c : ℤ) (u : K) *
      (((1 : Kˣ →* ℂˣ) u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ (0 : ℂ)) =
      fun u : Kˣ => (unitFiltrationUnits K c : Set Kˣ).indicator (fun _ => (1 : ℂ)) u from
      funext hpt,
    integral_indicator_const _ (isOpen_unitFiltrationUnits c).measurableSet, Complex.real_smul,
    mul_one, measureReal_def] at h
  exact_mod_cast h
end GroundTheory.LocalField
