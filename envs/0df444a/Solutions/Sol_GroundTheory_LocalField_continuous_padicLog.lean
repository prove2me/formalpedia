-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_padicLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:29.07626+00:00
-- url     : https://prove2.me/submissions/826d34ca-67c0-4f1a-b40b-cb3f2cec3335

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall
import Theorems.Thm_GroundTheory_LocalField_logSeries_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_tendsto_zero_iff_valBall
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution : Continuous (padicLog K) := by
  refine continuous_of_continuousAt_zero (padicLog K) ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_valBall]
  intro N
  set p := ringChar 𝓀[K]
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  set r : ℕ := N.toNat + e + 1 with hr_def
  have hr : (e : ℤ) < (p - 1 : ℤ) * (r : ℕ) := by
    have : (e : ℤ) + 1 ≤ r := by rw [hr_def]; push_cast; omega
    nlinarith
  have hcont : Continuous fun u : Additive (unitFiltrationUnits K 1) ↦
      ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_toMul)).sub
      continuous_const
  have hopen := (isOpen_valBall (r : ℤ)).preimage hcont
  filter_upwards [hopen.mem_nhds (by simp)] with u hu
  refine valBall_antitone ?_ (logSeries_mem_valBall p hu hr)
  rw [hr_def]; push_cast
  have := Int.self_le_toNat N
  omega
end GroundTheory.LocalField
