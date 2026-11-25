-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:56.890795+00:00
-- url     : https://prove2.me/submissions/f0b6a952-faf4-4374-b25a-5784044d710e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard_nnreal
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_add_eq
import Theorems.Thm_GroundTheory_LocalField_modulus_le_of_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_mem_nhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution : Continuous (modulus : K → ℝ≥0) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, modulus_zero, tendsto_order]
    refine ⟨fun a ha => (not_lt_zero ha).elim, fun ε hε => ?_⟩
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (one_lt_residueCard_nnreal (K := K)))
    filter_upwards [valBall_mem_nhds (K := K) k] with y hy
    calc modulus y ≤ (residueCard K : ℝ≥0) ^ (-(k : ℤ)) := modulus_le_of_mem_valBall hy
      _ = ((residueCard K : ℝ≥0))⁻¹ ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hk
  · have hmem : {y : K | y - x ∈ valBall K (ord x + 1)} ∈ 𝓝 x :=
      ((isOpen_valBall _).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
    have hev : ∀ᶠ y in 𝓝 x, modulus x = modulus y := by
      filter_upwards [hmem] with y hy
      have := modulus_add_eq hx hy
      rw [add_sub_cancel] at this
      exact this.symm
    exact tendsto_const_nhds.congr' hev
end GroundTheory.LocalField
