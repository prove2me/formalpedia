-- Prove2me | solution 1 for GroundTheory.LocalField.localZeta_oneAddValBallIndicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:28.924528+00:00
-- url     : https://prove2.me/submissions/3a2b1379-e562-41a7-b969-d07b86736d22

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_oneAddValBallIndicator_apply
import Theorems.Thm_GroundTheory_LocalField_oneAddValBallIndicator_add_one
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_integral_multHaar_mul_modulus
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_one_iff
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitFiltrationUnits_antitone
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
namespace GroundTheory.LocalField
theorem _root_.solution {c : ℕ} (hc : 1 ≤ c)
    (hker : unitFiltrationUnits K c ≤ χ.ker) (s : ℂ) :
    localZeta (oneAddValBallIndicator c) χ s =
      (multHaarConst K).toReal * (haarIntegers K).real (valBall K c) := by
  have hpt : ∀ u : Kˣ, oneAddValBallIndicator (c : ℤ) (u : K) * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s =
      oneAddValBallIndicator (c : ℤ) (u : K) * ((modulus (u : K) : ℝ) : ℂ) := by
    intro u
    by_cases hu : (u : K) - 1 ∈ valBall K c
    · have hU : u ∈ unitFiltrationUnits K c := (mem_unitFiltrationUnits_iff_valBall hc).mpr hu
      have hord : ord (u : K) = 0 :=
        mem_unitFiltrationUnits_zero_iff_ord.mp (unitFiltrationUnits_antitone (Nat.zero_le c) hU)
      have hmod : modulus (u : K) = 1 := modulus_eq_one_iff.mpr ⟨u.ne_zero, hord⟩
      rw [MonoidHom.mem_ker.mp (hker hU), hmod]
      simp
    · classical
      rw [oneAddValBallIndicator_apply, if_neg hu]
      simp
  unfold localZeta
  rw [show (fun u : Kˣ => oneAddValBallIndicator (c : ℤ) (u : K) * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s) =
    fun u : Kˣ => oneAddValBallIndicator (c : ℤ) (u : K) * ((modulus (u : K) : ℝ) : ℂ) from funext hpt,
    integral_multHaar_mul_modulus, ← integral_add_left_eq_self _ 1]
  simp only [oneAddValBallIndicator_add_one]
  rw [integral_indicator (measurableSet_valBall _), setIntegral_const, Complex.real_smul, mul_one]
end GroundTheory.LocalField
