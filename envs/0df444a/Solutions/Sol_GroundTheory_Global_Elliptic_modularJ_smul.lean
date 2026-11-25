-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.modularJ_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:55:35.30586+00:00
-- url     : https://prove2.me/submissions/aee9a45f-3b0f-4b98-99b5-86f139380398

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____29e4a99442e2
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_zero


attribute [local simp] GroundTheory.Global.Elliptic.latticeOfTau_ω₁
attribute [local simp] GroundTheory.Global.Elliptic.latticeOfTau_ω₂

set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology
open scoped PeriodPair Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (γ : SL(2, ℤ)) (τ : ℍ) : modularJ (γ • τ) = modularJ τ := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  simp only [CuspForm.coe_discriminant] at hΔ
  have hd := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have hΔ0 := ModularForm.discriminant_ne_zero τ
  rw [modularJ, modularJ, show γ • τ = (γ : GL (Fin 2) ℝ) • τ from rfl, h4, hΔ]
  have : (denom (γ : GL (Fin 2) ℝ) τ ^ (4 : ℤ)) ^ 3 = denom (γ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) := by
    rw [← zpow_natCast, ← zpow_mul]; norm_num
  rw [mul_pow, this, mul_div_mul_left _ _ (zpow_ne_zero _ hd)]
end GroundTheory.Global.Elliptic
