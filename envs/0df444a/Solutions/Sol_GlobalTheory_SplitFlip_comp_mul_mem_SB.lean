-- Prove2me | solution 1 for GlobalTheory.SplitFlip.comp_mul_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:29.966565+00:00
-- url     : https://prove2.me/submissions/52593dbb-32fa-416e-b3b1-19ef91dacbd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (g : GL A k) (h : GL D k) {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    (fun X => Φ (g.val * X * h.val)) ∈ SB (Matrix A D k) := by
  have := (SB (Matrix A D k)).smul_mem (om 1 h g⁻¹ (fun _ => 1) 0)⁻¹ (om_mem_SB 1 h g⁻¹ hΦ)
  convert this using 1
  funext X
  have h1 := fun (x : kˣ) (r : ℝ) => (Real.rpow_pos_of_pos (nabs_pos x) r).ne'
  simp only [om, Pi.smul_apply, smul_eq_mul, inv_inv, mul_one]
  rw [inv_mul_cancel_left₀]
  simp only [ne_eq, mul_eq_zero, Units.ne_zero, Complex.ofReal_eq_zero, h1, or_self, not_false_eq_true]
end GlobalTheory.SplitFlip
