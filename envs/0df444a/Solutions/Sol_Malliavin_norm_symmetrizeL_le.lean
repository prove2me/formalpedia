-- Prove2me | solution 1 for Malliavin.norm_symmetrizeL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:44.093041+00:00
-- url     : https://prove2.me/submissions/c97bad61-9157-438f-a7c9-c4282864207f

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_norm_permL_le

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}
namespace Malliavin
theorem _root_.solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖symmetrizeL E (μ := μ) n p‖ ≤ 1 := by
  have hsum : ‖∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ‖ ≤ (n.factorial : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun σ _ => norm_permL_le (E := E) (μ := μ) n p σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  calc ‖symmetrizeL E (μ := μ) n p‖
      = ‖(n.factorial : ℝ)⁻¹‖ * ‖∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ‖ :=
        norm_smul _ _
    _ ≤ ‖(n.factorial : ℝ)⁻¹‖ * (n.factorial : ℝ) := by gcongr
    _ = 1 := by
        rw [norm_inv, Real.norm_natCast, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero)]
end Malliavin
