-- Prove2me | solution 1 for OAI.ShortDraftMellin.mobiusExpSum_flat_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:24.958369+00:00
-- url     : https://prove2.me/submissions/67aa21e2-6376-443d-8857-6f8d5a82e3cf

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_norm_le_two

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin
namespace OAI.ShortDraftMellin
theorem _root_.solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by
  have hExp : (fun t : ℝ => mobiusExpSum χ t) =O[atTop]
      (fun t : ℝ => Real.exp (-t)) := by
    apply isBigO_iff_isBigOWith.mpr
    refine ⟨2, IsBigOWith.of_bound ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      mobiusExpSum_norm_le_two χ t ht
  have hpow : (fun t : ℝ => mobiusExpSum χ t) =O[atTop]
      (fun t : ℝ => t ^ (-b)) := by
    apply hExp.trans
    simpa only [one_mul, neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-b)).isBigO
  have hcomp := hpow.comp_tendsto tendsto_inv_nhdsGT_zero
  refine hcomp.congr (fun _ => rfl) ?_
  intro D
  dsimp
  rw [← Real.rpow_neg_eq_inv_rpow]
  simp
end OAI.ShortDraftMellin
