-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.Uni.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:39.296026+00:00
-- url     : https://prove2.me/submissions/ceb7a512-e98d-4211-a26c-4f184e192d4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.Radical
namespace Uni
theorem _root_.solution {b : ι → ℕ} {g : GL ι k} (h : Uni b g.val) : Uni b (g⁻¹).val := by
  have hb : (g⁻¹).val.BlockTriangular b := by
    letI : Invertible g.val := g.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri
  intro r s hrs
  have : ((g⁻¹).val * g.val) r s = ((g⁻¹).val * (1 : Matrix ι ι k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b s) (b t) with ht | ht
    · rw [h t s ht]
    · rw [hb (show b t < b r from lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [Matrix.mul_one, Units.inv_mul] at this
  exact this.symm
end Uni
end GlobalTheory.RootEx.Radical
