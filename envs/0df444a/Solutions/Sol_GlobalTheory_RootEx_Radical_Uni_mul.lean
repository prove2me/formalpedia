-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.Uni.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:18.467897+00:00
-- url     : https://prove2.me/submissions/671cbe92-3426-44d7-a643-d3d4f7c87ed3

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
theorem _root_.solution {b : ι → ℕ} {M M' : Matrix ι ι k} (h : Uni b M) (h' : Uni b M') :
    Uni b (M * M') := by
  intro r s hrs
  have : (M * M') r s = ((1 : Matrix ι ι k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b t) (b r) with ht | ht
    · rw [h r t ht]
    · rw [h'.blockTri (show b s < b t from lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul, h' r s hrs]
end Uni
end GlobalTheory.RootEx.Radical
