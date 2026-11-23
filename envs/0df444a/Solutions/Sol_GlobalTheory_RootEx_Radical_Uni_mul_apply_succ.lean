-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.Uni.mul_apply_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:26.816284+00:00
-- url     : https://prove2.me/submissions/a95e6915-0c6e-4adc-adae-0e02d7ea9f4d

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
theorem _root_.solution {b : ι → ℕ} {M M' : Matrix ι ι k} (h : Uni b M) (h' : Uni b M')
    {r s : ι} (hrs : b s = b r + 1) : (M * M') r s = M r s + M' r s := by
  have e : (M * M') r s = (M * (1 : Matrix ι ι k)) r s + ((1 : Matrix ι ι k) * M') r s := by
    simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (b t) (b r) with ht | ht
    · have hts : t ≠ s := by
        rintro rfl
        omega
      rw [h r t ht, Matrix.one_apply_ne hts, mul_zero, zero_add]
    · have hrt : r ≠ t := by
        rintro rfl
        omega
      rw [h' t s (by omega), Matrix.one_apply_ne hrt, zero_mul, add_zero]
  rw [e, Matrix.mul_one, Matrix.one_mul]
end Uni
end GlobalTheory.RootEx.Radical
