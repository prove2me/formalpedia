-- Prove2me | solution 1 for GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:49.914694+00:00
-- url     : https://prove2.me/submissions/a06c875d-7a01-47bc-8108-38f8a183393b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Theorems.Thm_GlobalTheory_sum_zeta_pow_le
import Theorems.Thm_GlobalTheory_ncard_ideal_absNorm_eq_le
import Theorems.Thm_GlobalTheory_exists_ideal_in_class_of_norm_le_sqrt_discr
import Theorems.Thm_GlobalTheory_one_le_sqrt_abs_discr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (finrank ℚ K - 1) := by
  classical
  set X := √|(discr K : ℝ)| with hXdef
  have hX : 1 ≤ X := one_le_sqrt_abs_discr K
  refine le_trans ?_ (sum_zeta_pow_le (k := finrank ℚ K) finrank_pos hX)
  rw [Nat.cast_le]
  choose g hg hN using exists_ideal_in_class_of_norm_le_sqrt_discr K
  have hginj : Function.Injective fun C => (g C : Ideal (𝓞 K)) := by
    intro C D h
    rw [← hg C, ← hg D, Subtype.ext h]
  rw [classNumber, ← card_univ, card_eq_sum_card_fiberwise
    (f := fun C => Ideal.absNorm (g C : Ideal (𝓞 K))) (t := Ioc 0 ⌊X⌋₊)]
  · refine sum_le_sum fun n hn => le_trans ?_ (ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn (fun C => (g C : Ideal (𝓞 K)))
      (fun C hC => by simpa using hC) hginj.injOn (Ideal.finite_setOfPred_absNorm_eq n)
  · intro C _
    rw [mem_coe, mem_Ioc]
    exact ⟨Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors _),
      Nat.le_floor (hN C)⟩
end GlobalTheory
