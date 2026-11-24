-- Prove2me | solution 1 for GlobalTheory.DiffVanish.multiDiff_form_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:15.710096+00:00
-- url     : https://prove2.me/submissions/f127b044-e1a0-4b2f-82f2-9651eee0a303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_DiffVanish_form_apply
import Theorems.Thm_GlobalTheory_multiDiff_pow
import Theorems.Thm_GlobalTheory_pow_sub_pow_mem_pow_succ
import Theorems.Thm_GlobalTheory_diffElt_sub_sum_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
namespace DiffVanish
theorem _root_.solution {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (x : G) :
    multiDiff g (fun y ↦ h.form fun _ ↦ y) x = d.factorial • h.form g := by
  have e : ∀ S : Finset (Fin d), (h.form fun _ ↦ x - ∑ i ∈ S, g i) =
      shiftAct G M ((diffElt x - ∑ i ∈ S, diffElt (g i)) ^ d) φ 0 := fun S ↦ by
    have := h.shiftAct_eq_zero (pow_sub_pow_mem_pow_succ (diffElt_mem _)
      (Ideal.sub_mem _ (diffElt_mem x) (Ideal.sum_mem _ fun i _ ↦ diffElt_mem (g i)))
      (diffElt_sub_sum_mem S g x) d)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [← this, h.form_apply _ 0, multiDiff_eq_shiftAct]
    simp
  have := multiDiff_pow (fun i ↦ diffElt (g i)) (diffElt x)
  rw [multiDiff_apply] at this
  rw [multiDiff_apply, h.form_apply _ 0, multiDiff_eq_shiftAct, ← Pi.smul_apply,
    ← LinearMap.smul_apply, ← map_nsmul, nsmul_eq_mul, ← this, map_sum, LinearMap.sum_apply,
    Finset.sum_apply]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [e, map_zsmul, LinearMap.smul_apply, Pi.smul_apply]
end DiffVanish
end GlobalTheory
