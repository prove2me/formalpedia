-- Prove2me | solution 1 for GlobalTheory.CharFormDeriv.norm_iteratedFDeriv_rem_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:09.194239+00:00
-- url     : https://prove2.me/submissions/1ed25124-e845-40b1-9904-95715eb61360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Theorems.Thm_GlobalTheory_CharFormDeriv_norm_iteratedDeriv_rem_le
import Theorems.Thm_GlobalTheory_CharFormDeriv_contDiff_rem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => rem t (L x)) x‖ ≤ 3 * |t| * (1 + ‖L‖ * ‖x‖) ^ 2 * ‖L‖ ^ i := by
  have h := L.iteratedFDeriv_comp_right (contDiff_rem t) x (i := i) (by exact_mod_cast le_top)
  have e : (fun x => rem t (L x)) = rem t ∘ ⇑L := rfl
  rw [e, h]
  calc _ ≤ ‖iteratedFDeriv ℝ i (rem t) (L x)‖ * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedDeriv i (rem t) (L x)‖ * ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; simp
    _ ≤ 3 * |t| * (1 + |L x|) ^ 2 * ‖L‖ ^ i := by
        gcongr; exact norm_iteratedDeriv_rem_le ht0 ht1 i (L x)
    _ ≤ 3 * |t| * (1 + ‖L‖ * ‖x‖) ^ 2 * ‖L‖ ^ i := by
        gcongr; rw [← Real.norm_eq_abs]; exact L.le_opNorm x
end GlobalTheory.CharFormDeriv
