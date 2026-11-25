-- Prove2me | solution 1 for GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:05.670891+00:00
-- url     : https://prove2.me/submissions/26c14d97-f9bb-4765-88a1-c6b1bd9f835a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_entry
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_bvec_pair
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_fvec_castSucc
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_fvec_last
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_half
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_star_isoVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.FrameOrth
namespace GlobalTheory.HCXi.FrameOrth
theorem _root_.solution : ∀ k r : ℕ, 1 ≤ k →
    (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  intro k r hk
  constructor
  · rw [← Matrix.mul_one (frame k r)ᴴ]
    ext a b
    rw [entry]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp only [fvec_last, fvec_castSucc, star_isoVec] <;>
      simp only [isoVec, Matrix.mulVec_smul, Matrix.mulVec_add, dotProduct_smul, smul_dotProduct,
        add_dotProduct, dotProduct_add, bvec_pair, smul_eq_mul]
    · have h : wI k r 0 ≠ wI k r (Fin.last k) := by
        simp only [wI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, Matrix.one_apply_eq,
        Matrix.one_apply_eq, Matrix.one_apply_eq]
      linear_combination half
    · rename_i b
      have := b.isLt
      rw [Matrix.one_apply_ne, Matrix.one_apply_ne, Matrix.one_apply_ne]
      · simp
      all_goals simp only [wI, eI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last, Fin.val_castSucc]; omega
    · rename_i b
      have := b.isLt
      rw [Matrix.one_apply_ne, Matrix.one_apply_ne, Matrix.one_apply_ne]
      · simp
      all_goals simp only [wI, eI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last, Fin.val_castSucc]; omega
    · simp [Matrix.one_apply, eI, Fin.ext_iff]
  · ext a b
    rw [entry]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp only [fvec_last, fvec_castSucc, star_isoVec] <;>
      simp only [isoVec, Matrix.mulVec_smul, Matrix.mulVec_add, dotProduct_smul, smul_dotProduct,
        add_dotProduct, dotProduct_add, bvec_pair, smul_eq_mul, Matrix.zero_apply]
    · have h1 : Hpk k r (wI k r 0) (wI k r 0) = 1 := by
        unfold Hpk
        have e : (wI k r 0).val = r := by simp [wI]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_neg (by omega)]
      have h2 : Hpk k r (wI k r 0) (wI k r (Fin.last k)) = 0 := by
        simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        split_ifs <;> first | rfl | omega
      have h3 : Hpk k r (wI k r (Fin.last k)) (wI k r 0) = 0 := by
        simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        split_ifs <;> first | rfl | omega
      have h4 : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 := by
        unfold Hpk
        have e : (wI k r (Fin.last k)).val = r + k := by simp [wI]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos e]
      rw [h1, h2, h3, h4]
      ring
    · rename_i b
      have := b.isLt
      have h1 : ∀ j, Hpk k r (wI k r j) (eI k r b) = 0 := by
        intro j
        have := j.isLt
        simp only [Hpk, wI, eI, Fin.ext_iff]
        split_ifs <;> first | rfl | omega
      rw [h1, h1]
      ring
    · rename_i b
      have := b.isLt
      have h1 : ∀ j, Hpk k r (eI k r b) (wI k r j) = 0 := by
        intro j
        have := j.isLt
        simp only [Hpk, wI, eI, Fin.ext_iff]
        split_ifs <;> first | rfl | omega
      rw [h1, h1]
      ring
    · rename_i a b
      have := a.isLt
      have := b.isLt
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
end GlobalTheory.HCXi.FrameOrth
