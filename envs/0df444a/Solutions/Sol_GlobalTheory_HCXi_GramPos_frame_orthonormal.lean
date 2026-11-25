-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.frame_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:20.527617+00:00
-- url     : https://prove2.me/submissions/2f1e925b-b850-4f88-ba03-9f9d3389a388

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Theorems.Thm_GlobalTheory_HCXi_GramPos_sq_half
import Theorems.Thm_GlobalTheory_HCXi_GramPos_bvec_pair
import Theorems.Thm_GlobalTheory_HCXi_GramPos_frame_pair
import Theorems.Thm_GlobalTheory_HCXi_GramPos_pair_iso_left
import Theorems.Thm_GlobalTheory_HCXi_GramPos_pair_iso_right

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.GramPos
namespace GlobalTheory.HCXi.GramPos
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) : (frame k r)ᴴ * frame k r = 1 := by
  ext a b
  have := frame_pair k r 1 a b
  rw [Matrix.mul_one] at this
  rw [this]
  have ha := a.isLt
  have hb := b.isLt
  unfold fvec
  split_ifs with h1 h2 h2
  · rw [bvec_pair]; simp [one_apply, eI, Fin.ext_iff]
  · rw [pair_iso_right, bvec_pair, bvec_pair]
    simp only [one_apply, eI, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · rw [pair_iso_left]
    simp only [one_apply, eI, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · rw [pair_iso_right, pair_iso_left, pair_iso_left]
    simp only [one_apply, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    have e : a.val = b.val := by omega
    have h3 : ¬ (r + k = r + 0) := by omega
    have h4 : ¬ (r + 0 = r + k) := by omega
    simp only [if_pos e, h3, h4, if_true, if_false]
    linear_combination 2 * sq_half
end GlobalTheory.HCXi.GramPos
