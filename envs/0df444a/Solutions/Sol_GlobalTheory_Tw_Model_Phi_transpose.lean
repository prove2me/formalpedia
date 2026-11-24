-- Prove2me | solution 1 for GlobalTheory.Tw.Model.Phi_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:56.546706+00:00
-- url     : https://prove2.me/submissions/e95dfd83-213f-45c4-9df1-5535b94b4d5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
omit [StarRing R]
namespace GlobalTheory.Tw.Model
theorem _root_.solution : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + (j : ℕ) + 1 = n
  · rw [if_pos h, if_pos (by omega)]
    have : n - 1 = i + j := by omega
    rw [this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp
  · rw [if_neg h, if_neg (by omega)]; simp
end GlobalTheory.Tw.Model
