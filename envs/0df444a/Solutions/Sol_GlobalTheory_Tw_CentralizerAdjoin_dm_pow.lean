-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.dm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:16.648678+00:00
-- url     : https://prove2.me/submissions/7f05d11d-fe6f-4658-ab4d-4f8fbf573233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_dm_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R]
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (k : ℕ) :
    dm N g ^ (k + 1) = dm (N ^ (k + 1)) (((k + 1 : ℕ) : R) • (N ^ k * g)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, dm_mul]
    congr 1
    rw [Matrix.smul_mul, Matrix.mul_assoc (N ^ k) g N, hc, ← Matrix.mul_assoc, ← pow_succ]
    rw [show (((k + 1 + 1 : ℕ) : R)) = ((k + 1 : ℕ) : R) + 1 by push_cast; ring, add_smul, one_smul]
    abel
end GlobalTheory.Tw.CentralizerAdjoin
