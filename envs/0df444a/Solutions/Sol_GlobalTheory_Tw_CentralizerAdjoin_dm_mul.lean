-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.dm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:34.176344+00:00
-- url     : https://prove2.me/submissions/3315ea9b-bddb-4767-b5ca-cee79995f3dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus

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
theorem _root_.solution (U V U' V' : Matrix (Fin n) (Fin n) R) :
    dm U V * dm U' V' = dm (U * U') (U * V' + V * U') := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]
end GlobalTheory.Tw.CentralizerAdjoin
