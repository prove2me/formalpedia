-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.dm_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:22.898802+00:00
-- url     : https://prove2.me/submissions/905da286-5e6b-4dc4-875a-1fcdf47e47fb

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
theorem _root_.solution (U V : Matrix (Fin n) (Fin n) R) : (dm U V).map TrivSqZeroExt.fst = U := by
  ext i j; simp [dm]
end GlobalTheory.Tw.CentralizerAdjoin
