-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.dm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:24.441405+00:00
-- url     : https://prove2.me/submissions/967ffaab-4f3f-46e3-af5e-c531fa88ed8f

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
theorem _root_.solution : dm (1 : Matrix (Fin n) (Fin n) R) 0 = 1 := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_ <;> by_cases h : i = j <;> simp [dm, Matrix.one_apply, h]
end GlobalTheory.Tw.CentralizerAdjoin
