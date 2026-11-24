-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAntipode.Tm_op_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:38.112978+00:00
-- url     : https://prove2.me/submissions/0d17f704-91d9-405f-856e-ac68820752b2

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAntipode
namespace GlobalTheory.CompanionTheory.CapelliAntipode
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ)
    (i j : Fin n) :
    Tm (fun i j => MulOpposite.op (-X i j)) w i j = MulOpposite.op (-(Tm X (-w) i j)) := by
  unfold Tm
  by_cases h : i = j
  · simp [h, MulOpposite.algebraMap_apply, add_comm]
  · simp [h]
end GlobalTheory.CompanionTheory.CapelliAntipode
