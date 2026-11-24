-- Prove2me | solution 1 for GlobalTheory.T.quantum_det_opposite_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:21:10.682129+00:00
-- url     : https://prove2.me/submissions/dd4a1e9e-83db-4975-8451-30f289a29b75

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_unop_qdet_op_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X → ∀ v : ℂ, MulOpposite.unop (Formalism.REAL.qdet (fun i j => MulOpposite.op (-X i j)) v) = ((-1 : ℂ) ^ n) • Formalism.REAL.qdet X ((n : ℂ) - 1 - v) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | exact GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | (intros; apply GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg <;> assumption)
end _root_.GlobalTheory.T
