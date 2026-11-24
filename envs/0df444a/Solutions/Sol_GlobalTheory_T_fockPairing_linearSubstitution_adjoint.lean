-- Prove2me | solution 1 for GlobalTheory.T.fockPairing_linearSubstitution_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:13.094813+00:00
-- url     : https://prove2.me/submissions/1a638baa-1ae4-4fd8-90c0-30c75f354abd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjointStatement
import Theorems.Thm_GlobalTheory_MinorFrame_fockS_rsub_adj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' = Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  first | exact @GlobalTheory.MinorFrame.fockS_rsub_adj | exact GlobalTheory.MinorFrame.fockS_rsub_adj | (intros; apply GlobalTheory.MinorFrame.fockS_rsub_adj <;> assumption)
end _root_.GlobalTheory.T
