-- Prove2me | solution 1 for GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:20:19.935078+00:00
-- url     : https://prove2.me/submissions/4a65cf73-9539-40e5-88cc-55ae74f5319e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExpStatement
import Theorems.Thm_GlobalTheory_ColLie_hasDerivAt_coeff_colSub_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a)
    (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
    HasDerivAt (fun h : ℝ => MvPolynomial.coeff m (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (MvPolynomial.coeff m (GlobalTheory.ColLie.colDer τ S R)) 0 := by
  first | exact @GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | exact GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | (intros; apply GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp <;> assumption)
end _root_.GlobalTheory.T
