-- Prove2me | solution 1 for GlobalTheory.T.thetaRecognition_lattice_iso_and_terms_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:19.096919+00:00
-- url     : https://prove2.me/submissions/ac53123b-e996-4110-b3e9-5afea23a0cb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLatticeIsoAndTermsAgree
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLatticeIsoAndTermsAgreeStatement
import Theorems.Thm_GlobalTheory_MatchTerm_main
import Theorems.Thm_GlobalTheory_PsiQuadratic_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  first | exact @GlobalTheory.MatchTerm.main | exact GlobalTheory.MatchTerm.main | (intros; apply GlobalTheory.MatchTerm.main <;> assumption)
end _root_.GlobalTheory.T
