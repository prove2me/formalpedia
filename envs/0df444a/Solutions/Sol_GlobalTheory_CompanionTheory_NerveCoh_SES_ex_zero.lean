-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.SES.ex_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:53.454458+00:00
-- url     : https://prove2.me/submissions/88043b82-4fe1-480d-ae7e-29525986def0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.NerveCoh
namespace SES
theorem _root_.solution {A B C : Cx R} (S : SES A B C) (hB : B.Ex 0) : A.Ex 0 := by
  rw [Cx.ex_zero_iff] at hB ⊢
  intro x hx
  apply S.inj 0
  rw [map_zero]
  apply hB
  rw [← S.i.f_d, hx, map_zero]
end SES
end GlobalTheory.CompanionTheory.NerveCoh
