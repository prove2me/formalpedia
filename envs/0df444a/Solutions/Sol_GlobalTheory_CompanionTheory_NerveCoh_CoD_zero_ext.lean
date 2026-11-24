-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.CoD.zero_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:01.18541+00:00
-- url     : https://prove2.me/submissions/dff9b3e6-a655-4b3a-8614-b99c320e09a0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_key

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
variable {E : Type} [Category.{0} E]
variable [Quiver.IsThin E]
variable {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R}
namespace GlobalTheory.CompanionTheory.NerveCoh
namespace CoD
theorem _root_.solution (A : CoD H B) (a : MCn H 0) (ha : mdn H 0 a = 0)
    (h0 : ∀ y, A.ev (𝟙 y) (a (pt y)) = 0) : a = 0 := by
  funext c
  refine A.ext _ fun y f ↦ ?_
  rw [A.key a ha c f, h0]
end CoD
end GlobalTheory.CompanionTheory.NerveCoh
