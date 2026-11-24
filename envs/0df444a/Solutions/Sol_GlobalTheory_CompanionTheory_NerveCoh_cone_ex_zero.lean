-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.cone_ex_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:55.894069+00:00
-- url     : https://prove2.me/submissions/e84510d8-c10e-423a-881b-388922353e28

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
theorem _root_.solution {A B : Cx R} (f : Hm A B) :
    (cone f).Ex 0 ↔ ∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0 := by
  rw [Cx.ex_zero_iff]
  exact ⟨fun h a h1 h2 ↦ h a (Prod.ext h1 h2), fun h a ha ↦ h a (congrArg Prod.fst ha) (congrArg Prod.snd ha)⟩
end GlobalTheory.CompanionTheory.NerveCoh
