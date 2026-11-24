-- Prove2me | solution 1 for GlobalTheory.T.natCard_homology_restrictScalars_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:33.216578+00:00
-- url     : https://prove2.me/submissions/e0173804-bce4-4eb6-b781-5488e21d8630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyRestrictScalars
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyRestrictScalarsStatement
import Theorems.Thm_GlobalTheory_natCard_homology_restrictScalars


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ), Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  first | exact @GlobalTheory.natCard_homology_restrictScalars | exact GlobalTheory.natCard_homology_restrictScalars | (intros; apply GlobalTheory.natCard_homology_restrictScalars <;> assumption)
end _root_.GlobalTheory.T
