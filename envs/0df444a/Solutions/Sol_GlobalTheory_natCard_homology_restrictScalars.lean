-- Prove2me | solution 1 for GlobalTheory.natCard_homology_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:50.116905+00:00
-- url     : https://prove2.me/submissions/51e971e5-f8c9-4b28-b5bf-889efc3fecf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  have e : (((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n ≅
      (ModuleCat.restrictScalars.{0} f).obj (D.homology n) :=
    (D.sc n).mapHomologyIso (ModuleCat.restrictScalars.{0} f)
  exact Nat.card_congr e.toLinearEquiv.toEquiv
end GlobalTheory
