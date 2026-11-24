-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.CoD.ev_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:28:16.809618+00:00
-- url     : https://prove2.me/submissions/05710086-c3d2-40f0-b8f8-3e67a6767db8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic

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
variable {C D : Type} [Category.{0} C] [Category.{0} D]
namespace GlobalTheory.CompanionTheory.NerveCoh
namespace CoD
theorem _root_.solution {E : Type} [Category.{0} E] {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R} (A : CoD H B)
    {x : E} {v w : H.obj x} (h : ∀ (y : E) (f : x ⟶ y), A.ev f v = A.ev f w) : v = w := by
  rw [← sub_eq_zero]
  exact A.ext _ fun y f ↦ by rw [map_sub, h, sub_self]
end CoD
end GlobalTheory.CompanionTheory.NerveCoh
