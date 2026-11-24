-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.CoD.uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:38.495049+00:00
-- url     : https://prove2.me/submissions/0501a2b8-fe7b-42dd-b480-03405aea1b75

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_zero_ext

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
theorem _root_.solution (A : CoD H B) (p q : MCn H 0) (hp : mdn H 0 p = 0) (hq : mdn H 0 q = 0)
    (h : ∀ y, A.ev (𝟙 y) (p (pt y)) = A.ev (𝟙 y) (q (pt y))) : p = q := by
  rw [← sub_eq_zero]
  refine A.zero_ext _ (by rw [map_sub, hp, hq, sub_self]) fun y ↦ ?_
  rw [Pi.sub_apply, map_sub, h, sub_self]
end CoD
end GlobalTheory.CompanionTheory.NerveCoh
