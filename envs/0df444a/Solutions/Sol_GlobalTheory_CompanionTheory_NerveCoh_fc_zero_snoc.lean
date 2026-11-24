-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.fc_zero_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:11.496527+00:00
-- url     : https://prove2.me/submissions/04c53b58-9bf8-4ff2-9b7b-ba63fde72e5f

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
variable {E : Type} [Category.{0} E]
variable [Quiver.IsThin E]
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution (c : Fin 1 ⥤ E) (y : E) (f : c.obj (Fin.last 0) ⟶ y) : fc 0 (snoc c y f) = pt y :=
  chain_ext fun k ↦ by
    show (snoc c y f).obj (Fin.succAbove 0 k) = y
    have : Fin.succAbove 0 k = Fin.last 1 := by
      rw [Fin.fin_one_eq_zero k]; rfl
    rw [this, snoc_obj_last]
end GlobalTheory.CompanionTheory.NerveCoh
