-- Prove2me | solution 1 for GlobalTheory.SmGL.Placing.exists_moves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:20.560181+00:00
-- url     : https://prove2.me/submissions/8d3f52fb-953a-4151-8687-1daa09695605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
open ValuativeRel MeasureTheory
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.Placing
namespace _root_.GlobalTheory.SmGL.Placing
theorem _root_.solution {ι : Type} (e e' : ι ≃ n) :
    ∃ w : GL n R, _root_.GlobalTheory.SmGL.Placing.Moves e e' w := by
  let σ : n ≃ n := e.symm.trans e'
  refine ⟨⟨σ.symm.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, ?_, ?_⟩, fun g x y => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · simp [σ, Units.inv_mk, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
end _root_.GlobalTheory.SmGL.Placing
end GlobalTheory.SmGL.Placing
