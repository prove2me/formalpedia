-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.boxExp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:43.895219+00:00
-- url     : https://prove2.me/submissions/2f0766b1-32ff-4396-859c-d0bbad710e5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {n n' : Type} {c : ℕ} (rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
    (h : ¬ Free 1 rs) : boxExp rs = 0 := by
  rcases rs with ⟨r | l, s | j⟩ <;> simp only [Free, boxExp] at h ⊢ <;> omega
end GlobalTheory.RootEx.UnfoldShape
