-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.downMap_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:05.672606+00:00
-- url     : https://prove2.me/submissions/6ea2f9f2-93aa-4eef-9ce7-6d916a97fb42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_stepPt_shift

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
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {G : Grid k} (hs : 1 ≤ G.s)
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) (j : ℕ) :
    downMap hs x (shiftVars d + e) j - downMap hs x e j = if h : j < G.m - 1 then
      (d ⟨j, h⟩).reindex (frame (by have := topRank_add hs (j + 1); dsimp only; omega))
        (frame (by have := topRank_add hs j; dsimp only; omega)) else 0 := by
  unfold downMap
  split_ifs with h
  · have := stepPt_shift hd x e ⟨j, h⟩
    dsimp only at this
    rw [this]
    ext r s; simp
  · simp
  · simp
end GlobalTheory.FunObj.FiniteSupport
