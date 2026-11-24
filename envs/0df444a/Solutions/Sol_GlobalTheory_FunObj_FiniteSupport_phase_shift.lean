-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.phase_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:14.989062+00:00
-- url     : https://prove2.me/submissions/01500332-8401-4542-a384-dd8e74cdca2e

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
theorem _root_.solution {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) :
    phase x (shiftVars d + e) = phase x e + ∑ j, ch (d j) := by
  have h1 : ∀ j s, rowVar x (shiftVars d + e) j s = rowVar x e j s := fun j s => by
    unfold rowVar
    split_ifs with h
    · refine Finset.sum_congr rfl fun l _ => ?_
      have := stepPt_shift hd x e ⟨j, h⟩
      dsimp only at this
      rw [this, Matrix.add_apply, (hd ⟨j, h⟩).2, add_zero]
    · rfl
  have h2 : ∀ j r, colVar x (shiftVars d + e) j r = colVar x e j r := fun j r => by
    rw [colVar, colVar, stepPt_shift hd, Matrix.add_apply, (hd j).1 _ _ (by simp [Free]), add_zero]
  have h3 : ∀ j : Fin (G.m - 1), ch (stepPt (x j) ((shiftVars d + e) j)) = ch (stepPt (x j) (e j)) + ch (d j) :=
    fun j => by rw [stepPt_shift hd]; simp [ch, Finset.sum_add_distrib]
  simp only [phase, h1, h2, h3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.FunObj.FiniteSupport
