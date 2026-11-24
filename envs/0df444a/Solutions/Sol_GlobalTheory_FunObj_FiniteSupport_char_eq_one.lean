-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.char_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:43.610338+00:00
-- url     : https://prove2.me/submissions/8b82bb91-892d-48f4-ba4b-360a5e1cefae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_phase_shift
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {G : Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
  [ν.IsAddHaarMeasure]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {S : G.Args → ℂ} {x : ColArgs G} {y : RowArgs G} (hne : flatTensor hs ψ ν S x y ≠ 0)
    {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (hS : ∀ e, S (fill hs x y (shiftVars d + e)) = S (fill hs x y e)) :
    ψ (∑ j, ch (d j)) = 1 := by
  classical
  haveI := secondCountable k
  haveI : (varsVol G ν).IsAddLeftInvariant := by unfold varsVol; infer_instance
  have key := integral_add_left_eq_self (μ := varsVol G ν) (flatIntegrand hs ψ S x y) (shiftVars d)
  simp only [flatIntegrand, hS, phase_shift hd, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← mul_assoc] at key
  rw [integral_mul_const] at key
  have h1 : (ψ (-∑ j, ch (d j)) : ℂ) = 1 := by
    apply mul_left_cancel₀ hne
    rw [mul_one]
    exact key
  have h2 : ψ (-∑ j, ch (d j)) = 1 := Circle.coe_eq_one.1 h1
  rwa [AddChar.map_neg_eq_inv, inv_eq_one] at h2
end GlobalTheory.FunObj.FiniteSupport
