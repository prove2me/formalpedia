-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.tensor_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:16:59.870355+00:00
-- url     : https://prove2.me/submissions/bd67495b-c91c-4fb5-b5e5-2efba1e73b29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_moveArgs_theta
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_moveArgs_sub
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_downMap_shift
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_transpose_mem_matLat
import Theorems.Thm_GlobalTheory_FunObj_fill_theta
import Theorems.Thm_GlobalTheory_RootEx_Supp_bd_zero


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
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (g : G.VertexGroup) (x : ColArgs G) (y : RowArgs G) (v : Vars G) {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d)
    (hb : ∀ (j : ℕ) (h : j < G.m - 1), Bd (valuation k ((ϖ ^ e : kˣ) : k)) (((g (G.m, j + 1))⁻¹).val *
      (d ⟨j, h⟩).reindex (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); dsimp only; omega))
        (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; dsimp only; omega)) * (g (G.m, j)).val)) :
    T (G.moveArgs .one g (fill hs x y (shiftVars d + v))) = T (G.moveArgs .one g (fill hs x y v)) := by
  rw [← hT.2.2 (G.moveArgs .one g (fill hs x y v))
    (G.moveArgs .one g (fill hs x y (shiftVars d + v) - fill hs x y v)), moveArgs_sub, add_sub_cancel]
  rintro (⟨i, l⟩ | ⟨i, l⟩)
  · rw [moveArgs_theta]
    refine transpose_mem_matLat _ ?_
    by_cases hi : i = G.m
    · subst hi
      rw [Pi.sub_apply, fill_theta, fill_theta, ← transpose_sub, transpose_transpose, downMap_shift hs hd]
      split_ifs with hl
      · exact hb l hl
      · simpa using bd_zero _
    · have : (fill hs x y (shiftVars d + v) - fill hs x y v) (.theta i l) = 0 := by simp [fill, hi]
      rw [this]
      simpa using bd_zero _
  · have : (fill hs x y (shiftVars d + v) - fill hs x y v) (.ex i l) = 0 := sub_self _
    simp only [Grid.moveArgs, this, Matrix.mul_zero, Matrix.zero_mul, zero_mem]
end GlobalTheory.FunObj.FiniteSupport
