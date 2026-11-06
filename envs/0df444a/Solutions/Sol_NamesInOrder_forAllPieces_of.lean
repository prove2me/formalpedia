-- Prove2me | solution 1 for NamesInOrder.forAllPieces_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:42:58.655471+00:00
-- url     : https://prove2.me/submissions/d8ec9ced-6c1c-4199-88fc-7bd87feda79b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_MainRoute_General
import Definitions.Def_MainRoute_EveryMachine
import Definitions.Def_TwoMachines_Main
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Main
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_NamesInOrder_Chain
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_GeneralPieces_x_Of_ge_2a558e3f9765
import Theorems.Thm_VariableBound_Net_Main_val


set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution (hOn : OnEverySolver) (hPairs : ThePairsSatisfyTheHypothesis) (hTheta : ThetaOfThePairs) : ForAllPieces := by
  intro c P₀ A val h
  obtain ⟨C₀, Cp, H⟩ := hPairs c
  obtain ⟨Q, hPoly, hK, hpick, hnum, -⟩ := H P₀ A val h.1
  obtain ⟨n₀, hn₀⟩ := hOn _ _ _ C₀ Q hPoly fractionHalf hnum
  refine ⟨n₀, fun n₁ hn₁ => ?_⟩
  have hθ : ∀ l : ℕ, Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c) l ≤ ((3 * GeneralPieces.x₀Of c + 6 : ℕ) : ℝ) / Real.sqrt (lg ((RecursionWithPieces.solverAB P₀ val c).K (Q.idx l))) := fun l => by
    rw [hK l]
    obtain ⟨-, -, -, -, -, t6⟩ := hTheta (GeneralPieces.x₀Of c) l (GeneralPieces.x₀Of_ge c)
    refine t6.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have hx : (0 : ℝ) ≤ (GeneralPieces.x₀Of c : ℝ) := Nat.cast_nonneg _
    have hs : Real.sqrt (3 * (GeneralPieces.x₀Of c : ℝ) + 6) ≤ 3 * (GeneralPieces.x₀Of c : ℝ) + 6 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hs0 := Real.sqrt_nonneg (3 * (GeneralPieces.x₀Of c : ℝ) + 6)
    push_cast
    linarith
  obtain ⟨r1, r2, r3⟩ := hn₀ (3 * GeneralPieces.x₀Of c + 6) hθ n₁ hn₁
  rw [hpick] at r1 r2 r3
  rw [hK 0] at r2 r3
  exact ⟨r1, r2, r3⟩
end NamesInOrder
