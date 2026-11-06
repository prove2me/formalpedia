-- Prove2me | solution 1 for NamesInOrder.onEverySolver_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:49:16.589743+00:00
-- url     : https://prove2.me/submissions/7a8ac73b-05a3-4b1c-95ae-99d44a265186

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
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_TwoMachines_everyTwoMachinesCanBeAlternated
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound MainRoute
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution (hBoth : BothBoundsOnEverySolver) (hAlone : BoundInMWithoutThePolynomial) (hAlt : EveryDirectAlternationMeetsTheBound) : OnEverySolver := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀, hn₀⟩ := hBoth Idx S e C₀ Q hS num hnum
  refine ⟨n₀, fun a ha n₁ hn₁ => ?_⟩
  obtain ⟨hM, hR⟩ := hn₀ a ha
  have R := hR n₁ hn₁
  have hM' : ∀ (M₁ : TM2ComputableAux Bool Bool) (q₁ : ℕ), Computes M₁ (AM S Q.pick) (eM S Q.pick) q₁ → ∃ C₁ : ℕ, MeetsBoundInMAlone M₁ C₁ := fun M₁ q₁ h => by
    obtain ⟨C, hC⟩ := hM M₁ q₁ h
    exact hAlone M₁ C hC
  refine ⟨hM', ?_, ?_⟩
  · rintro N ⟨M₁, M₂, q₁, q, hch, hM₁, halt⟩
    obtain ⟨C₂, hC₂⟩ := R.db M₂ hch
    obtain ⟨C₁, hC₁⟩ := hM' M₁ q₁ hM₁
    exact hAlt M₁ C₁ hC₁ M₂ C₂ hC₂ N q halt
  · obtain ⟨-, Ma, Mb, M₂, M₁, qa, qb, q₂, q₂', q₁, -, -, pre, -, test, Ka, Kb, -, -, hfa, hfb, hf₂, hf₁, -, hpreP, htestP, -, hMa, hMb, hpre, htest, hh₂, hch, hM₁, -⟩ := R.exist.1
    obtain ⟨K₁, K₂, N, q', q, hfN, hhN, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ id id id id PolyT.id' PolyT.id' PolyT.id' PolyT.id'
    exact ⟨N, Ma, Mb, M₂, M₁, qa, qb, q₂, q₂', q₁, q, q', pre, test, Ka, Kb, K₁, K₂, hfa, hfb, hf₂, hf₁, hfN, hpreP, htestP, hMa, hMb, hpre, htest, hh₂, hch, hM₁, hhN, halt⟩
end NamesInOrder
