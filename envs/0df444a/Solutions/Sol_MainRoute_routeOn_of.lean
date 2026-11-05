-- Prove2me | solution 1 for MainRoute.routeOn_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:34.706171+00:00
-- url     : https://prove2.me/submissions/82a2daf7-6849-4f73-97db-2dd9907562ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_TwoMachines_Main
import Definitions.Def_Wrap_Main
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_GeneralPieces_ThmRunningTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_MainRoute_General
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_TwoMachines_everyTwoMachinesCanBeAlternated
import Theorems.Thm_TwoMachines_everyTwoMachinesCanBeChosenBetween
import Theorems.Thm_Wrap_lastStepsArePolynomialTime
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
namespace MainRoute
theorem _root_.solution (hVariablesAEvery : RecursionToBound.ThmVariablesAForEveryMachine) (hChoice : EveryChoiceMeetsThmVariablesB) (hTries : EveryExhaustiveMachineTriesAll) (hFront : FrontEndAndTestExist)
    (hExh : ExhaustiveMachineExists) (hAlt : EveryAlternationMeetsMinBound) (hDec : EveryAlternationDecidesWithinMinBound) (hRen : RenamingFrontEndExists) (hMain : MinBoundIsTheMainTheorem) : RouteOnEverySolver := by
  intro Idx _ S e C₀ Q hPoly num hnum
  obtain ⟨n₀, hn₀⟩ := hVariablesAEvery Idx S e C₀ Q hPoly num hnum
  refine ⟨n₀, fun a ha fm em hMex hM n₁ hn₁ => ?_⟩
  obtain ⟨hVariablesAEx, hVariablesA⟩ := hn₀ n₁ hn₁
  -- Theorem D (b) for every chosen machine, from the body of Theorem D (a)
  have hVariablesB : ∀ (Ma : TM2ComputableAux Bool Bool) (Ca : ℕ), ThmVariablesAFor S Q Ma Ca → ∀ (Mb : TM2ComputableAux Bool Bool) (cb : ℕ), TriesAllWithin Mb cb →
      ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
        ∀ (M₂ : TM2ComputableAux Bool Bool) (q₂ : ℕ), Chooses Ma Mb test pre id id id M₂ q₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂ := hChoice Idx S e C₀ Q a ha
  -- the same, for the machines built on the named function
  have hVariablesB' : ∀ M₂ : TM2ComputableAux Bool Bool, ChosenAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) (S.K (Q.idx 0)) M₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂ := by
    rintro M₂ ⟨Ma, Mb, qa, qb, q₂, pre, test, hMa, hMb, hpre, htest, hch⟩
    obtain ⟨Ca, hCa⟩ := hVariablesA Ma qa hMa
    obtain ⟨cb, hcb⟩ := hTries Mb qb hMb
    exact hVariablesB Ma Ca hCa Mb cb hcb pre test hpre htest M₂ q₂ hch
  -- existence
  have hex : ∀ post : List Bool → List Bool, PolyT post → ∃ N : TM2ComputableAux Bool Bool,
      BuiltAsPrinted (RecursionToBound.count S n₁ Q.pick num) (RecursionToBound.expo S n₁ Q.pick num) fm em (S.K (Q.idx 0)) post N := fun post hpost => by
    obtain ⟨Ma, qa, hfa, hMa⟩ := hVariablesAEx
    obtain ⟨Mb, -, qb, hfb, -, hMb⟩ := hExh
    obtain ⟨⟨pre, hpreP, hpre⟩, hT⟩ := hFront
    obtain ⟨test, htestP, htest⟩ := hT (S.K (Q.idx 0))
    obtain ⟨Ka, Kb, M₂, q₂', q₂, hf₂, hh₂, hch⟩ := everyTwoMachinesCanBeChosenBetween Ma Mb hfa hfb test pre id id id htestP hpreP PolyT.id' PolyT.id' PolyT.id'
    obtain ⟨M₁, q₁, hf₁, hM₁⟩ := hMex
    obtain ⟨ren, hrenP, hren⟩ := hRen
    obtain ⟨K₁, K₂, N, q', q, hfN, hhN, halt⟩ := everyTwoMachinesCanBeAlternated M₁ M₂ hf₁ hf₂ ren ren post post hrenP hrenP hpost hpost
    exact ⟨N, Ma, Mb, M₂, M₁, qa, qb, q₂, q₂', q₁, q, q', pre, ren, test, Ka, Kb, K₁, K₂, hfa, hfb, hf₂, hf₁, hfN, hpreP, htestP, hrenP, hMa, hMb, hpre, htest, hh₂, hch, hM₁, hren, hhN, halt⟩
  exact
    { da := hVariablesA
      variablesBFromTheBody := hVariablesB
      tries := hTries
      db := hVariablesB'
      cor := hAlt
      main := by
        rintro N ⟨M₁, M₂, q₁, q, ren, hch, hM₁, hren, halt⟩
        obtain ⟨C₂, hC₂⟩ := hVariablesB' M₂ hch
        obtain ⟨C₁, hC₁⟩ := hM M₁ q₁ hM₁
        obtain ⟨C, hC⟩ := hAlt ren hren M₁ C₁ hC₁ M₂ C₂ hC₂ N q halt
        exact ⟨C, hC, (hMain N C).1 hC⟩
      decides := by
        rintro N ⟨M₁, M₂, q₁, q, ren, hch, hM₁, hren, halt⟩
        obtain ⟨C₂, hC₂⟩ := hVariablesB' M₂ hch
        obtain ⟨C₁, hC₁⟩ := hM M₁ q₁ hM₁
        exact hDec ren hren M₁ C₁ hC₁ M₂ C₂ hC₂ N q halt
      exist := ⟨hex id PolyT.id', hex someBit lastStepsArePolynomialTime.2⟩ }
end MainRoute
