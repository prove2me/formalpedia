-- Prove2me | solution 1 for MinOfBounds.alternation_outputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:45.241603+00:00
-- url     : https://prove2.me/submissions/ca137c5f-930c-450a-965d-d3abf2e9591f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_TwoMachines_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_MinOfBounds_Main
import Theorems.Thm_MinOfBounds_bothComputeTheSameNumber
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_MinOfBounds_overheadGoesIntoC
import Theorems.Thm_MinOfBounds_renamedCodeIsPolynomial
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_VariableBound_Rename_lengthEncC
import Theorems.Thm_Wrap_Outputs_mono
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution {pre : List Bool → List Bool} (hpre : RenamesTheVariablesThatOccur pre) {M₁ : TM2ComputableAux Bool Bool} {C₁ : ℕ} (h₁ : MeetsBoundInM M₁ C₁)
    {M₂ : TM2ComputableAux Bool Bool} {C₂ : ℕ} (h₂ : ThmVariablesBFor M₂ C₂) {post : List Bool → List Bool} {N : TM2ComputableAux Bool Bool} {q : ℕ} (hN : Alternates M₁ M₂ pre pre post post N q) :
    ∃ C : ℕ, ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length → 4 ≤ numOcc φ →
      Outputs N (encC k φ) (post (SatK.binary (numOcc φ) (numSatOcc φ))) (timeCor C k φ.length (numOcc φ) + C * (encC k φ).length ^ C) := by
  obtain ⟨a, ha⟩ := renamedCodeIsPolynomial
  obtain ⟨C, hC⟩ := overheadGoesIntoC C₁ C₂ q a
  refine ⟨C, fun k V φ hk hφ hm hn => ?_⟩
  obtain ⟨b₁, b₂⟩ := bothComputeTheSameNumber M₁ C₁ h₁ M₂ C₂ h₂ k V φ hk hφ hm hn
  rw [← hpre k V φ hk hφ] at b₁ b₂
  have hL : 1 ≤ (encC k φ).length := by
    rw [VariableBound.Rename.lengthEncC]
    omega
  refine Outputs.mono (hN (encC k φ) _ _ _ _ b₁ b₂ rfl) ?_
  rw [hpre k V φ hk hφ]
  exact hC k φ.length (numOcc φ) (encC k φ).length (renamedCode k φ).length hk hm hn hL (ha k V φ hk hφ)
end MinOfBounds
