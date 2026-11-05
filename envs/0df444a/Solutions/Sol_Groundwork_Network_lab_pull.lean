-- Prove2me | solution 1 for Groundwork.Network.lab_pull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:14:59.063438+00:00
-- url     : https://prove2.me/submissions/db69c619-40c5-41ae-bacc-1fda1ef69912

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Definitions.Def_StepMachines_Math_Pull
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Network
variable {J σ τ : Type*}
variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))
namespace Groundwork.Network
theorem _root_.solution {P B : ℕ} (h : N.Sized P B) (a b : J) : (N.pull n cs cl).lab a b = words (N.c a b) := by
  simp only [lab, pull]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hab, max_eq_left hab, h.c_symm]
end Groundwork.Network
