-- Prove2me | solution 1 for Groundwork.Prog.NetE.validB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:02:32.714726+00:00
-- url     : https://prove2.me/submissions/451ab061-509e-406b-8ae9-fe1e3133fcb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_getD_ofFn
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (c : C) (x β : ℕ) (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    validB K g Np ((c, x), (G.val, List.ofFn θ)) = true ↔
      ∀ G' : Fin K, G' ≠ G → θ G' ∈ mD K g Np c x β (min G G') (max G G') := by
  rw [validB, List.all_eq_true]
  constructor
  · intro h G' hne
    have h1 := h G'.val (List.mem_range.2 G'.2)
    rw [Bool.or_eq_true, beq_iff_eq, getD_ofFn] at h1
    have h2 := h1.resolve_left fun e => hne (Fin.ext e)
    rw [mD, mem_filter, mem_words]
    exact ⟨hθ G' hne, h2⟩
  · intro h G' hG'
    have hG'' := List.mem_range.1 hG'
    rw [Bool.or_eq_true, beq_iff_eq]
    by_cases e : G' = G.val
    · exact .inl e
    · right
      have h1 := h ⟨G', hG''⟩ fun e' => e (congrArg Fin.val e')
      rw [mD, mem_filter] at h1
      rw [← getD_ofFn θ ⟨G', hG''⟩] at h1
      exact h1.2
end Groundwork.Prog.NetE
