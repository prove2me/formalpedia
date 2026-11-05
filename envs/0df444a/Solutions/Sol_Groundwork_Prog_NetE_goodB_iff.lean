-- Prove2me | solution 1 for Groundwork.Prog.NetE.goodB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:37.809259+00:00
-- url     : https://prove2.me/submissions/b03eb9fc-7015-4f95-b9e4-a56b4c1bd40b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_length_members
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_eq
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hK : 0 < K) (hN : Np.Presents c N t S) (x : ℕ) :
    goodB K g Np (c, x) = true ↔ (∀ G : Fin K, K * #{a : Fin g | chi hK x a = G} < 2 * g) ∧
      ∀ G G' : Fin K, G ≠ G' → (N.merge (chi hK x) [] []).c G G' ≤ betaC K g Np c := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun G => ?_, fun G G' hne => ?_⟩
    · rw [← length_members]; exact h1 G.val G.2
    · rw [← lbLen_eq Np hK hN x hne]
      exact (h2 G.val G.2 G'.val G'.2).resolve_left fun e => hne (Fin.ext e)
  · rintro ⟨h1, h2⟩
    refine ⟨fun G hG => ?_, fun G hG G' hG' => ?_⟩
    · rw [length_members hK x ⟨G, hG⟩]; exact h1 _
    · by_cases e : G = G'
      · exact .inl e
      · right
        have hne : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e' => e (congrArg Fin.val e')
        rw [lbLen_eq Np hK hN x hne]
        exact h2 _ _ hne
end Groundwork.Prog.NetE
