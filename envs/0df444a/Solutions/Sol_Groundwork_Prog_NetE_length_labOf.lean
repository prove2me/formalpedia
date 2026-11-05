-- Prove2me | solution 1 for Groundwork.Prog.NetE.length_labOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:52.416412+00:00
-- url     : https://prove2.me/submissions/24279686-a38f-47d1-b02f-57ceefbcac18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_Prog_NetE_mem_members
import Theorems.Thm_Groundwork_Prog_NetE_cap_symm
import Theorems.Thm_Groundwork_Prog_NetE_length_lAt
import Theorems.Thm_Groundwork_Prog_NetE_mem_prs

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β)
    {a b : ℕ} (ha : a ∈ members K g x G) (hb : b < g) (hc : col K x b ≠ G) :
    (labOf K g Np ((c, x), (G.val, List.ofFn θ)) a b).length = Np.cap c a b := by
  have hK : 0 < K := G.pos
  have hG' : col K x b < K := Nat.mod_lt _ hK
  have hbm : b ∈ members K g x (col K x b) := (mem_members K g).2 ⟨hb, rfl⟩
  have hget : (List.ofFn θ).getD (col K x b) [] = θ ⟨col K x b, hG'⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hG']; rfl
  have hlen : ((List.ofFn θ).getD (col K x b) []).length = β := by
    rw [hget]; exact hθ _ fun h => hc (congrArg Fin.val h)
  unfold labOf
  by_cases hlt : G.val < col K x b
  · rw [if_pos hlt]
    exact length_lAt (mem_prs ha hbm) (by rw [hlen]; exact hβ _ G.2 _ hG' (Ne.symm hc))
  · rw [if_neg hlt]
    rw [length_lAt (mem_prs hbm ha) (by rw [hlen]; exact hβ _ hG' _ G.2 hc)]
    exact cap_symm hN hS ⟨b, hb⟩ ⟨a, ((mem_members K g).1 ha).1⟩
end Groundwork.Prog.NetE
