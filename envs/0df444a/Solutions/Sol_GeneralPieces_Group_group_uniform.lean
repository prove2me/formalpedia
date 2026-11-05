-- Prove2me | solution 1 for GeneralPieces.Group.group_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:08.786679+00:00
-- url     : https://prove2.me/submissions/0925b521-440c-43f1-bf36-03b949b8c124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_ClauseBound_Group_Grouping_card_cls
import Theorems.Thm_ClauseBound_Group_Grouping_card_filter_le_of_fibers
import Theorems.Thm_ClauseBound_Group_Grouping_exists_perm_sets
import Theorems.Thm_ClauseBound_Group_Grouping_fiber_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (γ : Fin K) (Q : Finset (Fin (K * n)) → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : (#{A ∈ powersetCard n (univ : Finset (Fin (K * n))) | Q A} : ℝ) ≤ ε * #(powersetCard n (univ : Finset (Fin (K * n))))) :
    (#{e : Equiv.Perm (Fin (K * n)) | Q (cls e γ)} : ℝ) ≤ ε * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  refine card_filter_le_of_fibers univ (fun e => cls e γ) (powersetCard n univ)
    (fun e _ => mem_powersetCard.2 ⟨subset_univ _, card_cls e γ⟩) (fun A' hA' A'' hA'' => ?_) Q ε hQ
  obtain ⟨p, -, hp⟩ := exists_perm_sets ∅ A' A'' (disjoint_empty_left _) (disjoint_empty_left _)
    (by rw [(mem_powersetCard.1 hA').2, (mem_powersetCard.1 hA'').2])
  exact fiber_le univ p (fun _ _ => mem_univ _) γ A' A'' hp
end GeneralPieces.Group
