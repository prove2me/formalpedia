-- Prove2me | solution 1 for Groundwork.Grid.botW_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:11:56.692757+00:00
-- url     : https://prove2.me/submissions/f4c54453-58e9-43e5-b29c-db411e9f397a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_Code_card_dec_subsets
import Theorems.Thm_Groundwork_Code_sum_dec
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_sum_toWord
attribute [local simp] Groundwork.mem_words


section
namespace Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
private theorem val_bijOn (n : ℕ) :
    Set.BijOn (fun k : Fin n => (k : ℕ)) (univ : Finset (Fin n)) (range n : Finset ℕ) :=
  ⟨fun k _ => mem_coe.2 (mem_range.2 k.2), fun _ _ _ _ h => Fin.ext h,
    fun j hj => ⟨⟨j, mem_range.1 (mem_coe.1 hj)⟩, mem_coe.2 (mem_univ _), rfl⟩⟩
private theorem sum_powersetCard_eq_sum_range {n : ℕ} (i : ℕ) (f1 f0 : Fin n → ℤ) :
    ∑ S ∈ powersetCard i (univ : Finset (Fin n)), (∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k
      = ∑ s ∈ range (2 ^ n), if (toWord n s).count true = i then
          ∏ k : Fin n, (if (toWord n s).getD k false = true then f1 k else f0 k) else 0 := by
  rw [sum_toWord n fun τ => if τ.count true = i then
    ∏ k : Fin n, (if τ.getD k false = true then f1 k else f0 k) else 0]
  rw [powersetCard_eq_filter, sum_filter, ← (Code.subsets univ n _ (val_bijOn n)).sum_dec]
  refine sum_congr rfl fun τ hτ => ?_
  rw [Code.card_dec_subsets univ n _ (val_bijOn n) (mem_words.1 hτ)]
  split_ifs
  · rw [prod_ite, ← compl_filter]
    rfl
  · rfl
end Groundwork.Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (tr : Bool) {n : ℕ} (i c : ℕ) {x y : List Bool} (w : List Bool) (hx : x.length = n) :
    botW tr i x y w = (sideBit tr).Bot i ((Code.sparse (sideS0 tr) n c).dec w) (bitsOf n x) (bitsOf n y) := by
  subst hx
  rw [botW, BitCut.Bot, sum_powersetCard_eq_sum_range]
  refine sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [prod_range]
    exact prod_congr rfl fun k _ => rfl
  · rfl
end Groundwork.Grid
