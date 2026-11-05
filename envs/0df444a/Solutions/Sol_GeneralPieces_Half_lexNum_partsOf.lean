-- Prove2me | solution 1 for GeneralPieces.Half.lexNum_partsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:31:07.143716+00:00
-- url     : https://prove2.me/submissions/d44f8f93-b366-4723-811e-d546a741ad66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
import Theorems.Thm_GeneralPieces_Half_pairwise_partsLe
import Theorems.Thm_GeneralPieces_Half_desc_ptn
import Theorems.Thm_GeneralPieces_Half_ptn_desc
import Theorems.Thm_GeneralPieces_Half_desc_mem_partsOf
import Theorems.Thm_ClauseBound_Part_mem_partsOf
import Theorems.Thm_ClauseBound_Part_nodup_partsOf
import Theorems.Thm_GeneralPieces_Half_wt_ptn
import Theorems.Thm_GeneralPieces_Ring_mem_ptns
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution (h k : ℕ) (hk : k < (partsOf h).length) : lexNum h (ptn (partsOf h)[k]) = k := by
  have hm : ∀ L ∈ partsOf h, L.sum = h ∧ ClauseBound.Boson.Pos L ∧ L.Pairwise (· ≥ ·) := fun L hL => mem_partsOf.1 hL
  have hd : ∀ j (hj : j < (partsOf h).length), desc (ptn (partsOf h)[j]) = (partsOf h)[j] := fun j hj =>
    desc_ptn (hm _ (List.getElem_mem hj)).2.1 (hm _ (List.getElem_mem hj)).2.2
  have hlt := List.pairwise_iff_getElem.1 (pairwise_partsLe h h)
  have hset : {ν ∈ ptns h | desc ν < desc (ptn (partsOf h)[k])} = (((partsOf h).take k).map ptn).toFinset := by
    ext ν
    rw [Finset.mem_filter, List.mem_toFinset, List.mem_map, hd k hk]
    constructor
    · rintro ⟨hν, hl⟩
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem (desc_mem_partsOf hν)
      refine ⟨desc ν, List.mem_take_iff_getElem.2 ⟨j, ?_, e⟩, ptn_desc ν⟩
      rw [lt_min_iff]
      refine ⟨?_, hj⟩
      by_contra hkj
      rcases Nat.lt_or_ge k j with h1 | h1
      · have h2 : (partsOf h)[k] < (partsOf h)[j] := hlt k j hk hj h1
        rw [e] at h2
        exact lt_asymm h2 hl
      · have h2 : j = k := by omega
        subst h2
        rw [e] at hl
        exact lt_irrefl _ hl
    · rintro ⟨L, hL, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hL
      rw [lt_min_iff] at hj
      have hmj := hm _ (List.getElem_mem hj.2)
      exact ⟨(mem_ptns h _).2 (by rw [wt_ptn hmj.2.1, hmj.1]), by rw [hd j hj.2]; exact hlt j k hj.2 hk hj.1⟩
  have hnd : (((partsOf h).take k).map ptn).Nodup := by
    refine List.Nodup.map_on (fun L hL L' hL' e => ?_) ((nodup_partsOf h).sublist (List.take_sublist _ _))
    have h1 := hm L (List.mem_of_mem_take hL)
    have h2 := hm L' (List.mem_of_mem_take hL')
    rw [← desc_ptn h1.2.1 h1.2.2, e, desc_ptn h2.2.1 h2.2.2]
  rw [lexNum, hset, List.toFinset_card_of_nodup hnd, List.length_map, List.length_take, min_eq_left hk.le]
end GeneralPieces.Half
