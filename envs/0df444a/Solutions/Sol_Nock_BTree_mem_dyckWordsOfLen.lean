-- Prove2me | solution 1 for Nock.BTree.mem_dyckWordsOfLen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:18.572133+00:00
-- url     : https://prove2.me/submissions/c9cb4314-6f7a-4b30-8949-f795fdea348d

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Theorems.Thm_Nock_BTree_dyck_encode
public import Theorems.Thm_Nock_BTree_exists_encode_of_dyck
public import Theorems.Thm_Nock_BTree_size_eq

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree
namespace Nock.BTree
theorem _root_.solution {lam : ℕ} {w : List Bool} :
    w ∈ dyckWordsOfLen lam ↔ Dyck w ∧ w.length = 2 * lam := by
  simp only [dyckWordsOfLen, Finset.mem_map, Function.Embedding.coeFn_mk,
    BinaryTree.mem_treesOfNumNodesEq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨dyck_encode _, ?_⟩
    have hlen := encode_length_add_one (ofBin t)
    have hsz := size_eq (ofBin t)
    rw [toBin_ofBin, ht] at hsz
    omega
  · rintro ⟨hd, hlen⟩
    obtain ⟨s, hs⟩ := exists_encode_of_dyck hd
    refine ⟨toBin s, ?_, ?_⟩
    · have hlen' := encode_length_add_one s
      have hsz := size_eq s
      rw [hs, hlen] at hlen'
      omega
    · rw [ofBin_toBin, hs]
end Nock.BTree
