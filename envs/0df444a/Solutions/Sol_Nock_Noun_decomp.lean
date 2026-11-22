-- Prove2me | solution 1 for Nock.Noun.decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:32.08883+00:00
-- url     : https://prove2.me/submissions/7ba152d3-7c3c-4de6-8a13-0509e3e78ae1

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Theorems.Thm_Nock_Noun_one_le_leaves


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution (n nL nR : Noun) (lam : ℕ) :
    (∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ lam = p.1 + p.2 ∧
        nL.leaves = p.1 ∧ nR.leaves = p.2 ∧ n = Noun.cell nL nR)
      ↔ (n = Noun.cell nL nR ∧ n.leaves = lam) := by
  constructor
  · rintro ⟨p, ⟨_, _, hsum, hL, hR, hcons⟩, _⟩
    refine ⟨hcons, ?_⟩
    subst hcons
    simp only [Noun.leaves]
    omega
  · rintro ⟨hcons, hlen⟩
    refine ⟨(nL.leaves, nR.leaves),
      ⟨nL.one_le_leaves, nR.one_le_leaves, ?_, rfl, rfl, hcons⟩, ?_⟩
    · subst hcons; simp only [Noun.leaves] at hlen; omega
    · rintro q ⟨_, _, _, hqL, hqR, _⟩
      exact Prod.ext_iff.mpr ⟨hqL.symm, hqR.symm⟩
end Nock.Noun
