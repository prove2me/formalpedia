-- Prove2me | solution 1 for HajnalSzemeredi.hajnal_szemeredi_of_maxDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:44.528478+00:00
-- url     : https://prove2.me/submissions/81d7ac12-778f-4702-b160-4003558b9c3d

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_HajnalSzemeredi
public import Definitions.Def_HajnalSzemeredi_Solution
public import Theorems.Thm_HajnalSzemeredi_hajnal_szemeredi

set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi
namespace HajnalSzemeredi
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : G.maxDegree < k) :
    ∃ C : G.Coloring (Fin k), ∀ i j : Fin k,
      (Finset.univ.filter fun v => C v = i).card ≤
        (Finset.univ.filter fun v => C v = j).card + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  exact hajnal_szemeredi G r fun v => Nat.lt_succ_iff.1 ((G.degree_le_maxDegree v).trans_lt hk)
end HajnalSzemeredi
