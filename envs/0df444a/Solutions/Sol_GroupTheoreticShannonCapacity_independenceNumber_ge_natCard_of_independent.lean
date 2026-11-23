-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.independenceNumber_ge_natCard_of_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:37.007099+00:00
-- url     : https://prove2.me/submissions/3efd15a2-49e7-419b-895c-236a082d34af

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_ge_card_of_independent

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) [Fintype V]
    (S : Set V) (hS : G.IsIndepSet S) :
    G.indepNum ≥ Nat.card S := by
  classical
  have hfin : S.Finite := Set.toFinite S
  have hS' : G.IsIndepSet ((hfin.toFinset) : Set V) := by
    apply (SimpleGraph.isIndepSet_iff G).2
    intro u hu v hv huv
    have hu' : u ∈ S := by simpa [Set.Finite.mem_toFinset] using hu
    have hv' : v ∈ S := by simpa [Set.Finite.mem_toFinset] using hv
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS
    exact hpair hu' hv' huv
  have h := independenceNumber_ge_card_of_independent G hfin.toFinset hS'
  simp only [Set.Finite.card_toFinset] at h
  have hcard : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  rw [hcard]
  exact h
end GroupTheoreticShannonCapacity
