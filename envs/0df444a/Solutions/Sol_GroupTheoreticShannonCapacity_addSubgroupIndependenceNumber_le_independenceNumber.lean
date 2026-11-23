-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.addSubgroupIndependenceNumber_le_independenceNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:38:45.918059+00:00
-- url     : https://prove2.me/submissions/8693ea1f-603a-495a-ae0b-5031068e5b23

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_ge_natCard_of_independent

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {G : Type*} [AddGroup G] [Fintype G]
    (Γ : SimpleGraph G) :
    addSubgroupIndependenceNumber Γ ≤ Γ.indepNum := by
  simp only [addSubgroupIndependenceNumber]
  apply csSup_le
  · -- Nonempty: trivial subgroup
    use 1, ⊥
    constructor
    · intro u hu v hv huv
      simp only [SetLike.mem_coe, AddSubgroup.mem_bot] at hu hv
      rw [hu, hv] at huv
      exact (huv rfl).elim
    · exact AddSubgroup.card_bot
  · -- Each element in the set is ≤ independenceNumber
    intro x ⟨H, hH_indep, hH_card⟩
    rw [← hH_card]
    exact independenceNumber_ge_natCard_of_independent Γ (H : Set G) hH_indep
end GroupTheoreticShannonCapacity
