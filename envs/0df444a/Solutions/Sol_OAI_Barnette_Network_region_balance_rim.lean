-- Prove2me | solution 1 for OAI.Barnette.Network.region_balance_rim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:13:04.739977+00:00
-- url     : https://prove2.me/submissions/87ee0871-002c-40ba-8588-6f64d20ec1c1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Contraction.lean:L222-L255
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.region_balance_rim. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Theorems.Thm_OAI_Barnette_Network_card_star

-- ---- from OAI.Combinatorics.Hamiltonian.Network ----
namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

theorem edge_reachable (e : E) : N.graph.Reachable (N.tail e) (N.head e) := by
  by_cases h : N.tail e = N.head e
  · rw [h]
  · exact (show N.graph.Adj (N.tail e) (N.head e) from
      ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩).reachable

variable [Fintype V] [Fintype E]
attribute [local instance] OAI.Barnette.Network.instDecidableEq
attribute [local instance] OAI.Barnette.Network.instDecidableEq_1
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

end
end Barnette

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Contraction ----
namespace OAI

/-! Contraction and deletion of finite oriented dual networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma star_count (hN : N.Simple) (v : V) :
    (N.star v).card = ∑ e, ((if N.tail e = v then 1 else 0) +
      (if N.head e = v then 1 else 0)) := by
  rw [star,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne := hN.loopless e
  by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all [Incident]

lemma weighted_stars (hN : N.Simple) (f : V → ℤ) :
    ∑ v, f v * (N.star v).card = ∑ e, (f (N.tail e) + f (N.head e)) := by
  simp only [N.star_count hN,Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,Finset.mul_sum,mul_add,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [Finset.sum_add_distrib,eq_comm]

omit [Fintype V] [Fintype E] in
lemma colorSign_add (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    colorSign black (N.tail e) + colorSign black (N.head e) = 0 := by
  have he := hc e
  by_cases ht : black (N.tail e) <;> by_cases hh : black (N.head e) <;>
    simp_all [colorSign]

omit [Fintype F] in
lemma regionShore_off_edge (U : Finset F) (q : N.Regions D U) {e : E}
    (he : e ∉ D.inducedEdges U) :
    N.tail e ∈ N.regionShore D U q ↔ N.head e ∈ N.regionShore D U q := by
  simp only [N.mem_regionShore]
  have hh : (N.regions D U).componentMap (N.tail e) =
      (N.regions D U).componentMap (N.head e) :=
    SimpleGraph.ConnectedComponent.sound ((N.regions D U).edge_reachable ⟨e,he⟩)
  rw [hh]

omit [Fintype F] in
lemma region_balance_rim (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) (q : N.Regions D U) :
    3 * N.regionBalance D black U q = 2 * (N.blackRim D black U q : ℤ) - N.rim D U q := by
  let A := N.regionShore D U q
  let f : V → ℤ := fun v => if v ∈ A then colorSign black v else 0
  have hs := N.weighted_stars hN f
  have hv : ∀ v, (N.star v).card = 3 := fun v => (N.card_star hN v).trans (h3 v)
  have hleft : (∑ v, f v * (N.star v).card) = 3 * N.regionBalance D black U q := by
    simp only [hv,Nat.cast_ofNat,← Finset.sum_mul,f]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,regionBalance,A,mul_comm]
  rw [hleft] at hs
  have hreduce : (∑ e, (f (N.tail e) + f (N.head e))) =
      ∑ e ∈ D.inducedEdges U, (f (N.tail e) + f (N.head e)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have heq := N.regionShore_off_edge D U q he
    simp only [f,A,heq]
    split_ifs
    · exact N.colorSign_add black hc e
    · rfl
  rw [hreduce] at hs
  rw [hs]
  simp only [blackRim,rim,Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [f,A,colorSign]
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;>
    by_cases bt : black (N.tail e) <;> by_cases bh : black (N.head e) <;> norm_num [ht,hh,bt,bh]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.region_balance_rim := @_root_.OAI.Barnette.Network.region_balance_rim
