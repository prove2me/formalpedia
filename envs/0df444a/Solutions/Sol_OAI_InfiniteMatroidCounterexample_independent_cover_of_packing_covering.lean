-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.independent_cover_of_packing_covering
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:56:40.21476+00:00
-- url     : https://prove2.me/submissions/3085c1ac-8969-4163-8d5e-d89d2cfe7ba5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/PackingCovering.lean:L34-L57
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.independent_cover_of_packing_covering. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_TransfiniteConstruction
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_RankDescent

-- ---- from OAI.Combinatorics.InfiniteMatroid.PackingCovering ----
namespace OAI

section
open Set Matroid
namespace InfiniteMatroidCounterexample

lemma contraction_indep_compl_spanning {α : Type*} (M : Matroid α) (hM : M.dual = M)
    {C I : Set α} (hI : (contractOnto M C).Indep I) :
    (M ↾ C).Spanning (C \ I) := by
  unfold contractOnto at hI
  rw [hM] at hI
  have h : (M ↾ C).Coindep I := hI
  simpa only [Matroid.restrict_ground_eq] using h.compl_spanning

lemma spanning_union_of_restrictions {α : Type*} (M : Matroid α) (hE : M.E = univ)
    {P C S T : Set α} (hPC : P ∪ C = univ) (hSP : S ⊆ P) (hTC : T ⊆ C)
    (hS : (M ↾ P).Spanning S) (hT : (M ↾ C).Spanning T) : M.Spanning (S ∪ T) := by
  apply (M.spanning_iff_ground_subset_closure (by rw [hE]; exact subset_univ _)).mpr
  have hPg : P ⊆ M.E := by rw [hE]; exact subset_univ _
  have hCg : C ⊆ M.E := by rw [hE]; exact subset_univ _
  have hp := (M.restrict_spanning_iff hSP hPg).mp hS
  have hc := (M.restrict_spanning_iff hTC hCg).mp hT
  rw [hE,←hPC]
  exact union_subset (hp.trans (M.closure_mono subset_union_left))
    (hc.trans (M.closure_mono subset_union_right))

lemma indep_compl_of_selfDual_spanning {α : Type*} (M : Matroid α) (hE : M.E = univ)
    (hM : M.dual = M) {A : Set α} (hA : M.Spanning A) : M.Indep Aᶜ := by
  have h : M.dual.Indep (M.E \ A) := hA.compl_coindep
  simpa only [hM,hE,← Set.compl_eq_univ_sdiff] using h

/-- The mixed packing/covering reduction, not merely the two pure cases. -/
lemma independent_cover_of_packing_covering {α : Type*} (M₀ M₁ : Matroid α)
    (hE₀ : M₀.E = univ) (hE₁ : M₁.E = univ) (hM₀ : M₀.dual = M₀) (hM₁ : M₁.dual = M₁)
    (h : HasPackingCovering M₀ M₁) :
    ∃ J₀ J₁ : Set α, M₀.Indep J₀ ∧ M₁.Indep J₁ ∧ J₀ ∪ J₁ = univ := by
  classical
  obtain ⟨P,C,S₀,S₁,I₀,I₁,hdPC,hPC,_,hS₀P,hS₁P,hdS,hS₀,hS₁,_,_,hI₀,hI₁,hIC⟩ := h
  have hPC' : P ∪ C = univ := hPC.trans hE₀
  have hT₀ := contraction_indep_compl_spanning M₀ hM₀ hI₀
  have hT₁ := contraction_indep_compl_spanning M₁ hM₁ hI₁
  have hA₀ := spanning_union_of_restrictions M₀ hE₀ hPC' hS₀P sdiff_subset hS₀ hT₀
  have hA₁ := spanning_union_of_restrictions M₁ hE₁ hPC' hS₁P sdiff_subset hS₁ hT₁
  have hd : Disjoint (S₀ ∪ (C \ I₀)) (S₁ ∪ (C \ I₁)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact Set.disjoint_left.mp hdS hx hy
    · exact Set.disjoint_left.mp hdPC (hS₀P hx) hy.1
    · exact Set.disjoint_left.mp hdPC (hS₁P hy) hx.1
    · have hm : x ∈ I₀ ∪ I₁ := hIC.symm ▸ hx.1
      exact hm.elim hx.2 hy.2
  refine ⟨_,_,indep_compl_of_selfDual_spanning M₀ hE₀ hM₀ hA₀,
    indep_compl_of_selfDual_spanning M₁ hE₁ hM₁ hA₁,?_⟩
  rw [←Set.compl_inter,hd.inter_eq,Set.compl_empty]

end InfiniteMatroidCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Matroid


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.independent_cover_of_packing_covering := @_root_.OAI.InfiniteMatroidCounterexample.independent_cover_of_packing_covering
