-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.packingCovering_of_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T06:07:34.858977+00:00
-- url     : https://prove2.me/submissions/fd6ae15c-c4fb-423f-a36e-18c5ed9adf1c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/IntersectionReduction.lean:L8-L59
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.packingCovering_of_intersection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries

-- ---- from OAI.Combinatorics.InfiniteMatroid.IntersectionReduction ----
namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

lemma packingCovering_of_intersection {α : Type*} {M N : Matroid α}
    (hE : N.E = M.E) (h : HasIntersection M N) : HasPackingCovering M N.dual := by
  obtain ⟨J, J₀, J₁, hJM, hJN, hd, hJJ, hcl⟩ := h
  have h0J : J₀ ⊆ J := hJJ ▸ subset_union_left
  have h1J : J₁ ⊆ J := hJJ ▸ subset_union_right
  have h0M := hJM.subset h0J
  have h1M := hJM.subset h1J
  have h0N := hJN.subset h0J
  have h1N := hJN.subset h1J
  let P := M.closure J₀
  let C := M.E \ P
  have hPE : P ⊆ M.E := M.closure_subset_ground J₀
  have h0P : J₀ ⊆ P := M.subset_closure J₀
  have h1C : J₁ ⊆ C := by
    intro x hx
    refine ⟨h1M.subset_ground hx, ?_⟩
    intro hxP
    have hx0 : x ∈ J₀ := (hJM.closure_inter_eq_self_of_subset h0J) ▸ ⟨hxP, h1J hx⟩
    exact disjoint_left.mp hd hx0 hx
  have hCcl : C ⊆ N.closure J₁ := by
    intro x hx
    have hxcl : x ∈ P ∪ N.closure J₁ := hcl.symm ▸ hx.1
    exact hxcl.resolve_left hx.2
  have h0basis : M.IsBasis J₀ P := h0M.isBasis_closure
  have h1basis : N.IsBasis J₁ C := h1N.isBasis_of_subset_of_subset_closure h1C hCcl
  have hJ0con : (N ／ C).Indep J₀ := by
    apply h1basis.contract_indep_iff.mpr
    refine ⟨hJJ ▸ hJN, ?_⟩
    exact disjoint_sdiff_left.mono_right h0P
  have hJ1con : (M ／ P).Indep J₁ := by
    apply h0basis.contract_indep_iff.mpr
    refine ⟨?_, disjoint_sdiff_right.mono_right h1C⟩
    simpa only [union_comm J₁, hJJ] using hJM
  have hNP : N.E \ C = P := by
    rw [hE]
    exact sdiff_sdiff_cancel_left hPE
  have hdualS : (N.dual ↾ P).Spanning (P \ J₀) := by
    have hc : (N.dual ↾ P).Coindep J₀ := by
      change ((N.dual ↾ P).dual).Indep J₀
      simpa only [Matroid.contract, Matroid.delete, Matroid.dual_ground, hNP] using hJ0con
    exact hc.compl_spanning
  have hN1 : (N ↾ C).Spanning J₁ :=
    (N.restrict_spanning_iff h1C (by rw [hE]; exact sdiff_subset)).mpr hCcl
  have hdualI : (contractOnto N.dual C).Indep (C \ J₁) := by
    simpa only [contractOnto, Matroid.dual_dual, Matroid.restrict_ground_eq] using hN1.compl_coindep.indep
  refine ⟨P, C, J₀, P \ J₀, J₁, C \ J₁,
    disjoint_sdiff_right, union_sdiff_cancel hPE, ?_, h0P, sdiff_subset,
    disjoint_sdiff_right, ?_, hdualS, h1C, sdiff_subset, ?_, hdualI, ?_⟩
  · simpa only [Matroid.dual_ground] using hE
  · exact (M.restrict_spanning_iff h0P hPE).mpr Subset.rfl
  · exact hJ1con
  · exact union_sdiff_cancel h1C

end InfiniteMatroidCounterexample

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Matroid


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.packingCovering_of_intersection := @_root_.OAI.InfiniteMatroidCounterexample.packingCovering_of_intersection
