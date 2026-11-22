-- Prove2me | solution 1 for MasulloGRH.expDecay_exists_cofinal_goodSubgroups
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:37:31.99323+00:00
-- url     : https://prove2.me/submissions/927a9058-0230-424c-b31a-24daaa9947cd

import Theorems.Thm_MasulloGRH_exists_cofinal_structuralPairs
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

open MasulloGRH

theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
:
    ∃ k : ℕ → Subgroup G, (∀ N, IsGoodSubgroup (k N)) ∧ Antitone k ∧
      ∀ k' : Subgroup G, IsGoodSubgroup k' → ∃ N, k N ≤ k' := by
  obtain ⟨Γ, k, m', n', r', s', d', π, h1, -, hk, hcof⟩ := exists_cofinal_structuralPairs G
  refine ⟨k, fun N => (h1 N).1.2.2.1, hk, fun k' hk' => ?_⟩
  have hkc : IsCompact (k' : Set G) := isCompact_of_isGoodSubgroup G k' hk'
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hsub : K ∪ (k' : Set G) ⊆ (Subgroup.closure (K ∪ (k' : Set G)) : Set G) :=
    Subgroup.subset_closure
  have hs : IsStructuralPair (Subgroup.closure (K ∪ (k' : Set G))) k' := by
    refine ⟨?_, ?_, hk', ?_⟩
    · exact Subgroup.isOpen_of_mem_nhds _
        (Filter.mem_of_superset hK1 (Set.subset_union_left.trans hsub))
    · exact ⟨K ∪ (k' : Set G), hK.union hkc, hsub,
        ⟨K, hK1, Set.inter_subset_left.trans Set.subset_union_left⟩, rfl⟩
    · exact fun x hx => hsub (Or.inr hx)
  obtain ⟨m₁, n₁, r₁, s₁, d₁, π₁, hπ₁⟩ :=
    exists_elemPresentation_of_isStructuralPair G _ k' hs
  obtain ⟨M, -, hM⟩ := hcof _ k' m₁ n₁ r₁ s₁ d₁ π₁ hs hπ₁
  exact ⟨M, hM⟩
