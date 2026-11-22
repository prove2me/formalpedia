-- Prove2me | solution 1 for MasulloGRH.isCompact_preimage_of_isOpenMap_of_isCompact_ker
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:21:59.650178+00:00
-- url     : https://prove2.me/submissions/6a582893-eed4-4f15-ab83-376327b953c4

import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

open Topology Filter Pointwise

namespace MasulloGRHProperAux

theorem main {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →* H) (hc : Continuous f) (ho : IsOpenMap f) (hk : IsCompact {x : G | f x = 1})
    {K : Set H} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : G)
  have hO : f '' V₀ ∈ 𝓝 (1 : H) := by simpa using ho.image_mem_nhds hV₀n
  have hR : IsClosed (Set.range f) := by
    have := Subgroup.isClosed_of_isOpen f.range (by simpa using ho.isOpen_range)
    simpa using this
  have hK' : IsCompact (K ∩ Set.range f) := hK.inter_right hR
  obtain ⟨t, htK, hcover⟩ := hK'.elim_nhds_subcover (fun k => {y | k⁻¹ * y ∈ f '' V₀})
    (fun k _ => by
      have h1 : Tendsto (fun y : H => k⁻¹ * y) (𝓝 k) (𝓝 (k⁻¹ * k)) :=
        (continuous_const.mul continuous_id).tendsto k
      rw [inv_mul_cancel] at h1
      exact h1 hO)
  have hpre : ∀ k ∈ t, ∃ p : G, f p = k := fun k hk => (htK k hk).2
  choose! p hp using hpre
  have hM : IsCompact (⋃ k ∈ t, (fun x => p k * x) '' (V₀ * {x : G | f x = 1})) :=
    t.isCompact_biUnion fun k _ =>
      (hV₀c.mul hk).image (continuous_const.mul continuous_id)
  refine hM.of_isClosed_subset (hK.isClosed.preimage hc) fun q hq => ?_
  have hq' : f q ∈ K ∩ Set.range f := ⟨hq, q, rfl⟩
  obtain ⟨k, hkt, hkq⟩ := Set.mem_iUnion₂.1 (hcover hq')
  obtain ⟨v, hv, hfv⟩ := hkq
  refine Set.mem_iUnion₂.2 ⟨k, hkt, v * (v⁻¹ * ((p k)⁻¹ * q)), ⟨v, hv, v⁻¹ * ((p k)⁻¹ * q), ?_, rfl⟩,
    by simp⟩
  show f (v⁻¹ * ((p k)⁻¹ * q)) = 1
  rw [map_mul, map_mul, map_inv, map_inv, hp k hkt, hfv, inv_mul_cancel]

end MasulloGRHProperAux

theorem solution
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →* H) (hc : Continuous f) (ho : IsOpenMap f) (hk : IsCompact {x : G | f x = 1})
    {K : Set H} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  MasulloGRHProperAux.main f hc ho hk hK
