-- Prove2me | solution 1 for LCAGroup.compactlyGenerated_closedSubgroup_and_quotient
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:56:57.868597+00:00
-- url     : https://prove2.me/submissions/c0f44acc-3e0c-45e6-833a-e803f425d68e

import Mathlib

open Topology

set_option autoImplicit false

namespace Sol_LCAGroup_compactlyGenerated_closedSubgroup_and_quotient

open Filter Set

open scoped Pointwise in
/-- A closed subgroup of a compactly generated abelian topological group is compactly
generated (Dickson's lemma argument). -/
theorem closedSubgroup
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ U ∈ 𝓝 (1 : H), IsCompact U ∧ Subgroup.closure U = ⊤ := by
  classical
  obtain ⟨U, hU, hUc, hGen⟩ := hG
  -- Write every element as a product of finitely many fixed directions and a remainder in U.
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates
    ((hUc.union hUc.inv).mul hUc) ⟨1, mem_interior_iff_mem_nhds.mpr hU⟩
  let a (n : t → ℕ) : G := ∏ i : t, ((i : G)⁻¹) ^ n i
  have ha0 : a 0 = 1 := by simp [a]
  have haAdd (m n : t → ℕ) : a (m + n) = a m * a n := by
    simp only [a, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  have haSingle (i : t) : a (Pi.single i 1) = (i : G)⁻¹ := by
    unfold a
    rw [Finset.prod_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, pow_zero])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same, pow_one]
  have hStep (x : G) (hx : x ∈ U ∪ U⁻¹) (y : G)
      (hy : ∃ n : t → ℕ, ∃ u ∈ U, y = a n * u) :
      ∃ n : t → ℕ, ∃ u ∈ U, x * y = a n * u := by
    obtain ⟨n, u, hu, rfl⟩ := hy
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (ht (Set.mul_mem_mul hx hu))
    change i * (x * u) ∈ U at hiu
    refine ⟨n + Pi.single ⟨i, hi⟩ 1, i * (x * u), hiu, ?_⟩
    rw [haAdd, haSingle]
    simp [mul_assoc, mul_left_comm]
  have hRepresent (x : G) : ∃ n : t → ℕ, ∃ u ∈ U, x = a n * u := by
    have hx : x ∈ Subgroup.closure U := hGen.symm ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction_left (p := fun z _ ↦ ∃ n : t → ℕ, ∃ u ∈ U, z = a n * u)
      ⟨0, 1, mem_of_mem_nhds hU, by simp [ha0]⟩ ?_ ?_ hx
    · exact fun z hz y _ ↦ hStep z (Or.inl hz) y
    · exact fun z hz y _ ↦ hStep z⁻¹ (Or.inr (by simpa using hz)) y
  obtain ⟨V, hV, _, hVinv, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hUc
    ⟨1, mem_interior_iff_mem_nhds.mpr hV⟩
  -- For each translate, Dickson's lemma bounds the minimal nonzero exponent vectors.
  let P (i : s) (n : t → ℕ) : Prop :=
    n ≠ 0 ∧ ∃ u ∈ U, (i : G) * u ∈ V ∧ a n * u ∈ H
  let M : Set (t → ℕ) := {0} ∪ ⋃ i : s, {n | Minimal (P i) n}
  have hM : M.Finite := (finite_singleton 0).union (finite_iUnion fun i ↦
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (P i)))
  let K : Set G := (a '' M) * U
  let S : Set H := Subtype.val ⁻¹' K
  let J : Subgroup G := (Subgroup.closure S).map H.subtype
  have hK : IsCompact K := (hM.image a).isCompact.mul hUc
  have hUK : U ⊆ K := by
    intro u hu
    rw [← one_mul u, ← ha0]
    exact Set.mul_mem_mul (mem_image_of_mem a (Or.inl rfl)) hu
  have hMem (x : G) (hx : x ∈ H) (hxK : x ∈ K) : x ∈ J :=
    Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.subset_closure hxK, rfl⟩
  have hReduce (n : t → ℕ) : ∀ u ∈ U, a n * u ∈ H → a n * u ∈ J := by
    refine wellFounded_lt.induction (C := fun m ↦ ∀ u ∈ U, a m * u ∈ H → a m * u ∈ J) n ?_
    clear n
    intro n ih u hu hnu
    by_cases hn : n = 0
    · exact hMem _ hnu (Set.mul_mem_mul (mem_image_of_mem a (Or.inl hn)) hu)
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (hs hu)
    let j : s := ⟨i, hi⟩
    obtain ⟨m, hmn, hm⟩ := exists_minimal_le_of_wellFoundedLT (P j) n
      ⟨hn, u, hu, hiu, hnu⟩
    obtain ⟨hm0, v, hv, hiv, hmv⟩ := hm.prop
    obtain ⟨d, hd⟩ := exists_add_of_le hmn
    have hdn : d < n := by
      rw [hd]
      exact lt_add_of_pos_left d (lt_of_le_of_ne (fun i ↦ Nat.zero_le (m i)) hm0.symm)
    have huv : u / v ∈ U := by
      have hInv : (i * v)⁻¹ ∈ V := hVinv ▸ Set.mem_inv.mpr (by simpa using hiv)
      have hMul := hVV (Set.mul_mem_mul hiu hInv)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMul
    have hFactor : a n * u = (a m * v) * (a d * (u / v)) := by
      rw [hd, haAdd]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hdH : a d * (u / v) ∈ H := by
      simpa only [hFactor, inv_mul_cancel_left] using H.mul_mem (H.inv_mem hmv) hnu
    rw [hFactor]
    exact J.mul_mem (hMem _ hmv (Set.mul_mem_mul (mem_image_of_mem a
      (Or.inr (mem_iUnion.mpr ⟨j, hm⟩))) hv)) (ih d hdn (u / v) huv hdH)
  refine ⟨S, continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_of_superset hU hUK),
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK, eq_top_iff.mpr ?_⟩
  intro x _
  obtain ⟨n, u, hu, hx⟩ := hRepresent x
  have hxJ : (x : G) ∈ J := hx ▸ hReduce n u hu (hx ▸ x.property)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxJ
  exact (Subtype.ext hyx : y = x) ▸ hy

/-- The quotient of a compactly generated topological group by a subgroup is compactly
generated: the image of a compact generating neighbourhood works. -/
theorem quotient
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤)
    (H : Subgroup G) :
    ∃ U ∈ 𝓝 (1 : G ⧸ H), IsCompact U ∧ Subgroup.closure U = ⊤ := by
  obtain ⟨U, hU, hCompact, hGen⟩ := hG
  let q := QuotientGroup.mk' H
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  refine ⟨q '' U, ?_, hCompact.image hq.continuous, ?_⟩
  · simpa only [map_one] using hq.isOpenMap.image_mem_nhds hU
  · rw [← MonoidHom.map_closure, hGen, Subgroup.map_top_of_surjective q hq.surjective]

end Sol_LCAGroup_compactlyGenerated_closedSubgroup_and_quotient


theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (hG : ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    (∃ U ∈ 𝓝 (1 : H), IsCompact U ∧ Subgroup.closure U = ⊤) ∧
    (∃ U ∈ 𝓝 (1 : G ⧸ H), IsCompact U ∧ Subgroup.closure U = ⊤) :=
  ⟨Sol_LCAGroup_compactlyGenerated_closedSubgroup_and_quotient.closedSubgroup hG H hH,
    Sol_LCAGroup_compactlyGenerated_closedSubgroup_and_quotient.quotient hG H⟩
