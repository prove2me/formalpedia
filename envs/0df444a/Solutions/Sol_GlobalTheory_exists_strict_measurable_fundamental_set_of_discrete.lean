-- Prove2me | solution 1 for GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:34.739887+00:00
-- url     : https://prove2.me/submissions/ea8491f3-100e-44e6-b32b-4057f4d5968b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStrictMeasurableFundamentalSetOfDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) := by
  intro G _ _ _ _ _ _ _ _ Γ ⟨U, hU, hΓU⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨t, htU, ht, h1t⟩ := mem_nhds_iff.1 hU
    have hopen : IsOpen ({1} : Set Γ) := by
      rw [isOpen_induced_iff]
      refine ⟨t, ht, ?_⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact Subtype.ext (hΓU x x.2 (htU hx))
      · rintro rfl
        exact h1t
    haveI : DiscreteTopology Γ := discreteTopology_of_isOpen_singleton_one hopen
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split hU
    let C : G → Set G := fun x => {y | y * x⁻¹ ∈ V ∧ x * y⁻¹ ∈ V}
    have hCo : ∀ x, IsOpen (C x) := fun x =>
      (hVo.preimage (continuous_id.mul continuous_const)).inter
        (hVo.preimage (continuous_const.mul continuous_inv))
    have hCx : ∀ x, x ∈ C x := fun x => by simp [C, hV1]
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable C hCo
    have hTne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h1 : (1 : G) ∈ ⋃ x, C x := Set.mem_iUnion.2 ⟨1, hCx 1⟩
      rw [← hT, h] at h1
      simp at h1
    obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
    let W : ℕ → Set G := fun n => C (c n)
    have hWo : ∀ n, IsOpen (W n) := fun n => hCo _
    have hcover : ∀ x, ∃ n, x ∈ W n := by
      intro x
      have hx : x ∈ ⋃ y ∈ T, C y := by rw [hT]; exact Set.mem_iUnion.2 ⟨x, hCx x⟩
      rw [hc] at hx
      simp only [Set.biUnion_range, Set.mem_iUnion] at hx
      exact hx
    have hsep : ∀ n (x : G) (γ : Γ), x ∈ W n → (γ : G) * x ∈ W n → γ = 1 := by
      intro n x γ hx hγx
      have h := hVU _ hγx.1 _ hx.2
      have he : (γ : G) * x * (c n)⁻¹ * (c n * x⁻¹) = γ := by group
      rw [he] at h
      exact Subtype.ext (hΓU γ γ.2 h)
    let S : ℕ → Set G := fun m => ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' W m
    have hSo : ∀ m, IsOpen (S m) := fun m =>
      isOpen_iUnion fun γ => (hWo m).preimage (continuous_const.mul continuous_id)
    have hmemS : ∀ m x, x ∈ S m ↔ ∃ γ : Γ, (γ : G) * x ∈ W m := fun m x => by
      simp only [S, Set.mem_iUnion, Set.mem_preimage]
    refine ⟨⋃ n : ℕ, W n \ ⋃ m : Fin n, S m, ?_, ?_⟩
    · exact MeasurableSet.iUnion fun n =>
        (hWo n).measurableSet.diff (MeasurableSet.iUnion fun m => (hSo m).measurableSet)
    · intro g
      have hmemF : ∀ y, y ∈ (⋃ n : ℕ, W n \ ⋃ m : Fin n, S m) ↔
          ∃ n, y ∈ W n ∧ ∀ m < n, y ∉ S m := by
        intro y
        simp only [Set.mem_iUnion, Set.mem_diff, not_exists]
        constructor
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m hm' => hm ⟨m, hm'⟩⟩
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m => hm m m.2⟩
      have hex : ∃ n, g ∈ S n := by
        obtain ⟨n, hn⟩ := hcover g
        exact ⟨n, (hmemS n g).2 ⟨1, by simpa using hn⟩⟩
      classical
      obtain ⟨γ, hγ⟩ := (hmemS _ g).1 (Nat.find_spec hex)
      refine ⟨γ, (hmemF _).2 ⟨Nat.find hex, hγ, fun m hm hS => ?_⟩, ?_⟩
      · obtain ⟨δ, hδ⟩ := (hmemS m _).1 hS
        exact Nat.find_min hex hm ((hmemS m g).2 ⟨δ * γ, by simpa [mul_assoc] using hδ⟩)
      · intro γ' hγ'
        obtain ⟨k, hk, hkS⟩ := (hmemF _).1 hγ'
        have hkN : k = Nat.find hex := by
          refine le_antisymm ?_ (Nat.find_min' hex ((hmemS k g).2 ⟨γ', hk⟩))
          by_contra hlt
          push_neg at hlt
          exact hkS _ hlt ((hmemS _ _).2 ⟨γ * γ'⁻¹, by simpa [mul_assoc] using hγ⟩)
        rw [hkN] at hk
        have h1 := hsep _ _ (γ' * γ⁻¹) hγ (by simpa [mul_assoc] using hk)
        exact mul_inv_eq_one.1 h1
end _root_.GlobalTheory
end GlobalTheory
