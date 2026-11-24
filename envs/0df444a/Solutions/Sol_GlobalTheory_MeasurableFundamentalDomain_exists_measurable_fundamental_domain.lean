-- Prove2me | solution 1 for GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:29.363068+00:00
-- url     : https://prove2.me/submissions/866f655f-1788-4cbc-a741-91eefc9504f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMeasurableFundamentalDomain
import Theorems.Thm_GlobalTheory_MeasurableFundamentalDomain_exists_small_open

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MeasurableFundamentalDomain
open Set Topology
namespace GlobalTheory.MeasurableFundamentalDomain
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable ↥Γ]
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y : G, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = (1 : G) := by
  classical
  obtain ⟨V, hVo, hV1, hV⟩ := exists_small_open Γ hΓ
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq G
  let U : ℕ → Set G := fun n => {y | y * (g n)⁻¹ ∈ V}
  let S : ℕ → Set G := fun n => ⋃ γ ∈ Γ, {y | γ * y ∈ U n}
  have hUo : ∀ n, IsOpen (U n) := fun n => hVo.preimage (continuous_id.mul continuous_const)
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_biUnion fun γ _ => (hUo n).preimage (continuous_const.mul continuous_id)
  have hS : ∀ n y, y ∈ S n ↔ ∃ γ ∈ Γ, γ * y ∈ U n := by
    intro n y
    simp [S]
  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ y, γ * y ∈ S n → y ∈ S n := by
    intro n γ hγ y hy
    obtain ⟨δ, hδ, h⟩ := (hS _ _).1 hy
    exact (hS _ _).2 ⟨δ * γ, Γ.mul_mem hδ hγ, by rwa [mul_assoc]⟩
  refine ⟨⋃ n, (U n \ ⋃ m ∈ Set.Iio n, S m), ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n =>
      (hUo n).measurableSet.diff (isOpen_biUnion fun m _ => hSo m).measurableSet
  · intro y
    have hex : ∃ n, y ∈ S n := by
      have ho : IsOpen {x : G | y * x⁻¹ ∈ V} :=
        hVo.preimage (continuous_const.mul continuous_inv)
      obtain ⟨n, hn⟩ := hg.exists_mem_open ho ⟨y, by simpa using hV1⟩
      exact ⟨n, (hS _ _).2 ⟨1, Γ.one_mem, by rw [one_mul]; exact hn⟩⟩
    obtain ⟨γ, hγ, h⟩ := (hS _ _).1 (Nat.find_spec hex)
    refine ⟨γ, hγ, mem_iUnion.2 ⟨Nat.find hex, h, ?_⟩⟩
    intro hm
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.1 hm
    exact Nat.find_min hex hm (hSinv m γ hγ y hy)
  · intro γ hγ y hy hγy
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hy
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hγy
    have hnm : n = m := by
      rcases lt_trichotomy n m with h | h | h
      · exact absurd (mem_iUnion₂.2 ⟨n, h, (hS _ _).2
          ⟨γ⁻¹, Γ.inv_mem hγ, by rwa [inv_mul_cancel_left]⟩⟩) hm'
      · exact h
      · exact absurd (mem_iUnion₂.2 ⟨m, h, (hS _ _).2 ⟨γ, hγ, hm⟩⟩) hn'
    subst hnm
    have e : (γ * y * (g n)⁻¹) * (y * (g n)⁻¹)⁻¹ = γ := by group
    have := hV _ hm _ hn (by rw [e]; exact hγ)
    rwa [e] at this
end GlobalTheory.MeasurableFundamentalDomain
