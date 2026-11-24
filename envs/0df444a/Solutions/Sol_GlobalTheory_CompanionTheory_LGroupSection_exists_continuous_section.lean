-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:22:35.805798+00:00
-- url     : https://prove2.me/submissions/8b62d043-ed2f-4a2f-aa4a-c45c4ea08857

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_LGroupSection_exists_refine
import Theorems.Thm_GlobalTheory_CompanionTheory_LGroupSection_exists_subgroup_seq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LGroupSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.LGroupSection
theorem _root_.solution (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  classical
  haveI : IsClosed (H : Set G) := hH
  obtain ⟨K, hK0, hKle, hKo, hKc, hKb⟩ := exists_subgroup_seq (G := G)

  let P : ℕ → (G ⧸ H → G) → Prop := fun n t =>
    IsLocallyConstant t ∧ ∀ x, x ∈ cosetImage H (K n) (t x)
  have hstep : ∀ n (t : {t // P n t}), ∃ t' : {t // P (n + 1) t},
      ∀ x, (t.1 x)⁻¹ * t'.1 x ∈ K n := by
    rintro n ⟨t, ht, hmem⟩
    obtain ⟨t', h1, h2, h3⟩ :=
      exists_refine H (K n) (K (n + 1)) (hKle n) (hKo _) (hKc n) t ht hmem
    exact ⟨⟨t', h1, h2⟩, h3⟩
  have h0 : P 0 (fun _ => 1) := by
    refine ⟨IsLocallyConstant.const _, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, by simp [hK0], by simp⟩
  choose nxt hnxt using hstep
  let T : (n : ℕ) → {t // P n t} := fun n => Nat.rec ⟨_, h0⟩ (fun n t => nxt n t) n
  have hT : ∀ n x, ((T n).1 x)⁻¹ * (T (n + 1)).1 x ∈ K n := fun n x => hnxt n (T n) x

  let C : G ⧸ H → ℕ → Set G := fun x n => (fun k => (T (n + 1)).1 x * k) '' (K (n + 1) : Set G)
  have hCmem : ∀ x n g, g ∈ C x n ↔ ((T (n + 1)).1 x)⁻¹ * g ∈ K (n + 1) := by
    intro x n g
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
    · intro hg
      exact ⟨_, hg, by simp⟩
  have hCanti : ∀ x n, C x (n + 1) ⊆ C x n := by
    intro x n g hg
    rw [hCmem] at hg ⊢
    have h1 := hT (n + 1) x
    have : ((T (n + 1)).1 x)⁻¹ * g = (((T (n + 1)).1 x)⁻¹ * (T (n + 1 + 1)).1 x) *
        (((T (n + 1 + 1)).1 x)⁻¹ * g) := by group
    rw [this]
    exact (K (n + 1)).mul_mem h1 (hKle _ hg)
  have hCne : ∀ x, (⋂ n, C x n).Nonempty := fun x =>
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (C x) (hCanti x)
      (fun n => ⟨_, 1, (K (n + 1)).one_mem, rfl⟩)
      ((hKc 0).image (continuous_const.mul continuous_id))
      (fun n => ((hKc n).image (continuous_const.mul continuous_id)).isClosed)
  choose s hs using hCne
  have hsC : ∀ x n, ((T (n + 1)).1 x)⁻¹ * s x ∈ K (n + 1) := fun x n =>
    (hCmem x n _).1 (mem_iInter.1 (hs x) n)
  refine ⟨s, ?_, fun c => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_def]
    intro W hW

    have hW1 : (fun k => s x * k) ⁻¹' W ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW
    obtain ⟨m, hm⟩ := hKb _ hW1
    have hmm : (K (m + 1) : Set G) ⊆ (fun k => s x * k) ⁻¹' W :=
      fun g hg => hm (hKle m hg)
    have hloc : {y | (T (m + 1)).1 y = (T (m + 1)).1 x} ∈ 𝓝 x :=
      ((T (m + 1)).2.1.isOpen_fiber _).mem_nhds rfl
    filter_upwards [hloc] with y hy
    have h1 := hsC y m
    have h2 := hsC x m
    rw [hy] at h1
    have : (s x)⁻¹ * s y = (((T (m + 1)).1 x)⁻¹ * s x)⁻¹ * (((T (m + 1)).1 x)⁻¹ * s y) := by group
    have hk : (s x)⁻¹ * s y ∈ K (m + 1) := by
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) h1
    simpa using hmm hk
  · by_contra hne

    have hopen : IsOpen {g : G | (g : G ⧸ H) ≠ c} :=
      (isOpen_compl_singleton (x := c)).preimage continuous_quotient_mk'
    have hW1 : (fun k => s c * k) ⁻¹' {g : G | (g : G ⧸ H) ≠ c} ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hopen.mem_nhds hne
    obtain ⟨m, hm⟩ := hKb _ hW1
    obtain ⟨k, hk, hkc⟩ := (T (m + 1)).2.2 c
    have hk' : (s c)⁻¹ * ((T (m + 1)).1 c * k) ∈ K (m + 1) := by
      have h2 := hsC c m
      have : (s c)⁻¹ * ((T (m + 1)).1 c * k) = (((T (m + 1)).1 c)⁻¹ * s c)⁻¹ * k := by group
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) hk
    have := hm (hKle m hk')
    simp only [mem_preimage, mem_setOf_eq, mul_inv_cancel_left] at this
    exact this hkc
end GlobalTheory.CompanionTheory.LGroupSection
