-- Prove2me | solution 1 for GlobalTheory.CharDotKill.charDot_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:28.731173+00:00
-- url     : https://prove2.me/submissions/ffc8553d-d04f-40d6-bd6a-b8a0f57606a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompact
import Theorems.Thm_GlobalTheory_CharDotKill_exists_open_ker
import Theorems.Thm_GlobalTheory_CharDotKill_nonarchimedean_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CharDotKill
namespace GlobalTheory.CharDotKill
theorem _root_.solution : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ]
    (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K),
      ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  intro K _ _ _ _ χ hχ κ _ C hC
  obtain ⟨K₀, hK₀⟩ := exists_open_ker χ hχ
  have hdot : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hO : IsOpen {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} :=
    K₀.isOpen.preimage hdot

  have hW : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ (K₀ : Set K) := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    have hO' : IsOpen {p : (κ → K) × (κ → K) | p.2 ⬝ᵥ p.1 ∈ (K₀ : Set K)} :=
      K₀.isOpen.preimage (continuous_snd.dotProduct continuous_fst)
    filter_upwards [hO'.mem_nhds (x := ((0 : κ → K), z)) (by simp [K₀.zero_mem])] with p hp
    exact hp

  have hP : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hO.mem_nhds (by simp [K₀.zero_mem])
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hP
  obtain ⟨U, hU, V, hV, hUV⟩ := hP
  haveI : NonarchimedeanAddGroup (κ → K) := nonarchimedean_pi
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (Filter.inter_mem (Filter.inter_mem hU hV) hW)
  refine ⟨H, fun z hz a ha b hb => hK₀ _ (K₀.add_mem ?_ ?_)⟩
  · exact (hH hb).2 z hz
  · exact hUV (Set.mk_mem_prod (hH ha).1.1 (hH hb).1.2)
end GlobalTheory.CharDotKill
