-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.supportedIn_le_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:36.576426+00:00
-- url     : https://prove2.me/submissions/bd4134b9-644d-490f-a3c1-392922264ca7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_mono
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_support
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_indicator_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_support_indicator_mul_subset
import Theorems.Thm_GroundTheory_Automorphic_exists_isCompact_isOpen_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {V : Set X} {M : Submodule ℂ (X → ℂ)}
    (hloc : ∀ x ∈ V, ∃ V' : Set X, IsOpen V' ∧ x ∈ V' ∧ supportedIn V' ≤ M) :
    supportedIn V ≤ M := by
  classical
  intro f hf
  have hB : ∀ x ∈ V, ∃ B : Set X, IsClopen B ∧ x ∈ B ∧ supportedIn B ≤ M := by
    intro x hx
    obtain ⟨V', hV'o, hxV', hV'M⟩ := hloc x hx
    obtain ⟨B, hBc, hBo, hxB, hBV'⟩ := exists_isCompact_isOpen_subset (hV'o.mem_nhds hxV')
    exact ⟨B, ⟨hBc.isClosed, hBo⟩, hxB, (supportedIn_mono hBV').trans hV'M⟩
  choose! B hBc hxB hBM using hB
  obtain ⟨s, hsV, hsfin, hs⟩ := (isCompact_support hf.1).elim_finite_subcover_image
    (b := V) (c := B) (fun x hx => (hBc x hx).isOpen)
    (fun x hx => mem_iUnion₂.2 ⟨x, hf.2 hx, hxB x (hf.2 hx)⟩)
  have key : ∀ t : Finset X, (↑t : Set X) ⊆ V → ∀ g ∈ supportedIn V,
      Function.support g ⊆ ⋃ x ∈ t, B x → g ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ g _ hg
      have : g = 0 := by
        funext x
        by_contra h
        simpa using hg h
      rw [this]
      exact M.zero_mem
    | insert a t hat ih =>
      intro htV g hg hgs
      have haV : a ∈ V := htV (by simp)
      have e : g = (fun x => (B a).indicator 1 x * g x) +
          (fun x => (B a)ᶜ.indicator 1 x * g x) := by
        funext x
        by_cases h : x ∈ B a <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      rw [e]
      refine M.add_mem (hBM a haV ⟨(indicator_mul_mem (hBc a haV) hg).1, ?_⟩)
        (ih (fun x hx => htV (by simp [hx])) _ (indicator_mul_mem (hBc a haV).compl hg) ?_)
      · exact support_indicator_mul_subset.trans inter_subset_left
      · intro x hx
        obtain ⟨hxB, hxg⟩ := support_indicator_mul_subset hx
        have := hgs hxg
        rw [Finset.set_biUnion_insert] at this
        rcases this with h | h
        · exact absurd h hxB
        · simpa using h
  exact key hsfin.toFinset (fun x hx => hsV (by simpa using hx)) f hf (by simpa using hs)
end GroundTheory.Automorphic.Whittaker
