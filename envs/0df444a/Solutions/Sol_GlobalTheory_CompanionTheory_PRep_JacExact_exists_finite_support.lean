-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.JacExact.exists_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:10.270882+00:00
-- url     : https://prove2.me/submissions/a1194e9b-7447-4849-bc7f-b73c89e8456c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.JacExact
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.PRep.JacExact
theorem _root_.solution (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ) (x : W)
    (hx : x ∈ twKer σ N θ) :
    ∃ (s : Finset N) (t : Finset W), x ∈ Submodule.span ℂ
      {y | ∃ n ∈ s, ∃ w ∈ t, y = σ (n : G) w - ((θ n : ℂˣ) : ℂ) • w} := by
  classical
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, w, rfl⟩ := hy
    exact ⟨{n}, {w}, Submodule.subset_span ⟨n, by simp, w, by simp, rfl⟩⟩
  | zero => exact ⟨∅, ∅, Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, h⟩ := ha
    obtain ⟨s', t', h'⟩ := hb
    refine ⟨s ∪ s', t ∪ t', Submodule.add_mem _ ?_ ?_⟩
    · refine Submodule.span_mono ?_ h
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_left _ hn, w, Finset.mem_union_left _ hw, rfl⟩
    · refine Submodule.span_mono ?_ h'
      rintro y ⟨n, hn, w, hw, rfl⟩
      exact ⟨n, Finset.mem_union_right _ hn, w, Finset.mem_union_right _ hw, rfl⟩
  | smul c a _ ha =>
    obtain ⟨s, t, h⟩ := ha
    exact ⟨s, t, Submodule.smul_mem _ _ h⟩
end GlobalTheory.CompanionTheory.PRep.JacExact
