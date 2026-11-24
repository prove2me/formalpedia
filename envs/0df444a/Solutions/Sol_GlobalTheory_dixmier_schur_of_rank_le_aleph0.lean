-- Prove2me | solution 1 for GlobalTheory.dixmier_schur_of_rank_le_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:53.043653+00:00
-- url     : https://prove2.me/submissions/cbe769f2-de3d-4c15-8f7f-09293503faed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierSchurOfRankLeAleph0
import Theorems.Thm_GlobalTheory_linearIndependent_of_sub_apply_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V),
      Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
      (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  intro V ι _ _ ρ T hV hrank hirr hcomm
  by_contra hne
  push_neg at hne
  have hunit : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c) := by
    intro c
    set S := T - algebraMap ℂ (Module.End ℂ V) c with hS
    have hS0 : S ≠ 0 := by
      intro h0
      apply hne c
      rw [← Algebra.algebraMap_eq_smul_one]
      exact sub_eq_zero.1 h0
    have hSc : ∀ i x, S (ρ i x) = ρ i (S x) := by
      intro i x
      have := LinearMap.congr_fun (hcomm i) x
      simp only [Module.End.mul_apply] at this
      simp [hS, this, Module.algebraMap_end_apply]
    rw [Module.End.isUnit_iff]
    constructor
    · rw [← LinearMap.ker_eq_bot]
      refine (hirr _ ?_).resolve_right ?_
      · intro i x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hSc, hx, map_zero]
      · rw [LinearMap.ker_eq_top]; exact hS0
    · rw [← LinearMap.range_eq_top]
      refine (hirr _ ?_).resolve_left ?_
      · rintro i _ ⟨x, rfl⟩
        exact ⟨ρ i x, hSc i x⟩
      · rw [LinearMap.range_eq_bot]; exact hS0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  choose w hw using fun c => ((Module.End.isUnit_iff _).1 (hunit c)).2 v
  have hli := linearIndependent_of_sub_apply_eq T hunit v hv w hw
  have h1 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)
end GlobalTheory
