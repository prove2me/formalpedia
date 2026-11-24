-- Prove2me | solution 1 for GlobalTheory.window_around_last_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:32.417248+00:00
-- url     : https://prove2.me/submissions/a5a768fa-4c98-4550-85ad-b7739500d965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAroundLastMaxNullSequence

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
theorem _root_.solution : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  intro β c h hc hβ0 hne hlim
  have hfin : ∀ ε : ℝ, 0 < ε → {k | ε ≤ β k}.Finite := by
    intro ε hε
    have h1 : ∀ᶠ k in Filter.cofinite, β k < ε := hlim.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at h1
    simpa [not_lt] using h1
  obtain ⟨k₀, hk₀⟩ := hne
  have hpos : 0 < β k₀ := lt_of_le_of_ne (hβ0 k₀) (Ne.symm hk₀)
  set T := (hfin _ hpos).toFinset with hT
  have hk₀T : k₀ ∈ T := by simp [T]
  obtain ⟨m, hmT, hm⟩ := T.exists_max_image β ⟨k₀, hk₀T⟩
  have hmax : ∀ k, β k ≤ β m := by
    intro k
    by_cases hk : β k₀ ≤ β k
    · exact hm k (by simp [T, hk])
    · push_neg at hk
      have : β k₀ ≤ β m := hm k₀ hk₀T
      linarith
  set U := T.filter (fun k => β k = β m) with hU
  have hmU : m ∈ U := Finset.mem_filter.2 ⟨hmT, rfl⟩
  set N := U.max' ⟨m, hmU⟩ with hNdef
  have hNU : N ∈ U := U.max'_mem _
  have hN : β N = β m := (Finset.mem_filter.1 hNU).2
  have hk₀m : β k₀ ≤ β m := hm k₀ hk₀T
  have hNlast : ∀ k, N < k → β k < β N := by
    intro k hk
    rcases lt_or_eq_of_le (hmax k) with h1 | h1
    · rw [hN]; exact h1
    · exfalso
      have hkU : k ∈ U := by
        refine Finset.mem_filter.2 ⟨?_, h1⟩
        simp [T]; linarith
      have := U.le_max' k hkU
      omega
  have hc₀ : 0 < β N := by rw [hN]; linarith
  have hcpos : 0 < c * β N := mul_pos hc hc₀
  set F := (hfin _ hcpos).toFinset with hF
  set B : ℕ := (F.image (fun k => k.natAbs)).sup id ⊔ N.natAbs with hB
  have hNB : N.natAbs ≤ B := le_sup_right
  have hFB : ∀ k, c * β N ≤ β k → k.natAbs ≤ B := by
    intro k hk
    have hkF : k ∈ F := by simp [F, hk]
    have : k.natAbs ≤ (F.image (fun k => k.natAbs)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hkF)
    exact le_trans this le_sup_left
  refine ⟨B + h, B + h + B, (N + B).toNat, ?_⟩
  have hx : ((((N + (B : ℤ)).toNat + h : ℕ)) : ℤ) - ((B + h : ℕ) : ℤ) = N := by omega
  rw [hx]
  refine ⟨by omega, by omega, hc₀, fun k => hN ▸ hmax k, fun k hk => hNlast k hk, ?_⟩
  intro k hk
  by_contra hlt
  push_neg at hlt
  have := hFB k hlt.le
  omega
end GlobalTheory
