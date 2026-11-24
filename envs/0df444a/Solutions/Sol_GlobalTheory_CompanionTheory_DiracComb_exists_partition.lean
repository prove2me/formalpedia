-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DiracComb.exists_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:19.34325+00:00
-- url     : https://prove2.me/submissions/74507fe2-8cd1-4df3-8da0-fff150070175

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_unity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiracComb
namespace GlobalTheory.CompanionTheory.DiracComb
theorem _root_.solution : ∀ (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ), HasCompactSupport (f : (Fin n → ℝ) → ℂ) → ∃ (s : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → SchwartzMap (Fin n → ℝ) ℂ), (∀ m, tsupport (g m : (Fin n → ℝ) → ℂ) ⊆ Metric.ball (fun i => (m i : ℝ)) 1) ∧ f = ∑ m ∈ s, g m := by
  intro n f hf
  obtain ⟨ρ, h1, h2, h3, h4⟩ := exists_unity n
  have hsm : ∀ m, ContDiff ℝ ∞ (fun x => ρ m x • f x) := fun m => (h1 m).smul (f.smooth ⊤)
  have hcs : ∀ m, HasCompactSupport (fun x => ρ m x • f x) := fun m =>
    HasCompactSupport.smul_left (f := ρ m) hf
  have hfin : {m | (Function.support (ρ m) ∩ tsupport (f : (Fin n → ℝ) → ℂ)).Nonempty}.Finite :=
    h3.finite_nonempty_inter_compact hf
  obtain ⟨s, hs⟩ := hfin.exists_finset_coe
  have hts : ∀ m, tsupport ((hcs m).toSchwartzMap (hsm m) : (Fin n → ℝ) → ℂ) ⊆ tsupport (ρ m) :=
    fun m => tsupport_smul_subset_left (ρ m) f
  refine ⟨s, fun m => (hcs m).toSchwartzMap (hsm m), fun m => (hts m).trans (h2 m), ?_⟩
  ext x
  rw [sum_apply]
  suffices h : f x = ∑ m ∈ s, ρ m x • f x from h.trans (Finset.sum_congr rfl fun _ _ => rfl)
  by_cases hx : x ∈ tsupport (f : (Fin n → ℝ) → ℂ)
  · have hsub : Function.support (fun m => ρ m x) ⊆ s := by
      intro m hm
      rw [hs]
      exact ⟨x, hm, hx⟩
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_support_subset _ hsub, h4, one_smul]
  · simp [image_eq_zero_of_notMem_tsupport hx]
end GlobalTheory.CompanionTheory.DiracComb
