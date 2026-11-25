-- Prove2me | solution 1 for GlobalTheory.Per.single_mem_of_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:01:07.653069+00:00
-- url     : https://prove2.me/submissions/b7330170-99a6-49fc-95ba-9a93d17693a1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SingleMemOfSupportSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Per
namespace GlobalTheory.Per
theorem _root_.solution {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]
    (u : LL) (Λ : Submodule LL (ℤ → D)) (hu : u ≠ 0) (hr : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1)
    (hγ : ∀ x ∈ Λ, (fun k => u ^ k • x k) ∈ Λ) (S : Finset ℤ) :
    ∀ x ∈ Λ, (∀ k, k ∉ S → x k = 0) → ∀ k, Pi.single k (x k) ∈ Λ := by
  induction S using Finset.induction_on with
  | empty =>
    intro x _ hx k
    rw [hx k (by simp), Pi.single_zero]
    exact Λ.zero_mem
  | insert a S' ha ih =>
    intro x hxΛ hx

    have hne : ∀ k, k ≠ a → u ^ k - u ^ a ≠ 0 := by
      intro k hk h
      apply hr (k - a) (sub_ne_zero.mpr hk)
      rw [zpow_sub₀ hu, sub_eq_zero.mp h, div_self (zpow_ne_zero a hu)]
    have hyΛ : (fun k => u ^ k • x k) - u ^ a • x ∈ Λ := Λ.sub_mem (hγ x hxΛ) (Λ.smul_mem _ hxΛ)
    have hyv : ∀ k, ((fun k => u ^ k • x k) - u ^ a • x) k = (u ^ k - u ^ a) • x k := by
      intro k
      simp [sub_smul]
    have hy : ∀ k, k ∉ S' → ((fun k => u ^ k • x k) - u ^ a • x) k = 0 := by
      intro k hk
      rw [hyv]
      by_cases hka : k = a
      · rw [hka, sub_self, zero_smul]
      · rw [hx k (by simp [hka, hk]), smul_zero]
    have hoff : ∀ k, k ≠ a → Pi.single k (x k) ∈ Λ := by
      intro k hk
      have h1 := ih _ hyΛ hy k
      rw [hyv] at h1
      have e : Pi.single k (x k) =
          (u ^ k - u ^ a)⁻¹ • (Pi.single k ((u ^ k - u ^ a) • x k) : ℤ → D) := by
        rw [Pi.single_smul, smul_smul, inv_mul_cancel₀ (hne k hk), one_smul]
      rw [e]
      exact Λ.smul_mem _ h1
    intro k
    by_cases hka : k = a
    · rw [hka]
      have hsum : (∑ j ∈ S', Pi.single j (x j)) ∈ Λ :=
        Λ.sum_mem (fun j hj => hoff j (by rintro rfl; exact ha hj))
      have e : Pi.single a (x a) = x - ∑ j ∈ S', Pi.single j (x j) := by
        funext j
        rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single]
        by_cases hjS : j ∈ S'
        · have hja : j ≠ a := by rintro rfl; exact ha hjS
          simp [hjS, hja]
        · by_cases hja : j = a
          · rw [hja]
            simp [ha]
          · simp [hjS, hja, hx j (by simp [hja, hjS])]
      rw [e]
      exact Λ.sub_mem hxΛ hsum
    · exact hoff k hka
end GlobalTheory.Per
