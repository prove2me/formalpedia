-- Prove2me | solution 1 for GlobalTheory.Desc.exists_finiteType_away_of_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:31.2348+00:00
-- url     : https://prove2.me/submissions/09963717-93e7-476b-8a01-9025d1c1c8eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteTypeAwayOfAtPrime
import Theorems.Thm_GlobalTheory_Desc_finiteType_away_of_pow_mul_mem
import Theorems.Thm_GlobalTheory_Desc_exists_pow_mul_mem_of_finiteType_away
import Theorems.Thm_GlobalTheory_Desc_exists_smul_mem_of_finiteType_tensor
import Theorems.Thm_GlobalTheory_Desc_exists_mul_mem_of_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Desc
open scoped TensorProduct
namespace GlobalTheory.Desc
theorem _root_.solution (R C : Type) [CommRing R] [IsNoetherianRing R]
    [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hf : algebraMap R C f ≠ 0)
    (h₁ : Algebra.FiniteType R (Localization.Away (algebraMap R C f)))
    (h₂ : Algebra.FiniteType (Localization.AtPrime 𝔭)
      (TensorProduct R (Localization.AtPrime 𝔭) C)) :
    ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  classical
  obtain ⟨s₁, hs₁⟩ := exists_pow_mul_mem_of_finiteType_away f h₁
  obtain ⟨s₂, hs₂⟩ := exists_smul_mem_of_finiteType_tensor 𝔭.primeCompl h₂
  let B := Algebra.adjoin R ((s₁ ∪ s₂ : Finset C) : Set C)
  have hB₁ : Algebra.adjoin R (s₁ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have hB₂ : Algebra.adjoin R (s₂ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have : IsNoetherianRing B := isNoetherianRing_of_fg ⟨s₁ ∪ s₂, rfl⟩
  obtain ⟨g, hg, hgB⟩ := exists_mul_mem_of_mul_mem B _ hf 𝔭.primeCompl fun c =>
    (hs₂ c).imp fun r hr => ⟨hr.1, hB₂ hr.2⟩
  refine ⟨g, hg, finiteType_away_of_pow_mul_mem (s₁ ∪ s₂) _ fun c => ?_⟩
  have key : ∀ (n : ℕ) (c : C), algebraMap R C f ^ n * c ∈ B → algebraMap R C g ^ n * c ∈ B := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [pow_succ, mul_assoc] at hc
      have h := ih _ hc
      rw [mul_left_comm] at h
      rw [pow_succ', mul_assoc]
      exact hgB _ h
  obtain ⟨n, hn⟩ := hs₁ c
  exact ⟨n, key n c (hB₁ hn)⟩
end GlobalTheory.Desc
