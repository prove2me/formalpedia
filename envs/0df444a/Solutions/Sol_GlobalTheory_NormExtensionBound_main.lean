-- Prove2me | solution 1 for GlobalTheory.NormExtensionBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:44.548425+00:00
-- url     : https://prove2.me/submissions/a2925fc2-a92e-4b7c-8791-6e1828250727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeOneOfExtension
import Theorems.Thm_GlobalTheory_NormExtensionBound_exists_extension
import Theorems.Thm_GlobalTheory_NormExtensionBound_norm_le_one_of_extension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormExtensionBound
open scoped Pointwise
namespace GlobalTheory.NormExtensionBound
theorem _root_.solution : ∀ (p : ℕ) [Fact (Nat.Prime p)] (A B : Type) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)]
    (𝔷 : Ideal B), Function.Injective (algebraMap A B) →
    (∀ (b : B), (∀ (σ : B ≃ₐ[A] B), σ b = b) → b ∈ Set.range (algebraMap A B)) →
    Ideal.IsMaximal 𝔷 → ∀ (ev : A →+* PadicAlgCl p), (∀ (a : A), ‖ev a‖ ≤ (1 : ℝ)) →
    (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < (1 : ℝ)) →
    ∃ (ev' : B →+* PadicAlgCl p), (∀ (a : A), ev' (algebraMap A B a) = ev a) ∧
      (∀ (b : B), ‖ev' b‖ ≤ (1 : ℝ)) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < (1 : ℝ) := by
  intro p _ A B _ _ _ _ _ _ _ 𝔷 hinj hfix hmax ev h1 h2
  obtain ⟨e, he⟩ := exists_extension hinj ev
  have hle := norm_le_one_of_extension ev h1 e he
  let m : Ideal B :=
    { carrier := {b | ‖e b‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖e (a + b)‖ < 1
        rw [map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        show ‖e (c * b)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hb }
  have hm : ∀ b, b ∈ m ↔ ‖e b‖ < 1 := fun _ => Iff.rfl
  have hmne : m ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hm]
    simp
  have hmu : m.under A = IsLocalRing.maximalIdeal A := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hmne)
    intro a ha
    rw [Ideal.mem_comap, hm, he]
    exact h2 a ha
  haveI hmm : m.IsPrime := ⟨hmne, fun {a b} hab => by
    rw [hm, map_mul, norm_mul] at hab
    by_contra hc
    rw [not_or, hm, hm, not_lt, not_lt] at hc
    exact absurd hab (not_lt.2 (one_le_mul_of_one_le_of_one_le hc.1 hc.2))⟩
  have hzu : 𝔷.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) 𝔷)
  haveI : Algebra.IsInvariant A B (B ≃ₐ[A] B) := ⟨fun b hb => hfix b hb⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B (B ≃ₐ[A] B) 𝔷 m
    (hzu.trans hmu.symm)
  refine ⟨e.comp (g : B →+* B), fun a => ?_, fun b => hle _, fun b hb => ?_⟩
  · simp [he]
  · have : g • b ∈ m := by
      rw [hg]
      exact Ideal.smul_mem_pointwise_smul g b 𝔷 hb
    exact this
end GlobalTheory.NormExtensionBound
