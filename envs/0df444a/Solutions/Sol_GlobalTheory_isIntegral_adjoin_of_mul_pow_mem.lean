-- Prove2me | solution 1 for GlobalTheory.isIntegral_adjoin_of_mul_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:14.843798+00:00
-- url     : https://prove2.me/submissions/80079b63-70ab-4926-b493-1cf2b21a8e7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulMemAdjoinOfMemPowRange
import Theorems.Thm_GlobalTheory_mem_graded_of_mem_pow_range
import Theorems.Thm_GlobalTheory_mem_span_pow_range_of_mem_adjoin
import Theorems.Thm_GlobalTheory_exists_mul_mem_adjoin_of_mem_pow_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open scoped Pointwise
namespace GlobalTheory
theorem _root_.solution :
    (∀ (K T : Type) [Field K] [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m : ℕ) (x : Fin m → T), (∀ i, x i ∈ 𝒜 1) → (∃ i, x i ≠ 0) → ∀ (d : ℕ), ∀ s ∈ 𝒜 d, (∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) → IsIntegral (Algebra.adjoin K (Set.range x)) s) := by
  intro K T _ _ _ _ 𝒜 _ m x hx hne d s hsd hs
  obtain ⟨N, hN⟩ := exists_mul_mem_adjoin_of_mem_pow_range x s hs
  set S := Algebra.adjoin K (Set.range x) with hS
  have hP : ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k, t ∈ S := by
    intro k
    induction k with
    | zero =>
      intro t ht
      rw [pow_zero, Set.mem_one] at ht
      subst ht
      exact S.one_mem
    | succ k ih =>
      intro t ht
      rw [pow_succ] at ht
      obtain ⟨a, ha, b, hb, rfl⟩ := ht
      exact S.mul_mem (ih a ha) (Algebra.subset_adjoin hb)
  have hfin : ∀ k : ℕ, ((Set.range x) ^ k).Finite := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact Set.finite_one
    | succ k ih => rw [pow_succ]; exact ih.mul (Set.finite_range x)
  refine isIntegral_of_smul_mem_submodule (Submodule.span S ((Set.range x) ^ N)) ?_
    (Submodule.fg_span (hfin N)) s ?_
  · obtain ⟨i, hi⟩ := hne
    rw [Submodule.ne_bot_iff]
    exact ⟨x i ^ N, Submodule.subset_span (Set.pow_mem_pow ⟨i, rfl⟩), pow_ne_zero N hi⟩
  · intro t ht
    induction ht using Submodule.span_induction with
    | mem y hy =>
      have h1 := mem_span_pow_range_of_mem_adjoin 𝒜 x hx (d + N) (s * y) (hN y hy)
        (SetLike.mul_mem_graded hsd (mem_graded_of_mem_pow_range 𝒜 x hx N y hy))
      have h2 : Submodule.span K ((Set.range x) ^ (d + N)) ≤
          (Submodule.span S ((Set.range x) ^ N)).restrictScalars K := by
        rw [Submodule.span_le, pow_add]
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact Submodule.smul_mem (Submodule.span S ((Set.range x) ^ N)) (⟨a, hP d a ha⟩ : S)
          (Submodule.subset_span hb)
      exact h2 h1
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha
end GlobalTheory
