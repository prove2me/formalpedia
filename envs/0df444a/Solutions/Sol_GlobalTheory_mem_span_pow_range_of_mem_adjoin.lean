-- Prove2me | solution 1 for GlobalTheory.mem_span_pow_range_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:34.187157+00:00
-- url     : https://prove2.me/submissions/091ccd51-5f03-498a-bf8f-b268c4f63f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulMemAdjoinOfMemPowRange
import Theorems.Thm_GlobalTheory_mem_graded_of_mem_pow_range

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
theorem _root_.solution {K T : Type} [Field K] [CommRing T] [Algebra K T]
    (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] {m : ℕ} (x : Fin m → T) (hx : ∀ i, x i ∈ 𝒜 1)
    (k : ℕ) (t : T) (ht : t ∈ Algebra.adjoin K (Set.range x)) (htk : t ∈ 𝒜 k) :
    t ∈ Submodule.span K ((Set.range x) ^ k) := by
  have h1 : ∀ u ∈ Submonoid.closure (Set.range x), ∃ j : ℕ, u ∈ (Set.range x) ^ j := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem y hy => exact ⟨1, by simpa using hy⟩
    | one => exact ⟨0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      exact ⟨i + j, by rw [pow_add]; exact Set.mul_mem_mul hi hj⟩
  have h2 : ∀ u ∈ Submodule.span K (Submonoid.closure (Set.range x) : Set T),
      GradedAlgebra.proj 𝒜 k u ∈ Submodule.span K ((Set.range x) ^ k) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj⟩ := h1 y hy
      have hyj := mem_graded_of_mem_pow_range 𝒜 x hx j y hj
      rw [GradedAlgebra.proj_apply]
      by_cases hjk : j = k
      · subst hjk
        rw [DirectSum.decompose_of_mem_same 𝒜 hyj]
        exact Submodule.subset_span hj
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hyj hjk]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h3 : t ∈ Submodule.span K (Submonoid.closure (Set.range x) : Set T) := by
    rw [← Algebra.adjoin_eq_span]; exact ht
  have h4 := h2 t h3
  rwa [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 htk] at h4
end GlobalTheory
