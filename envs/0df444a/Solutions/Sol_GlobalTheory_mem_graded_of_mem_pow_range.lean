-- Prove2me | solution 1 for GlobalTheory.mem_graded_of_mem_pow_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:50.11402+00:00
-- url     : https://prove2.me/submissions/d1ae8500-6c74-4c03-88aa-b6c3460cd16b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulMemAdjoinOfMemPowRange

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
    (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] {m : ℕ} (x : Fin m → T) (hx : ∀ i, x i ∈ 𝒜 1) :
    ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k, t ∈ 𝒜 k := by
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [pow_zero, Set.mem_one] at ht
    subst ht
    exact SetLike.one_mem_graded 𝒜
  | succ k ih =>
    intro t ht
    rw [pow_succ] at ht
    obtain ⟨a, ha, b, ⟨i, rfl⟩, rfl⟩ := ht
    exact SetLike.mul_mem_graded (ih a ha) (hx i)
end GlobalTheory
