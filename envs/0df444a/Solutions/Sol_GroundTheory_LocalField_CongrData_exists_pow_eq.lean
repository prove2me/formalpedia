-- Prove2me | solution 1 for GroundTheory.LocalField.CongrData.exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:17.212653+00:00
-- url     : https://prove2.me/submissions/930accaf-8fca-4870-abbc-633998f7b6e7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_exists_sum_pow_prime_pow_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
variable {E : Subgroup G → Prop}
omit [Fintype G]
namespace GroundTheory.LocalField
namespace CongrData
theorem _root_.solution {p k : ℕ} (hp : p.Prime) {f : G → ℂ} (hf : CongrData ζ (p ^ k) s a f) :
    ∃ r ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ), f s ^ p ^ k = f (s ^ a) ^ p ^ k + p * r := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  obtain ⟨r1, hr1⟩ := exists_sum_pow_prime_pow_eq hp Finset.univ (fun i ↦ c i * β i) k
  obtain ⟨r2, hr2⟩ := exists_sum_pow_prime_pow_eq hp Finset.univ (fun i ↦ c i * β' i) k
  have heq : ∑ i, (c i * β i) ^ p ^ k = ∑ i, (c i * β' i) ^ p ^ k :=
    Finset.sum_congr rfl fun i _ ↦ by rw [mul_pow, mul_pow, hβ i]
  refine ⟨(r1 - r2 : Algebra.adjoin ℤ ({ζ} : Set ℂ)), (r1 - r2).2, ?_⟩
  have hx : f s = ((∑ i, c i * β i : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) := by
    rw [h1]
    push_cast
    rfl
  have hy : f (s ^ a) = ((∑ i, c i * β' i : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) := by
    rw [h2]
    push_cast
    rfl
  rw [hx, hy]
  have key : (∑ i, c i * β i) ^ p ^ k = (∑ i, c i * β' i) ^ p ^ k + p * (r1 - r2) := by
    rw [hr1, hr2, heq]
    ring
  have := congrArg (fun z : Algebra.adjoin ℤ ({ζ} : Set ℂ) ↦ (z : ℂ)) key
  simpa using this
end CongrData
end GroundTheory.LocalField
