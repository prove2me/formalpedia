-- Prove2me | solution 1 for OAI.FiniteCircle.few_large_prime_divisors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:34:52.428016+00:00
-- url     : https://prove2.me/submissions/5ea493b0-3e6f-4253-9a82-7caf0a7eb615

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskBranching.lean:L11-L37
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.few_large_prime_divisors. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching

-- ---- from OAI.Combinatorics.FiniteCircle.MaskBranching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem few_large_prime_divisors {h : ℕ} (hh : 2 ≤ h)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hlarge : ∀ i, h ^ 3 ≤ p i) {β : ℤ} (hβ : β ≠ 0)
    (hsmall : β.natAbs < h ^ h) :
    3 * ((Finset.univ.filter fun i => (p i : ℤ) ∣ β).card) < h := by
  let s := Finset.univ.filter fun i => (p i : ℤ) ∣ β
  have hdvd : (∏ i ∈ s, p i) ∣ β.natAbs := by
    have heq : (∏ q ∈ s.image p, q) = ∏ i ∈ s, p i :=
      Finset.prod_image (fun _ _ _ _ hij => hinj hij)
    rw [← heq]
    apply Finset.prod_primes_dvd
    · intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (hp i).prime
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact Int.natCast_dvd.mp (Finset.mem_filter.mp hi).2
  have hprod : h ^ (3 * s.card) ≤ β.natAbs := by
    calc
      h ^ (3 * s.card) = ∏ i ∈ s, h ^ 3 := by simp [pow_mul]
      _ ≤ ∏ i ∈ s, p i := Finset.prod_le_prod' (fun i _ => hlarge i)
      _ ≤ β.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hβ) hdvd
  by_contra hn
  have hge : h ≤ 3 * s.card := Nat.le_of_not_gt hn
  have : h ^ h ≤ h ^ (3 * s.card) := Nat.pow_le_pow_right (by omega) hge
  omega

-- [generator] dropped (set where defined): attribute [reducible] MaskChildren

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.few_large_prime_divisors := @_root_.OAI.FiniteCircle.few_large_prime_divisors
