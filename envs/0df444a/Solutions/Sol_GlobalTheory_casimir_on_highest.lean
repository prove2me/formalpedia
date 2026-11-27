-- Prove2me | solution 1 for GlobalTheory.casimir_on_highest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:03.394811+00:00
-- url     : https://prove2.me/submissions/ca1a8438-4343-4362-a377-9e605bbb4cce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Sl2NonnegWeightOfHighestWeightVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (v : V) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) :
    ∑ i, ∑ j, e i j (e j i v) = ((∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) : ℤ) : K) • v := by
  have key : ∀ i j, e i j (e j i v) =
      ((if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) : K) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End K V => f v) (he i j j i)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, ↓reduceIte] at h1
      rw [hv i j h, map_zero, sub_zero, hκ, hκ] at h1
      rw [h1, if_pos h]
      push_cast
      rw [sub_smul]
    · subst h
      rw [if_neg (lt_irrefl i), if_pos rfl, hκ, map_smul, hκ, smul_smul]
      push_cast
      rfl
    · rw [hv j i h, map_zero, if_neg (lt_asymm h), if_neg h.ne']
      simp
  have hsum : (∑ i : Fin m, ∑ j : Fin m,
      (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ)) =
      ∑ i : Fin m, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
    have h2 : ∀ i j : Fin m, (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) =
        ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0)) -
          (if i < j then κ j else 0) := by
      intro i j
      by_cases h : i < j
      · simp [h, h.ne]
      · simp [h]
    simp_rw [h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul, nsmul_eq_mul]
    have hi := i.isLt
    have hc : ((m - 1 - (i : ℕ) : ℕ) : ℤ) = m - 1 - (i : ℕ) := by omega
    rw [hc]
    ring
  simp_rw [key]
  rw [← hsum, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_sum, Finset.sum_smul]
end GlobalTheory
