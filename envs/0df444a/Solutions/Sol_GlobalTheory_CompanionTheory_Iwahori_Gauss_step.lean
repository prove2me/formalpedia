-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:28.262802+00:00
-- url     : https://prove2.me/submissions/dcfcc67a-52aa-4b7c-82d7-3b037c9f317c

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_eq_zero_of_mul_pieces
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_eq_zero_of_pieces_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_isUpper_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_isLowerUni_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_sub_one_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Gauss
open GlobalTheory.CompanionTheory.Iwahori
variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}
namespace GlobalTheory.CompanionTheory.Iwahori.Gauss
theorem _root_.solution (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ)
    (ih : ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b)
    (q : ι) (hq : wt q = m) (x : E) (hx : x ∈ J)
    (hH : ∀ i j, (m + 1 ≤ wt i ∨ m + 1 ≤ wt j) → P i * x * P j = 0) :
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ 1 + x = a * b := by
  have hl : ∀ i, m + 1 ≤ wt i → P i * x = 0 := fun i hi =>
    eq_zero_of_mul_pieces hP fun j => hH i j (Or.inl hi)
  have hr : ∀ j, m + 1 ≤ wt j → x * P j = 0 := fun j hj =>
    eq_zero_of_pieces_mul hP fun i => by rw [← mul_assoc]; exact hH i j (Or.inr hj)
  have hne : ∀ j, m + 1 ≤ wt j → P q * P j = 0 := fun j hj =>
    hP.orth q j (fun e => by subst e; omega)
  have hne' : ∀ j, m + 1 ≤ wt j → P j * P q = 0 := fun j hj =>
    hP.orth j q (fun e => by subst e; omega)
  have hQQ := hP.idem q
  obtain ⟨y, hy, h1, h2⟩ := hJ.inv (x * P q) (hJ.right_mem q x hx)
  obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ J, 1 + z = (1 + y) * (1 + x) :=
    ⟨(1 + y) * (1 + x) - 1,
      sub_one_mul_mem hJ (by rwa [add_sub_cancel_left]) (by rwa [add_sub_cancel_left]),
      by abel⟩
  have hAB : 1 + x = (1 + x * P q) * (1 + z) := by
    rw [hzdef, ← mul_assoc, h1, one_mul]
  have hzQ : z * P q = 0 := by
    have e : (1 + x) * P q = (1 + x * P q) * P q := by
      simp only [add_mul, one_mul, mul_assoc, hQQ]
    have : (1 + z) * P q = P q := by
      calc (1 + z) * P q = (1 + y) * ((1 + x) * P q) := by rw [hzdef, mul_assoc]
        _ = (1 + y) * ((1 + x * P q) * P q) := by rw [e]
        _ = ((1 + y) * (1 + x * P q)) * P q := by rw [mul_assoc]
        _ = P q := by rw [h2, one_mul]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzr : ∀ j, m + 1 ≤ wt j → z * P j = 0 := by
    intro j hj
    have e1 : (1 + x) * P j = P j := by rw [add_mul, one_mul, hr j hj, add_zero]
    have e2 : (1 + x * P q) * P j = P j := by
      rw [add_mul, one_mul, mul_assoc, hne j hj, mul_zero, add_zero]
    have e3 : (1 + y) * P j = P j := by
      calc (1 + y) * P j = (1 + y) * ((1 + x * P q) * P j) := by rw [e2]
        _ = ((1 + y) * (1 + x * P q)) * P j := by rw [mul_assoc]
        _ = P j := by rw [h2, one_mul]
    have : (1 + z) * P j = P j := by
      rw [hzdef, mul_assoc, e1, e3]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzl : ∀ i, m + 1 ≤ wt i → P i * z = 0 := by
    intro i hi
    have e1 : P i * (1 + x) = P i := by rw [mul_add, mul_one, hl i hi, add_zero]
    have e2 : P i * (1 + x * P q) = P i := by
      rw [mul_add, mul_one, ← mul_assoc, hl i hi, zero_mul, add_zero]
    have e3 : P i * (1 + y) = P i := by
      calc P i * (1 + y) = (P i * (1 + x * P q)) * (1 + y) := by rw [e2]
        _ = P i * ((1 + x * P q) * (1 + y)) := by rw [mul_assoc]
        _ = P i := by rw [h1, mul_one]
    have : P i * (1 + z) = P i := by
      rw [hzdef, ← mul_assoc, e3, e1]
    rw [mul_add, mul_one] at this
    simpa using this
  have hsJ : z - P q * z ∈ J := J.sub_mem hz (hJ.left_mem q z hz)
  have hsr : ∀ j, m ≤ wt j → (z - P q * z) * P j = 0 := by
    intro j hj
    rcases hj.eq_or_lt with h | h
    · have : j = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [sub_mul, hzQ, mul_assoc, hzQ, mul_zero, sub_zero]
    · rw [sub_mul, hzr j h, mul_assoc, hzr j h, mul_zero, sub_zero]
  have hsl : ∀ i, m ≤ wt i → P i * (z - P q * z) = 0 := by
    intro i hi
    rcases hi.eq_or_lt with h | h
    · have : i = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [mul_sub, ← mul_assoc, hQQ, sub_self]
    · rw [mul_sub, hzl i h, ← mul_assoc, hne' i h, zero_mul, sub_zero]
  have hS : ∀ i j, (m ≤ wt i ∨ m ≤ wt j) →
      P i * ((1 + (z - P q * z)) - 1) * P j = 0 := by
    intro i j hij
    rw [add_sub_cancel_left]
    rcases hij with h | h
    · rw [hsl i h, zero_mul]
    · rw [mul_assoc, hsr j h, mul_zero]
  obtain ⟨a', b', ha, hb, hau, hbl, hk⟩ :=
    ih (1 + (z - P q * z)) (by rwa [add_sub_cancel_left]) hS
  have hSC : (1 + (z - P q * z)) * (1 + P q * z) = 1 + z := by
    have : (1 + (z - P q * z)) * (1 + P q * z)
        = 1 + z + (z * P q) * z - P q * (z * P q) * z := by noncomm_ring
    rw [this, hzQ]
    simp
  have hA : IsUpper wt P (1 + x * P q) := by
    intro i j hij
    have hm : P i * (1 + x * P q) * P j = P i * P j + P i * x * (P q * P j) := by
      simp only [mul_add, add_mul, mul_one, mul_assoc]
    rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
    by_cases hjq : j = q
    · subst hjq
      rw [hl i (by omega), zero_mul]
    · rw [hP.orth q j (Ne.symm hjq), mul_zero]
  have hC : IsLowerUni wt P (1 + P q * z) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hm : P i * (1 + P q * z) * P j = P i * P j + (P i * P q) * (z * P j) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
      by_cases hiq : i = q
      · subst hiq
        rw [hzr j (by omega), mul_zero]
      · rw [hP.orth i q hiq, zero_mul]
    · have hm : P i * (1 + P q * z) * P i = P i * P i + (P i * P q) * (z * P i) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.idem]
      by_cases hiq : i = q
      · subst hiq
        rw [hzQ, mul_zero, add_zero]
      · rw [hP.orth i q hiq, zero_mul, add_zero]
  refine ⟨(1 + x * P q) * a', b' * (1 + P q * z), ?_, ?_, isUpper_mul hP hA hau,
    isLowerUni_mul hwt hP hbl hC, ?_⟩
  · exact sub_one_mul_mem hJ (by rw [add_sub_cancel_left]; exact hJ.right_mem q x hx) ha
  · exact sub_one_mul_mem hJ hb (by rw [add_sub_cancel_left]; exact hJ.left_mem q z hz)
  · rw [hAB, ← hSC, hk]
    simp only [mul_assoc]
end GlobalTheory.CompanionTheory.Iwahori.Gauss
