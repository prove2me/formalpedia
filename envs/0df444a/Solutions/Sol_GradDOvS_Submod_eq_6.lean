-- Prove2me | solution 1 for GradDOvS.Submod.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:24:25.047566+00:00
-- url     : https://prove2.me/submissions/26d88bd0-60f3-4820-aeb9-84132ca5b95b

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace Aux_GDSeq6

lemma abel (d : ℕ) (F xs : ℕ → ℝ) (hd : xs d = 0) :
    ∑ i ∈ Finset.range (d + 1), ((if i = 0 then 1 else xs (i - 1)) - xs i) * F i =
      F 0 + ∑ k ∈ Finset.range d, (F (k + 1) - F k) * xs k := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_true]
  have h1 := Finset.sum_range_succ' (fun i => xs i * F i) d
  have h2 := Finset.sum_range_succ (fun i => xs i * F i) d
  simp only [hd, zero_mul, add_zero] at h2
  have eL : ∑ i ∈ Finset.range d, (xs i - xs (i + 1)) * F (i + 1) =
      ∑ i ∈ Finset.range d, xs i * F (i + 1) - ∑ i ∈ Finset.range d, xs (i + 1) * F (i + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have eR : ∑ k ∈ Finset.range d, (F (k + 1) - F k) * xs k =
      ∑ i ∈ Finset.range d, xs i * F (i + 1) - ∑ i ∈ Finset.range d, xs i * F i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [eL, eR]
  linarith

end Aux_GDSeq6

open GradDOvS.Submod Aux_GDSeq6 in
theorem solution {d : ℕ} (f : Finset (Fin d) → ℝ) (x : Fin d → ℝ) (hx : x ∈ box d)
    (α : Equiv.Perm (Fin d)) (hα : IsConsistentPerm x α) :
    let xs : ℕ → ℝ := fun i => if h : i < d then x (α ⟨i, h⟩) else 0
    let w : ℕ → ℝ := fun i => (if i = 0 then 1 else xs (i - 1)) - xs i
    (lovaszWith f x α = ∑ i ∈ Finset.range (d + 1), w i * f (nbr α i)) ∧
      (∀ i ∈ Finset.range (d + 1), 0 ≤ w i) ∧
      (∑ i ∈ Finset.range (d + 1), w i = 1) ∧
      (∃ i ≤ d, f (nbr α i) ≤ lovaszWith f x α) := by
  intro xs w
  have hxs_lt : ∀ i (h : i < d), xs i = x (α ⟨i, h⟩) := fun i h => dif_pos h
  have hxs_ge : ∀ i, d ≤ i → xs i = 0 := fun i h => dif_neg (by omega)
  have hw0 : w 0 = 1 - xs 0 := by
    show (if (0:ℕ) = 0 then (1:ℝ) else xs (0 - 1)) - xs 0 = 1 - xs 0
    simp
  have hws : ∀ i, w (i + 1) = xs i - xs (i + 1) := by
    intro i
    show (if i + 1 = 0 then (1:ℝ) else xs (i + 1 - 1)) - xs (i + 1) = xs i - xs (i + 1)
    simp
  have hx01 : ∀ j, 0 ≤ x j ∧ x j ≤ 1 := fun j => ⟨hx.1 j, hx.2 j⟩
  have hxs01 : ∀ i, 0 ≤ xs i ∧ xs i ≤ 1 := by
    intro i
    by_cases h : i < d
    · rw [hxs_lt i h]; exact hx01 _
    · rw [hxs_ge i (by omega)]; norm_num
  set F : ℕ → ℝ := fun i => f (nbr α i) with hF
  have hab : ∀ G : ℕ → ℝ, ∑ i ∈ Finset.range (d + 1), w i * G i =
      G 0 + ∑ k ∈ Finset.range d, (G (k + 1) - G k) * xs k :=
    fun G => abel d G xs (hxs_ge d le_rfl)
  have hlov : lovaszWith f x α = ∑ i ∈ Finset.range (d + 1), w i * F i := by
    rw [hab F]
    unfold lovaszWith
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun k => (F (k + 1) - F k) * xs k) d]
    apply Finset.sum_congr rfl
    intro k _
    rw [hxs_lt k k.2]
  have hwnn : ∀ i ∈ Finset.range (d + 1), 0 ≤ w i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases i with _ | i
    · rw [hw0]; linarith [(hxs01 0).2]
    · rw [hws]
      by_cases h : i + 1 < d
      · rw [hxs_lt i (by omega), hxs_lt (i + 1) h]
        have := hα (show (⟨i, by omega⟩ : Fin d) ≤ ⟨i + 1, h⟩ from by
          rw [Fin.mk_le_mk]; omega)
        simp only [Function.comp_apply] at this
        linarith
      · rw [hxs_ge (i + 1) (by omega)]
        linarith [(hxs01 i).1]
  have hsum : ∑ i ∈ Finset.range (d + 1), w i = 1 := by
    have := hab (fun _ => 1)
    simp only [mul_one, sub_self, zero_mul, Finset.sum_const_zero, add_zero] at this
    exact this
  refine ⟨hlov, hwnn, hsum, ?_⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.range (d + 1)) F
    ⟨0, Finset.mem_range.2 (Nat.succ_pos d)⟩
  refine ⟨i0, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi0), ?_⟩
  rw [hlov]
  calc f (nbr α i0) = (∑ i ∈ Finset.range (d + 1), w i) * F i0 := by rw [hsum, one_mul]
    _ = ∑ i ∈ Finset.range (d + 1), w i * F i0 := Finset.sum_mul _ _ _
    _ ≤ ∑ i ∈ Finset.range (d + 1), w i * F i :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hmin i hi) (hwnn i hi))
