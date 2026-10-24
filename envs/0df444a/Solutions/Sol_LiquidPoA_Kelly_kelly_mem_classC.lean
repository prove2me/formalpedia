-- Prove2me | solution 1 for LiquidPoA.Kelly.kelly_mem_classC
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:50:11.832261+00:00
-- url     : https://prove2.me/submissions/dc8a8550-0474-4979-b27d-4aa8ff3e9739

import Definitions.Def_LiquidPoA_Kelly_Setting
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset Set LiquidPoA.Kelly

namespace D24KellyClass

namespace Core

theorem sum_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    ∑ j, Function.update s i b j = b + ∑ j ∈ univ.erase i, s j := by
  rw [← sum_erase_add _ _ (mem_univ i)]
  simp only [Function.update_self]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  exact Function.update_of_ne (mem_erase.1 hj).1 b s

theorem others_pos {n : ℕ} (s : Fin n → ℝ) (hs : InX s) (i : Fin n) :
    0 < ∑ j ∈ univ.erase i, s j := by
  obtain ⟨j, k, hjk, hj, hk⟩ := hs.2
  apply sum_pos'
  · intro l _
    exact hs.1 l
  · by_cases hji : j = i
    · exact ⟨k, mem_erase.2 ⟨by simpa [hji] using Ne.symm hjk, mem_univ _⟩, hk⟩
    · exact ⟨j, mem_erase.2 ⟨hji, mem_univ _⟩, hj⟩

end Core

lemma alloc_formula {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    allocIn (kelly n) s i = fun y => y / (y + ∑ j ∈ univ.erase i, s j) := by
  funext y
  simp [allocIn, kelly, Core.sum_update]

lemma pay_formula {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    payIn (kelly n) s i = fun y => y := by
  funext y
  simp [payIn, kelly]

lemma others_positive {n : ℕ} (s : Fin n → ℝ) (hs : IsSignal s) (i : Fin n)
    (hother : ∃ j, j ≠ i ∧ 0 < s j) : 0 < ∑ j ∈ univ.erase i, s j := by
  obtain ⟨j, hji, hj⟩ := hother
  apply sum_pos'
  · intro k _
    exact hs k
  · exact ⟨j, mem_erase.mpr ⟨hji, mem_univ _⟩, hj⟩

lemma frac_deriv (B y : ℝ) (hden : y + B ≠ 0) :
    HasDerivAt (fun z : ℝ => z / (z + B)) (B / (y + B) ^ 2) y := by
  simpa only [id_eq, one_mul, mul_one, add_sub_cancel_left] using
    (hasDerivAt_id y).fun_div ((hasDerivAt_id y).add_const B) hden

lemma frac_increasing (B : ℝ) (hB : 0 < B) :
    StrictMonoOn (fun y : ℝ => y / (y + B)) (Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  apply (div_lt_div_iff₀ (by linarith : 0 < x + B)
    (by linarith : 0 < y + B)).2
  nlinarith [mul_pos hB (sub_pos.mpr hxy)]

lemma frac_concave (B : ℝ) (hB : 0 < B) :
    ConcaveOn ℝ (Ici 0) (fun y : ℝ => y / (y + B)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change a * (x / (x + B)) + b * (y / (y + B)) ≤
    (a * x + b * y) / (a * x + b * y + B)
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hX : 0 < x + B := by linarith
  have hY : 0 < y + B := by linarith
  have hZ : 0 < a * x + b * y + B := by
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    linarith [mul_nonneg ha hx0, mul_nonneg hb hy0]
  have hbval : b = 1 - a := by linarith
  have hid : (a * x + b * y) / (a * x + b * y + B) -
      (a * (x / (x + B)) + b * (y / (y + B))) =
      B * a * b * (x - y) ^ 2 / ((x + B) * (y + B) * (a * x + b * y + B)) := by
    field_simp [ne_of_gt hX, ne_of_gt hY, ne_of_gt hZ]
    rw [hbval]
    ring
  have hpos : 0 ≤ B * a * b * (x - y) ^ 2 /
      ((x + B) * (y + B) * (a * x + b * y + B)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB.le ha) hb) (sq_nonneg _))
      (mul_pos (mul_pos hX hY) hZ).le
  linarith

lemma frac_diff (B : ℝ) (hB : 0 < B) :
    DifferentiableOn ℝ (fun y : ℝ => y / (y + B)) (Ici 0) := by
  intro y hy
  have hy0 : 0 ≤ y := hy
  exact (frac_deriv B y (by linarith)).differentiableAt.differentiableWithinAt

end D24KellyClass

theorem solution (n : ℕ) :
    IsRAMechanism (kelly n) ∧ InClassC (kelly n) := by
  constructor
  · refine {
      alloc_mem := ?_
      pay_nonneg := ?_
      anon_alloc := ?_
      anon_pay := ?_
      zero_sig := ?_
      alone := ?_
      alloc_incr := ?_
      pay_incr := ?_
      pay_cont_zero := ?_
      diff := ?_
      diff_alone := ?_
      deriv_pos := ?_ }
    · intro s hs
      change IsAllocation (fun i => s i / ∑ j, s j)
      refine ⟨fun i => div_nonneg (hs i) (sum_nonneg fun j _ => hs j), ?_⟩
      by_cases hzero : (∑ j, s j) = 0
      · right
        intro i
        simp [hzero]
      · left
        simp_rw [div_eq_mul_inv]
        rw [← sum_mul]
        exact mul_inv_cancel₀ hzero
    · intro s hs i
      exact hs i
    · intro σ s hs
      ext i
      change s (σ i) / (∑ j, s (σ j)) = s (σ i) / ∑ j, s j
      rw [Equiv.sum_comp σ]
    · intro σ s hs
      rfl
    · intro s hs i hi
      simp [kelly, hi]
    · intro i y hy
      change (Function.update (0 : Fin n → ℝ) i y i) /
        (∑ j, Function.update (0 : Fin n → ℝ) i y j) = 1
      rw [Function.update_self, D24KellyClass.Core.sum_update]
      simp [ne_of_gt hy]
    · intro s hs i hother
      rw [D24KellyClass.alloc_formula]
      exact D24KellyClass.frac_increasing _ (D24KellyClass.others_positive s hs i hother)
    · intro s hs i x hx y hy hxy
      simpa [payIn, kelly] using hxy
    · intro i
      rw [D24KellyClass.pay_formula]
      exact continuousWithinAt_id
    · intro s hs i hother
      rw [D24KellyClass.alloc_formula, D24KellyClass.pay_formula]
      exact ⟨D24KellyClass.frac_diff _ (D24KellyClass.others_positive s hs i hother),
        differentiableOn_id⟩
    · intro s hs i hothers
      have hB : (∑ j ∈ univ.erase i, s j) = 0 := by
        apply sum_eq_zero
        intro j hj
        exact hothers j (mem_erase.mp hj).1
      rw [D24KellyClass.alloc_formula, D24KellyClass.pay_formula, hB]
      constructor
      · intro y hy
        exact ((differentiableAt_id).div (differentiableAt_id.add_const 0)
          (by simpa using ne_of_gt hy)).differentiableWithinAt
      · exact differentiableOn_id
    · intro s hs i
      let B := ∑ j ∈ univ.erase i, s j
      have hB : 0 < B := D24KellyClass.Core.others_pos s hs i
      have hden : s i + B ≠ 0 := by linarith [hs.1 i]
      rw [D24KellyClass.alloc_formula]
      change 0 < derivWithin (fun y : ℝ => y / (y + B)) (Ici 0) (s i)
      rw [(D24KellyClass.frac_deriv B (s i) hden).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici 0 (s i) (hs.1 i))]
      exact div_pos hB (sq_pos_of_ne_zero hden)
  · intro s hs i hother
    rw [D24KellyClass.alloc_formula, D24KellyClass.pay_formula]
    exact ⟨D24KellyClass.frac_concave _ (D24KellyClass.others_positive s hs i hother),
      by
        refine ⟨convex_Ici 0, ?_⟩
        intro x hx y hy a b ha hb hab
        exact le_rfl⟩

#print axioms solution
