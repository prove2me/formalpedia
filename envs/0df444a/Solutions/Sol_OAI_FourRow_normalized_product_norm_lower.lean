-- Prove2me | solution 1 for OAI.FourRow.normalized_product_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:56:53.10904+00:00
-- url     : https://prove2.me/submissions/bc100fe7-1e14-4c57-ae80-373d3d11fc57

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Permanent/Norm.lean:L112-L133
-- (upload_full_project.md Phase 4): solution for node OAI.FourRow.normalized_product_norm_lower. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability

-- ---- inline helpers from OAI.Combinatorics.Permanent.Stability ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Quantitative exponent-two stability estimates. -/
theorem rowDist_nonneg (a : Site → ℝ) : 0 ≤ rowDist a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end FourRow
end

end OAI

-- ---- inline helpers from OAI.Combinatorics.Permanent.Norm ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Below-two control by the tangent bound for the exponential. -/
theorem scalar_rpow_lower (x δ : ℝ) (hx : 0 ≤ x) (hδ : 0 ≤ δ)
    (hp : 0 < 2 - δ) :
    x ^ 2 - δ * x ^ 2 * (x - 1) ≤ x ^ (2 - δ) := by
  rcases eq_or_lt_of_le hx with hx | hx
  · subst x
    simp [Real.zero_rpow (ne_of_gt hp)]
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hδ
  calc
    x ^ 2 - δ * x ^ 2 * (x - 1) = x ^ 2 * (1 - δ * (x - 1)) := by ring
    _ ≤ x ^ 2 * (1 - δ * Real.log x) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg x)
    _ ≤ x ^ 2 * Real.exp (Real.log x * (-δ)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
      nlinarith [Real.add_one_le_exp (Real.log x * (-δ))]
    _ = x ^ (2 - δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_two, Real.rpow_def_of_pos hx]

theorem normalized_entry_le (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hq : rowSq a = 4) (j : Site) : a j ≤ 2 := by
  have h : a j ^ 2 ≤ 4 := by
    calc
      a j ^ 2 ≤ rowSq a :=
        Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ j)
      _ = 4 := hq
  exact (sq_le_sq₀ (ha j) (by norm_num : (0 : ℝ) ≤ 2)).mp (by norm_num; exact h)

theorem cubic_sum_bound (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hq : rowSq a = 4) :
    (∑ j, a j ^ 2 * (a j - 1)) ≤ (5 / 2) * rowDist a := by
  have hpoint (j : Site) : a j ^ 2 * (a j - 1) ≤
      (5 / 2) * (a j - 1) ^ 2 + (a j ^ 2 - 1) / 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - a j by linarith [normalized_entry_le a ha hq j])
      (sq_nonneg (a j - 1))]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Site)) => hpoint j)
  simp only [rowSq, Fin.sum_univ_four] at hq
  simp only [rowDist, Fin.sum_univ_four] at hsum ⊢
  linarith

theorem lpNorm_nonneg (p : ℝ) (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j) :
    0 ≤ lpNorm p a :=
  Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg
    (ha j) _) (by norm_num)) _

theorem lpNorm_lower (p : ℝ) (a : Site → ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : ∀ j, 0 ≤ a j) (hq : rowSq a = 4) :
    1 - (5 * (2 - p) / 8) * rowDist a ≤ lpNorm p a := by
  have hp0 : 0 < p := by linarith
  have hδ : 0 ≤ 2 - p := by linarith
  have hraw : 1 - (5 * (2 - p) / 8) * rowDist a ≤
      (∑ j, (a j) ^ p) / 4 := by
    have hpoint (j : Site) := scalar_rpow_lower (a j) (2 - p) (ha j) hδ (by linarith)
    have hs : (∑ j, (a j ^ 2 - (2 - p) * a j ^ 2 * (a j - 1))) ≤
        ∑ j, a j ^ p := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [show (2 : ℝ) - (2 - p) = p by ring] using hpoint j
    have hpoly := cubic_sum_bound a ha hq
    calc
      1 - (5 * (2 - p) / 8) * rowDist a =
          (4 - (2 - p) * ((5 / 2) * rowDist a)) / 4 := by ring
      _ ≤ (4 - (2 - p) * (∑ j, a j ^ 2 * (a j - 1))) / 4 := by
        gcongr
      _ = (∑ j, (a j ^ 2 - (2 - p) * a j ^ 2 * (a j - 1))) / 4 := by
        rw [Finset.sum_sub_distrib]
        simp_rw [mul_assoc (2 - p), ← Finset.mul_sum]
        rw [show (∑ j, a j ^ 2) = 4 from hq]
      _ ≤ (∑ j, a j ^ p) / 4 := by gcongr
  let L := 1 - (5 * (2 - p) / 8) * rowDist a
  have hL1 : L ≤ 1 := by
    dsimp [L]
    have := mul_nonneg hδ (rowDist_nonneg a)
    nlinarith
  by_cases hL0 : 0 < L
  · have hroot : L ≤ L ^ (1 / p) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hL0 hL1
        (show (1 : ℝ) / p ≤ 1 by rw [div_le_one hp0]; exact hp1)
      simpa only [Real.rpow_one] using h
    exact hroot.trans (Real.rpow_le_rpow (le_of_lt hL0) hraw (by positivity))
  · exact (le_of_not_gt hL0).trans (lpNorm_nonneg p a ha)
theorem one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (e : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ e i) (h1 : ∀ i ∈ s, e i ≤ 1) :
    1 - ∑ i ∈ s, e i ≤ ∏ i ∈ s, (1 - e i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have he0 := h0 i (Finset.mem_insert_self _ _)
    have he1 := h1 i (Finset.mem_insert_self _ _)
    have hs0 : ∀ j ∈ s, 0 ≤ e j := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have hs1 : ∀ j ∈ s, e j ≤ 1 := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have hsum0 : 0 ≤ ∑ j ∈ s, e j := Finset.sum_nonneg hs0
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    calc
      1 - (e i + ∑ j ∈ s, e j) ≤ (1 - e i) * (1 - ∑ j ∈ s, e j) := by
        nlinarith [mul_nonneg he0 hsum0]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih hs0 hs1) (by linarith)

theorem normalized_rowDist_le (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hq : rowSq a = 4) : rowDist a ≤ 8 := by
  simp only [rowSq, Fin.sum_univ_four] at hq
  simp only [rowDist, Fin.sum_univ_four]
  nlinarith [ha 0, ha 1, ha 2, ha 3]

end FourRow
end

end OAI

-- ---- hoisted node ----
open OAI OAI.FourRow
open scoped BigOperators

theorem solution (p : ℝ) (hp0 : 9 / 5 ≤ p) (hp2 : p ≤ 2)
    (f : Functions) (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    1 - (5 * (2 - p) / 8) * totalDist f ≤ ∏ i, lpNorm p (f i) := by
  let e : Site → ℝ := fun i => (5 * (2 - p) / 8) * rowDist (f i)
  have he0 (i : Site) : 0 ≤ e i := by
    dsimp [e]
    exact mul_nonneg (by linarith) (rowDist_nonneg _)
  have he1 (i : Site) : e i ≤ 1 := by
    have := normalized_rowDist_le (f i) (hf i) (hn i)
    have := rowDist_nonneg (f i)
    dsimp [e]
    nlinarith [mul_nonneg (show 0 ≤ p - 9 / 5 by linarith)
      (rowDist_nonneg (f i))]
  have hb := one_sub_sum_le_prod Finset.univ e (fun i _ => he0 i) (fun i _ => he1 i)
  have hp : ∏ i, (1 - e i) ≤ ∏ i, lpNorm p (f i) := by
    apply Finset.prod_le_prod
    · intro i _; linarith [he1 i]
    · intro i _; exact lpNorm_lower p (f i) (by linarith) hp2 (hf i) (hn i)
  have heq : ∑ i, e i = (5 * (2 - p) / 8) * totalDist f := by
    simp only [e, totalDist, Finset.mul_sum]
  rw [heq] at hb
  exact hb.trans hp
