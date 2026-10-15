-- Prove2me | solution 1 for OAI.FourRow.pair_stability_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:53:04.368175+00:00
-- url     : https://prove2.me/submissions/eaa890ac-538a-4a9b-8c6f-10422ed0886b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Permanent/Stability.lean:L56-L108
-- (upload_full_project.md Phase 4): solution for node OAI.FourRow.pair_stability_one. Inline helpers are the
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
theorem pairSq_identity (a b : Site → ℝ) :
    pairSq a b = rowSq a * rowSq b + rowDot a b ^ 2 -
      2 * ∑ j, (a j * b j) ^ 2 := by
  simp only [pairSq, pairEntries, rowSq, rowDot, Fin.sum_univ_six,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem rowDot_sq_le (a b : Site → ℝ) :
    rowDot a b ^ 2 ≤ rowSq a * rowSq b :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

theorem rowDot_sq_le_four (a b : Site → ℝ) :
    rowDot a b ^ 2 ≤ 4 * ∑ j, (a j * b j) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Site => (1 : ℝ)) (fun j => a j * b j)
  simpa [rowDot] using h

end FourRow
end

end OAI

-- ---- hoisted node ----
open OAI OAI.FourRow
open scoped BigOperators

theorem solution (a b : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (haq : rowSq a = 4) (hbq : rowSq b = 4) :
    rowDist a ≤ 9 * (24 - pairSq a b) := by
  let t := rowDot a b
  let s := ∑ j, (a j * b j) ^ 2
  let d := ∑ j, (a j - b j) ^ 2
  let e := ∑ j, (a j * b j - 1) ^ 2
  let D := 24 - pairSq a b
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (hb j)
  have ht2 : t ^ 2 ≤ 16 := by
    have h := rowDot_sq_le a b
    rw [haq, hbq] at h
    norm_num at h
    exact h
  have ht4 : t ≤ 4 := by nlinarith
  have htprod : 0 ≤ t * (4 - t) := mul_nonneg ht0 (by linarith)
  have hts : t ^ 2 ≤ 4 * s := rowDot_sq_le_four a b
  have hD : D = 8 - t ^ 2 + 2 * s := by
    dsimp [D, t, s]
    rw [pairSq_identity, haq, hbq]
    ring
  have hd : d = 8 - 2 * t := by
    have h : d = rowSq a + rowSq b - 2 * t := by
      dsimp [d, rowSq, t, rowDot]
      simp only [Fin.sum_univ_four]
      ring
    rw [h, haq, hbq]
    ring
  have he : e = s - 2 * t + 4 := by
    dsimp [e, s, t, rowDot]
    simp only [Fin.sum_univ_four]
    ring
  have hdD : d ≤ D := by nlinarith
  have heD : 2 * e ≤ D := by nlinarith
  have hpoint (j : Site) : (a j - 1) ^ 2 ≤
      8 * (a j - b j) ^ 2 + 2 * (a j * b j - 1) ^ 2 := by
    have haj : a j ^ 2 ≤ 4 := by
      calc
        a j ^ 2 ≤ rowSq a :=
          Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ j)
        _ = 4 := haq
    have h1 : (a j - 1) ^ 2 ≤ (a j ^ 2 - 1) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg (ha j) (show 0 ≤ a j + 2 by linarith [ha j]))
        (sq_nonneg (a j - 1))]
    have h2 : (a j ^ 2 - a j * b j) ^ 2 ≤ 4 * (a j - b j) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 4 - a j ^ 2 by linarith)
        (sq_nonneg (a j - b j))]
    nlinarith [sq_nonneg (a j ^ 2 - 2 * a j * b j + 1)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Site)) => hpoint j)
  have hbound : rowDist a ≤ 8 * d + 2 * e := by
    simpa only [rowDist, Finset.sum_add_distrib, ← Finset.mul_sum] using hs
  linarith
