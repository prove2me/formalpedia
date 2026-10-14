-- Prove2me | solution 1 for OAI.FourRow.robust_permanent
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T15:52:34.390426+00:00
-- url     : https://prove2.me/submissions/8368081b-101a-48be-82d0-6d0d0895475a

import Mathlib
import Definitions.Def_FourRowPermanent

set_option autoImplicit false

open OAI.FourRow

noncomputable section

namespace OAI.FourRow.Sol
open OAI.FourRow

/-- Squared Euclidean length of a row. -/
def rowSq (a : Site → ℝ) : ℝ := ∑ j, a j ^ 2

/-- Squared distance of a row from the constant row `1`. -/
def rowDist (a : Site → ℝ) : ℝ := ∑ j, (a j - 1) ^ 2

/-- Total squared distance of a matrix from the all-ones matrix. -/
def totalDist (f : Functions) : ℝ := ∑ i, rowDist (f i)

/-- The uniform law on the 24 permutations. -/
def uniformLaw : Law := fun _ => 1 / 24

end OAI.FourRow.Sol

namespace OAI.FourRow.Sol

/-! ## Part A: exponent-two permanent inequality with stability (uniform law) -/

/-- Pair entry `x_{j,k}(a,b) = a j * b k + a k * b j`. -/
def A_px (a b : Site → ℝ) (j k : Site) : ℝ := a j * b k + a k * b j

/-- `pairSq(a,b) = Σ_{j<k} x_{j,k}(a,b)^2`. -/
def A_pairSq (a b : Site → ℝ) : ℝ :=
  A_px a b 0 1 ^ 2 + A_px a b 0 2 ^ 2 + A_px a b 0 3 ^ 2 +
  A_px a b 1 2 ^ 2 + A_px a b 1 3 ^ 2 + A_px a b 2 3 ^ 2

/-- Cauchy–Schwarz for six terms. -/
theorem A_cs6 (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℝ) :
    (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 + x5 * y5) ^ 2 ≤
      (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2) *
      (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2 + y5 ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ![x0, x1, x2, x3, x4, x5]
    ![y0, y1, y2, y3, y4, y5]
  simpa [Fin.sum_univ_six] using h

/-- Each entry of a nonnegative row with `rowSq = 4` is at most `2`. -/
theorem A_entry_le_two (a : Site → ℝ) (hn : rowSq a = 4) (j : Site) :
    a j ≤ 2 := by
  have h1 : a j ^ 2 ≤ rowSq a := by
    unfold rowSq
    exact Finset.single_le_sum (f := fun k => a k ^ 2) (fun k _ => sq_nonneg (a k))
      (Finset.mem_univ j)
  nlinarith

/-- The ring identity `pairSq = rowSq a * rowSq b + ⟨a,b⟩² − 2 Σ a_j² b_j²`. -/
theorem A_pairSq_eq (a b : Site → ℝ) :
    A_pairSq a b = rowSq a * rowSq b + (∑ j, a j * b j) ^ 2 - 2 * ∑ j, (a j * b j) ^ 2 := by
  simp only [A_pairSq, A_px, rowSq, Fin.sum_univ_four]
  ring

/-- `⟨a,b⟩² ≤ 4 Σ (a_j b_j)²`. -/
theorem A_inner_sq_le_four (a b : Site → ℝ) :
    (∑ j, a j * b j) ^ 2 ≤ 4 * ∑ j, (a j * b j) ^ 2 := by
  simp only [Fin.sum_univ_four]
  nlinarith [sq_nonneg (a 0 * b 0 - a 1 * b 1), sq_nonneg (a 0 * b 0 - a 2 * b 2),
    sq_nonneg (a 0 * b 0 - a 3 * b 3), sq_nonneg (a 1 * b 1 - a 2 * b 2),
    sq_nonneg (a 1 * b 1 - a 3 * b 3), sq_nonneg (a 2 * b 2 - a 3 * b 3)]

/-- `⟨a,b⟩² ≤ rowSq a * rowSq b`. -/
theorem A_inner_sq_le_rowSq (a b : Site → ℝ) :
    (∑ j, a j * b j) ^ 2 ≤ rowSq a * rowSq b :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

/-- Basic facts on `t = ⟨a,b⟩` and `s = Σ (a_j b_j)^2` for normalized nonnegative rows. -/
theorem A_ts_facts (a b : Site → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hna : rowSq a = 4) (hnb : rowSq b = 4) :
    0 ≤ ∑ j, a j * b j ∧ ∑ j, a j * b j ≤ 4 ∧
      (∑ j, a j * b j) ^ 2 ≤ 4 * ∑ j, (a j * b j) ^ 2 := by
  have h0 : 0 ≤ ∑ j, a j * b j := Finset.sum_nonneg (fun j _ => mul_nonneg (ha j) (hb j))
  have h1 := A_inner_sq_le_rowSq a b
  rw [hna, hnb] at h1
  refine ⟨h0, ?_, A_inner_sq_le_four a b⟩
  nlinarith

/-- `pairSq(a,b) ≤ 24` for normalized nonnegative rows. -/
theorem A_pairSq_le (a b : Site → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hna : rowSq a = 4) (hnb : rowSq b = 4) : A_pairSq a b ≤ 24 := by
  obtain ⟨h0, h4, hs⟩ := A_ts_facts a b ha hb hna hnb
  rw [A_pairSq_eq, hna, hnb]
  nlinarith

/-- `0 ≤ pairSq(a,b)`. -/
theorem A_pairSq_nonneg (a b : Site → ℝ) : 0 ≤ A_pairSq a b := by
  unfold A_pairSq
  positivity

/-- Pointwise stability estimate. -/
theorem A_pointwise (x y : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (x - 1) ^ 2 ≤ 8 * (x - y) ^ 2 + 2 * (x * y - 1) ^ 2 := by
  have h1 : (x - 1) ^ 2 ≤ (x ^ 2 - 1) ^ 2 := by
    have : (x ^ 2 - 1) ^ 2 = (x - 1) ^ 2 * (x + 1) ^ 2 := by ring
    rw [this]
    have h2 : 1 ≤ (x + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (x - 1)]
  have h2 : (x ^ 2 - 1) ^ 2 ≤ 2 * (x ^ 2 - x * y) ^ 2 + 2 * (x * y - 1) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - x * y - (x * y - 1))]
  have h3 : (x ^ 2 - x * y) ^ 2 ≤ 4 * (x - y) ^ 2 := by
    have : (x ^ 2 - x * y) ^ 2 = x ^ 2 * (x - y) ^ 2 := by ring
    rw [this]
    have hx4 : x ^ 2 ≤ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right hx4 (sq_nonneg _)
  linarith

/-- Stability for one row: `rowDist a ≤ 9 (24 − pairSq(a,b))`. -/
theorem A_rowDist_le (a b : Site → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hna : rowSq a = 4) (hnb : rowSq b = 4) :
    rowDist a ≤ 9 * (24 - A_pairSq a b) := by
  obtain ⟨h0, h4, hs⟩ := A_ts_facts a b ha hb hna hnb
  have hpt : rowDist a ≤ ∑ j, (8 * (a j - b j) ^ 2 + 2 * (a j * b j - 1) ^ 2) := by
    unfold rowDist
    exact Finset.sum_le_sum (fun j _ =>
      A_pointwise (a j) (b j) (ha j) (A_entry_le_two a hna j))
  have hexp : ∑ j, (8 * (a j - b j) ^ 2 + 2 * (a j * b j - 1) ^ 2) =
      8 * rowSq a + 8 * rowSq b - 20 * ∑ j, a j * b j + 2 * ∑ j, (a j * b j) ^ 2 + 8 := by
    simp only [rowSq, Fin.sum_univ_four]
    ring
  rw [hexp, hna, hnb] at hpt
  rw [A_pairSq_eq, hna, hnb]
  nlinarith

/-- Stability for a pair of rows. -/
theorem A_pair_stability (a b : Site → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hna : rowSq a = 4) (hnb : rowSq b = 4) :
    rowDist a + rowDist b ≤ 18 * (24 - A_pairSq a b) := by
  have h1 := A_rowDist_le a b ha hb hna hnb
  have h2 := A_rowDist_le b a hb ha hnb hna
  have h3 : A_pairSq b a = A_pairSq a b := by
    simp only [A_pairSq, A_px]
    ring
  rw [h3] at h2
  linarith

theorem A_sum_perm_succ (n : ℕ) (g : Equiv.Perm (Fin (n+1)) → ℝ) :
    ∑ π, g π = ∑ p : Fin (n+1), ∑ σ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (p, σ)) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]

/-- Generalized Laplace expansion of the 4×4 permanent along the first two rows. -/
theorem A_pair_expansion (f : Functions) :
    ∑ π : Perm, ∏ i, f i (π i) =
      A_px (f 0) (f 1) 0 1 * A_px (f 2) (f 3) 2 3 +
      A_px (f 0) (f 1) 0 2 * A_px (f 2) (f 3) 1 3 +
      A_px (f 0) (f 1) 0 3 * A_px (f 2) (f 3) 1 2 +
      A_px (f 0) (f 1) 1 2 * A_px (f 2) (f 3) 0 3 +
      A_px (f 0) (f 1) 1 3 * A_px (f 2) (f 3) 0 2 +
      A_px (f 0) (f 1) 2 3 * A_px (f 2) (f 3) 0 1 := by
  simp only [A_sum_perm_succ, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fin.sum_univ_succ, Fintype.sum_unique, mul_one]
  simp [Equiv.swap_apply_def, A_px]
  ring

/-- Cauchy–Schwarz on the pair expansion: `(Σ_π ∏ f)² ≤ pairSq(f0,f1) · pairSq(f2,f3)`. -/
theorem A_perm_sum_sq_le (f : Functions) :
    (∑ π : Perm, ∏ i, f i (π i)) ^ 2 ≤ A_pairSq (f 0) (f 1) * A_pairSq (f 2) (f 3) := by
  rw [A_pair_expansion]
  have h := A_cs6 (A_px (f 0) (f 1) 0 1) (A_px (f 0) (f 1) 0 2) (A_px (f 0) (f 1) 0 3)
    (A_px (f 0) (f 1) 1 2) (A_px (f 0) (f 1) 1 3) (A_px (f 0) (f 1) 2 3)
    (A_px (f 2) (f 3) 2 3) (A_px (f 2) (f 3) 1 3) (A_px (f 2) (f 3) 1 2)
    (A_px (f 2) (f 3) 0 3) (A_px (f 2) (f 3) 0 2) (A_px (f 2) (f 3) 0 1)
  have hV : A_pairSq (f 2) (f 3) =
      A_px (f 2) (f 3) 2 3 ^ 2 + A_px (f 2) (f 3) 1 3 ^ 2 + A_px (f 2) (f 3) 1 2 ^ 2 +
      A_px (f 2) (f 3) 0 3 ^ 2 + A_px (f 2) (f 3) 0 2 ^ 2 + A_px (f 2) (f 3) 0 1 ^ 2 := by
    unfold A_pairSq
    ring
  rw [hV]
  exact h

/-- The uniform permanent expectation is `(Σ_π ∏ f)/24`. -/
theorem A_permExp_uniform (f : Functions) :
    permanentExpectation uniformLaw f = (∑ π : Perm, ∏ i, f i (π i)) / 24 := by
  unfold permanentExpectation uniformLaw
  rw [← Finset.mul_sum]
  ring

/-- The final real-number step of Part A. -/
theorem A_final_step (S U V T : ℝ) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hU24 : U ≤ 24) (hV24 : V ≤ 24)
    (hCS : S ^ 2 ≤ U * V) (hT : T ≤ 18 * (48 - U - V)) :
    S / 24 ≤ 1 - T / 1728 := by
  have hUV : U * V ≤ 12 * (U + V) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hU24) hV0, mul_nonneg (sub_nonneg.2 hV24) hU0]
  have hP2 : (S / 24) ^ 2 ≤ 1 - T / 864 := by
    have h1 : (S / 24) ^ 2 = S ^ 2 / 576 := by ring
    rw [h1, div_le_iff₀ (by norm_num : (0:ℝ) < 576)]
    nlinarith
  have hT864 : T ≤ 864 := by nlinarith [sq_nonneg (S / 24)]
  have hc : 0 ≤ 1 - T / 1728 := by linarith
  have hsq : (S / 24) ^ 2 ≤ (1 - T / 1728) ^ 2 := by nlinarith [sq_nonneg T]
  exact le_of_sq_le_sq hsq hc

/-- Part A: exponent-two permanent inequality with stability, uniform law. -/
theorem uniform_stability (f : Functions) (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation uniformLaw f ≤ 1 - totalDist f / 1728 := by
  have hU0 := A_pairSq_nonneg (f 0) (f 1)
  have hV0 := A_pairSq_nonneg (f 2) (f 3)
  have hU24 := A_pairSq_le _ _ (hf 0) (hf 1) (hn 0) (hn 1)
  have hV24 := A_pairSq_le _ _ (hf 2) (hf 3) (hn 2) (hn 3)
  have hsU := A_pair_stability _ _ (hf 0) (hf 1) (hn 0) (hn 1)
  have hsV := A_pair_stability _ _ (hf 2) (hf 3) (hn 2) (hn 3)
  have hT : totalDist f = rowDist (f 0) + rowDist (f 1) + (rowDist (f 2) + rowDist (f 3)) := by
    unfold totalDist
    rw [Fin.sum_univ_four]
    ring
  rw [A_permExp_uniform]
  exact A_final_step _ _ _ _ hU0 hV0 hU24 hV24 (A_perm_sum_sq_le f) (by linarith)

end OAI.FourRow.Sol

namespace OAI.FourRow.Sol

/-! ## Part B: perturbation using exactly uniform marginals -/

/-- Each entry of a nonnegative row with `rowSq = 4` is at most `2`. -/
theorem B_entry_le_two (a : Site → ℝ) (_ha : ∀ j, 0 ≤ a j) (hn : rowSq a = 4) (j : Site) :
    a j ≤ 2 := by
  have h1 : a j ^ 2 ≤ rowSq a := by
    unfold rowSq
    exact Finset.single_le_sum (f := fun k => a k ^ 2) (fun k _ => sq_nonneg (a k))
      (Finset.mem_univ j)
  nlinarith [h1]

/-- Cauchy–Schwarz type bound `(x c + y)^2 ≤ 5 (x^2 + y^2)` when `c^2 ≤ 4`. -/
theorem B_cs_aux (x y c : ℝ) (hc : c ^ 2 ≤ 4) : (x * c + y) ^ 2 ≤ 5 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y * c),
    mul_le_mul_of_nonneg_left hc (add_nonneg (sq_nonneg x) (sq_nonneg y))]

/-- Product remainder bound for four entries in `[0,2]`. -/
theorem B_prod_remainder (a0 a1 a2 a3 : ℝ) (h1 : 0 ≤ a1) (h3 : 0 ≤ a3)
    (h1' : a1 ≤ 2) (h3' : a3 ≤ 2) :
    |a0 * a1 * a2 * a3 - (1 + ((a0 - 1) + (a1 - 1) + (a2 - 1) + (a3 - 1)))| ≤
      3 * ((a0 - 1) ^ 2 + (a1 - 1) ^ 2 + (a2 - 1) ^ 2 + (a3 - 1) ^ 2) := by
  have hc1 : a1 ^ 2 ≤ 4 := by nlinarith
  have hc3 : a3 ^ 2 ≤ 4 := by nlinarith
  have hA := B_cs_aux (a0 - 1) (a1 - 1) a1 hc1
  have hB := B_cs_aux (a2 - 1) (a3 - 1) a3 hc3
  have key : a0 * a1 * a2 * a3 - (1 + ((a0 - 1) + (a1 - 1) + (a2 - 1) + (a3 - 1))) =
      (a0 - 1) * (a1 - 1) + (a2 - 1) * (a3 - 1) +
        ((a0 - 1) * a1 + (a1 - 1)) * ((a2 - 1) * a3 + (a3 - 1)) := by ring
  rw [key, abs_le]
  constructor
  · nlinarith [sq_nonneg (a0 + a1 - 2), sq_nonneg (a2 + a3 - 2),
      sq_nonneg (((a0 - 1) * a1 + (a1 - 1)) + ((a2 - 1) * a3 + (a3 - 1)))]
  · nlinarith [sq_nonneg (a0 - a1), sq_nonneg (a2 - a3),
      sq_nonneg (((a0 - 1) * a1 + (a1 - 1)) - ((a2 - 1) * a3 + (a3 - 1)))]

/-- Marginal identity for laws with uniform marginals. -/
theorem B_marginal (ν : Law) (hm : UniformMarginals ν) (i : Site) (h : Site → ℝ) :
    ∑ π : Perm, ν π * h (π i) = (∑ j, h j) / 4 := by
  have step1 : ∀ π : Perm, ν π * h (π i) = ∑ j, if π i = j then ν π * h j else 0 := by
    intro π
    rw [Finset.sum_ite_eq]
    simp
  calc ∑ π : Perm, ν π * h (π i)
        = ∑ π : Perm, ∑ j, (if π i = j then ν π * h j else 0) :=
          Finset.sum_congr rfl (fun π _ => step1 π)
    _ = ∑ j, ∑ π : Perm, (if π i = j then ν π * h j else 0) := Finset.sum_comm
    _ = ∑ j, h j * ∑ π : Perm, (if π i = j then ν π else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun π _ => ?_)
        split_ifs <;> ring
    _ = ∑ j, h j * (1 / 4) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hm i j]
    _ = (∑ j, h j) / 4 := by rw [← Finset.sum_mul]; ring

/-- The fibre counts `#{π | π i = j}` do not depend on `j`. -/
theorem B_fiber_shift (i j : Site) :
    ∑ π : Perm, (if π i = j then (1 : ℝ) else 0) =
      ∑ π : Perm, (if π i = 0 then (1 : ℝ) else 0) := by
  rw [← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap (0 : Site) j))]
  refine Finset.sum_congr rfl (fun π _ => ?_)
  simp only [Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply]
  have hiff : (Equiv.swap (0 : Site) j) (π i) = j ↔ π i = 0 := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  exact if_congr hiff rfl rfl

/-- Each fibre `{π | π i = j}` has `6` elements. -/
theorem B_fiber_card (i j : Site) :
    ∑ π : Perm, (if π i = j then (1 : ℝ) else 0) = 6 := by
  have htot : ∑ j : Site, ∑ π : Perm, (if π i = j then (1 : ℝ) else 0) = 24 := by
    rw [Finset.sum_comm]
    have : ∀ π : Perm, ∑ j : Site, (if π i = j then (1 : ℝ) else 0) = 1 := by
      intro π
      rw [Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun π _ => this π)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Nat.factorial]
  rw [Fin.sum_univ_four, B_fiber_shift i 1, B_fiber_shift i 2, B_fiber_shift i 3] at htot
  rw [B_fiber_shift i j]
  linarith

/-- The uniform law is a probability law. -/
theorem B_uniform_isProb : IsProbability uniformLaw := by
  refine ⟨fun π => by unfold uniformLaw; norm_num, ?_⟩
  unfold uniformLaw
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Nat.factorial]

/-- The uniform law has uniform marginals. -/
theorem B_uniform_marginals : UniformMarginals uniformLaw := by
  intro i j
  have : ∀ π : Perm, (if π i = j then uniformLaw π else 0) =
      (1 / 24) * (if π i = j then (1 : ℝ) else 0) := by
    intro π
    unfold uniformLaw
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun π _ => this π), ← Finset.mul_sum, B_fiber_card]
  norm_num

/-- The affine part of the product has the same expectation under every law with uniform
marginals. -/
theorem B_linear_part (ν : Law) (hp : IsProbability ν) (hm : UniformMarginals ν)
    (f : Functions) :
    ∑ π : Perm, ν π * (1 + ∑ i, (f i (π i) - 1)) = 1 + ∑ i, (∑ j, (f i j - 1)) / 4 := by
  have : ∀ π : Perm, ν π * (1 + ∑ i, (f i (π i) - 1)) =
      ν π + ∑ i, ν π * (f i (π i) - 1) := by
    intro π
    rw [mul_add, mul_one, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun π _ => this π), Finset.sum_add_distrib, hp.2, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => B_marginal ν hm i (fun j => f i j - 1))

/-- Pointwise bound on the nonlinear remainder of the product. -/
theorem B_remainder_bound (f : Functions) (hf : ∀ i j, 0 ≤ f i j)
    (hn : ∀ i, rowSq (f i) = 4) (π : Perm) :
    |∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))| ≤ 3 * totalDist f := by
  have hle : ∀ i j, f i j ≤ 2 := fun i j => B_entry_le_two (f i) (hf i) (hn i) j
  have hrow : ∀ i, (f i (π i) - 1) ^ 2 ≤ rowDist (f i) := by
    intro i
    unfold rowDist
    exact Finset.single_le_sum (f := fun k => (f i k - 1) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ (π i))
  have key := B_prod_remainder (f 0 (π 0)) (f 1 (π 1)) (f 2 (π 2)) (f 3 (π 3))
    (hf _ _) (hf _ _) (hle _ _) (hle _ _)
  have hD : totalDist f = rowDist (f 0) + rowDist (f 1) + rowDist (f 2) + rowDist (f 3) := by
    unfold totalDist
    rw [Fin.sum_univ_four]
  rw [Fin.prod_univ_four, Fin.sum_univ_four, hD]
  calc _ ≤ _ := key
    _ ≤ _ := by linarith [hrow 0, hrow 1, hrow 2, hrow 3]

/-- Part B: perturbation estimate for laws with exactly uniform marginals. -/
theorem perturbation (ν : Law) (hp : IsProbability ν) (hm : UniformMarginals ν)
    (f : Functions) (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation ν f ≤
      permanentExpectation uniformLaw f + 6 * totalVariation ν * totalDist f := by
  have hsplit : ∀ μ : Law, permanentExpectation μ f =
      ∑ π : Perm, μ π * (1 + ∑ i, (f i (π i) - 1)) +
        ∑ π : Perm, μ π * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))) := by
    intro μ
    unfold permanentExpectation
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    ring
  have hLν := B_linear_part ν hp hm f
  have hLu := B_linear_part uniformLaw B_uniform_isProb B_uniform_marginals f
  have hdiff : ∑ π : Perm, ν π * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))) -
      ∑ π : Perm, uniformLaw π * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))) ≤
        6 * totalVariation ν * totalDist f := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ π : Perm, (ν π * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))) -
          uniformLaw π * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))))
          ≤ ∑ π : Perm, |ν π - 1 / 24| * (3 * totalDist f) := by
            refine Finset.sum_le_sum (fun π _ => ?_)
            have h1 : ν π * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))) -
                uniformLaw π * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))) =
                (ν π - 1 / 24) * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))) := by
              unfold uniformLaw
              ring
            rw [h1]
            calc (ν π - 1 / 24) * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1)))
                ≤ |(ν π - 1 / 24) * (∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1)))| :=
                  le_abs_self _
              _ = |ν π - 1 / 24| * |∏ i, f i (π i) - (1 + ∑ i, (f i (π i) - 1))| :=
                  abs_mul _ _
              _ ≤ |ν π - 1 / 24| * (3 * totalDist f) :=
                  mul_le_mul_of_nonneg_left (B_remainder_bound f hf hn π) (abs_nonneg _)
      _ = 6 * totalVariation ν * totalDist f := by
            rw [← Finset.sum_mul]
            unfold totalVariation
            ring
  rw [hsplit ν, hsplit uniformLaw, hLν, hLu]
  linarith

end OAI.FourRow.Sol

namespace OAI.FourRow.Sol

/-! ## Part C: passing from exponent 2 to `p ∈ [9/5, 2]` -/

/-- Scalar bound `x^p ≥ x² − (2 − p) x² (x − 1)` for `x ≥ 0`, `0 < p ≤ 2`. -/
theorem C_scalar (x p : ℝ) (hx : 0 ≤ x) (hp : 0 < p) (hp2 : p ≤ 2) :
    x ^ 2 - (2 - p) * (x ^ 2 * (x - 1)) ≤ x ^ p := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    rw [Real.zero_rpow hp.ne']
    simp
  · have hsplit : x ^ p = x ^ (2 : ℝ) * x ^ (-(2 - p)) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    have h2 : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_two x
    have hexp : 1 - (2 - p) * (x - 1) ≤ x ^ (-(2 - p)) := by
      rw [Real.rpow_def_of_pos hpos]
      have hlog := Real.log_le_sub_one_of_pos hpos
      have he := Real.add_one_le_exp (Real.log x * -(2 - p))
      have hq : 0 ≤ 2 - p := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hlog hq]
    rw [hsplit, h2]
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [mul_le_mul_of_nonneg_left hexp hx2]

/-- Each entry of a nonnegative row with `rowSq = 4` is at most `2`. -/
theorem C_entry_le_two (a : Site → ℝ) (hn : rowSq a = 4) (j : Site) : a j ≤ 2 := by
  have h1 : a j ^ 2 ≤ rowSq a := by
    unfold rowSq
    exact Finset.single_le_sum (f := fun k => a k ^ 2) (fun k _ => sq_nonneg (a k))
      (Finset.mem_univ j)
  nlinarith [h1]

/-- `rowDist` is nonnegative. -/
theorem C_rowDist_nonneg (a : Site → ℝ) : 0 ≤ rowDist a := by
  unfold rowDist
  exact Finset.sum_nonneg (fun j _ => sq_nonneg (a j - 1))

/-- For a nonnegative normalized row, `rowDist a ≤ 8`. -/
theorem C_rowDist_le_eight (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j) (hn : rowSq a = 4) :
    rowDist a ≤ 8 := by
  unfold rowDist
  unfold rowSq at hn
  rw [Fin.sum_univ_four] at hn ⊢
  nlinarith [ha 0, ha 1, ha 2, ha 3]

/-- The cubic sum bound: `∑ a_j^2 (a_j - 1) ≤ (5/2) rowDist a`. -/
theorem C_cubic_sum (a : Site → ℝ) (hn : rowSq a = 4) :
    ∑ j, a j ^ 2 * (a j - 1) ≤ 5 / 2 * rowDist a := by
  have hpt : ∀ j, a j ^ 2 * (a j - 1) ≤ 5 / 2 * (a j - 1) ^ 2 + (a j ^ 2 - 1) / 2 := by
    intro j
    have h2 := C_entry_le_two a hn j
    have : 0 ≤ (a j - 1) ^ 2 * (2 - a j) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [this]
  have hsum : ∑ j, a j ^ 2 * (a j - 1) ≤
      ∑ j, (5 / 2 * (a j - 1) ^ 2 + (a j ^ 2 - 1) / 2) :=
    Finset.sum_le_sum (fun j _ => hpt j)
  have hid : ∑ j, (5 / 2 * (a j - 1) ^ 2 + (a j ^ 2 - 1) / 2) =
      5 / 2 * rowDist a + (rowSq a - 4) / 2 := by
    unfold rowDist rowSq
    simp only [Fin.sum_univ_four]
    ring
  rw [hid, hn] at hsum
  linarith

/-- Lower bound for the normalized `p`-th power sum. -/
theorem C_powsum_lower (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 2) (a : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hn : rowSq a = 4) :
    1 - (5 * (2 - p) / 8) * rowDist a ≤ (∑ j, a j ^ p) / 4 := by
  have hpt : ∀ j, a j ^ 2 - (2 - p) * (a j ^ 2 * (a j - 1)) ≤ a j ^ p :=
    fun j => C_scalar (a j) p (ha j) hp hp2
  have hsum : ∑ j, (a j ^ 2 - (2 - p) * (a j ^ 2 * (a j - 1))) ≤ ∑ j, a j ^ p :=
    Finset.sum_le_sum (fun j _ => hpt j)
  have hid : ∑ j, (a j ^ 2 - (2 - p) * (a j ^ 2 * (a j - 1))) =
      rowSq a - (2 - p) * ∑ j, a j ^ 2 * (a j - 1) := by
    unfold rowSq
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hid, hn] at hsum
  have hc := C_cubic_sum a hn
  have hq : 0 ≤ 2 - p := by linarith
  have := mul_le_mul_of_nonneg_left hc hq
  nlinarith [this]

/-- `lpNorm` of a nonnegative row is nonnegative. -/
theorem C_lpNorm_nonneg (p : ℝ) (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j) : 0 ≤ lpNorm p a := by
  unfold lpNorm
  apply Real.rpow_nonneg
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (ha j) p)

/-- Row-wise lower bound for `lpNorm`. -/
theorem C_lpNorm_lower (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (a : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hn : rowSq a = 4) :
    1 - (5 * (2 - p) / 8) * rowDist a ≤ lpNorm p a := by
  set L := 1 - (5 * (2 - p) / 8) * rowDist a with hL
  have hp : 0 < p := by linarith
  have hS := C_powsum_lower p hp hp2 a ha hn
  rw [← hL] at hS
  rcases le_or_gt L 0 with hneg | hpos
  · exact le_trans hneg (C_lpNorm_nonneg p a ha)
  · have hL1 : L ≤ 1 := by
      have h0 := C_rowDist_nonneg a
      have : 0 ≤ (5 * (2 - p) / 8) * rowDist a :=
        mul_nonneg (by linarith) h0
      linarith
    have hinv : 1 / p ≤ 1 := by
      rw [div_le_one hp]; exact hp1
    have h1 : L ≤ L ^ (1 / p) := Real.self_le_rpow_of_le_one hpos.le hL1 hinv
    have h2 : L ^ (1 / p) ≤ ((∑ j, a j ^ p) / 4) ^ (1 / p) :=
      Real.rpow_le_rpow hpos.le hS (by positivity)
    unfold lpNorm
    exact le_trans h1 h2

/-- `1 - Σ e_i ≤ ∏ (1 - e_i)` for `e_i ∈ [0, 1]`, four factors. -/
theorem C_prod_ge (e : Site → ℝ) (h0 : ∀ i, 0 ≤ e i) (h1 : ∀ i, e i ≤ 1) :
    1 - ∑ i, e i ≤ ∏ i, (1 - e i) := by
  rw [Fin.sum_univ_four, Fin.prod_univ_four]
  have a0 := h0 0; have a1 := h0 1; have a2 := h0 2; have a3 := h0 3
  have b0 := h1 0; have b1 := h1 1; have b2 := h1 2; have b3 := h1 3
  have s1 : 1 - e 0 - e 1 ≤ (1 - e 0) * (1 - e 1) := by nlinarith [mul_nonneg a0 a1]
  have s2 : 1 - e 0 - e 1 - e 2 ≤ (1 - e 0) * (1 - e 1) * (1 - e 2) := by
    have hc : 0 ≤ 1 - e 2 := by linarith
    have := mul_le_mul_of_nonneg_right s1 hc
    nlinarith [this, mul_nonneg (add_nonneg a0 a1) a2]
  have s3 : 1 - e 0 - e 1 - e 2 - e 3 ≤ (1 - e 0) * (1 - e 1) * (1 - e 2) * (1 - e 3) := by
    have hc : 0 ≤ 1 - e 3 := by linarith
    have := mul_le_mul_of_nonneg_right s2 hc
    nlinarith [this, mul_nonneg (add_nonneg (add_nonneg a0 a1) a2) a3]
  linarith

theorem norm_lower (p : ℝ) (hp0 : 9 / 5 ≤ p) (hp2 : p ≤ 2) (f : Functions) (hf : ∀ i j, 0 ≤ f i j)
    (hn : ∀ i, rowSq (f i) = 4) :
    1 - (5 * (2 - p) / 8) * totalDist f ≤ ∏ i, lpNorm p (f i) := by
  set c := 5 * (2 - p) / 8 with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hc1 : c ≤ 1 / 8 := by rw [hc]; linarith
  have he0 : ∀ i, 0 ≤ c * rowDist (f i) := fun i => mul_nonneg hc0 (C_rowDist_nonneg _)
  have he1 : ∀ i, c * rowDist (f i) ≤ 1 := by
    intro i
    have h8 := C_rowDist_le_eight (f i) (hf i) (hn i)
    have hd := C_rowDist_nonneg (f i)
    nlinarith [mul_le_mul hc1 h8 hd (by norm_num : (0:ℝ) ≤ 1 / 8)]
  have hprod := C_prod_ge (fun i => c * rowDist (f i)) he0 he1
  have htot : c * totalDist f = ∑ i, c * rowDist (f i) := by
    unfold totalDist
    rw [Finset.mul_sum]
  rw [htot]
  refine le_trans hprod ?_
  apply Finset.prod_le_prod
  · intro i _
    linarith [he1 i]
  · intro i _
    exact C_lpNorm_lower p (by linarith) hp2 (f i) (hf i) (hn i)

end OAI.FourRow.Sol

namespace OAI.FourRow.Sol

/-! ## Part D: assembly and homogeneity -/


/-- The normalized `L^p` norm of a nonnegative row is nonnegative. -/
theorem D_lpNorm_nonneg (p : ℝ) (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j) : 0 ≤ lpNorm p a := by
  unfold lpNorm
  apply Real.rpow_nonneg
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (ha j) p)

/-- The product of the row norms of a nonnegative matrix is nonnegative. -/
theorem D_prod_lpNorm_nonneg (p : ℝ) (f : Functions) (hf : ∀ i j, 0 ≤ f i j) :
    0 ≤ ∏ i, lpNorm p (f i) :=
  Finset.prod_nonneg (fun i _ => D_lpNorm_nonneg p (f i) (hf i))

theorem D_rowDist_nonneg (a : Site → ℝ) : 0 ≤ rowDist a :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (a j - 1))

theorem D_totalDist_nonneg (f : Functions) : 0 ≤ totalDist f :=
  Finset.sum_nonneg (fun i _ => D_rowDist_nonneg (f i))

theorem D_rowSq_nonneg (a : Site → ℝ) : 0 ≤ rowSq a :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (a j))

theorem D_entry_sq_le_rowSq (a : Site → ℝ) (j : Site) : a j ^ 2 ≤ rowSq a := by
  unfold rowSq
  exact Finset.single_le_sum (f := fun k => a k ^ 2) (fun k _ => sq_nonneg (a k))
    (Finset.mem_univ j)

/-- A row with `rowSq = 0` vanishes identically. -/
theorem D_row_zero (a : Site → ℝ) (h : rowSq a = 0) (j : Site) : a j = 0 := by
  have h1 := D_entry_sq_le_rowSq a j
  rw [h] at h1
  have h2 : a j ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h2

/-- Normalized case (all rows with `rowSq = 4`), with `p₀ = 2 - 1/2000`, `ε = 1/25000`. -/
theorem D_normalized (ν : Law) (hp : IsProbability ν) (htv : totalVariation ν < 1 / 25000)
    (hm : UniformMarginals ν) (f : Functions) (hf : ∀ i j, 0 ≤ f i j)
    (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation ν f ≤ ∏ i, lpNorm (2 - 1 / 2000) (f i) := by
  have hA := uniform_stability f hf hn
  have hB := perturbation ν hp hm f hf hn
  have hC := norm_lower (2 - 1 / 2000) (by norm_num) (by norm_num) f hf hn
  have hD := D_totalDist_nonneg f
  have h1 : 0 ≤ (1 / 25000 - totalVariation ν) * totalDist f := mul_nonneg (by linarith) hD
  nlinarith

/-- Homogeneity of the normalized `L^p` norm. -/
theorem D_lpNorm_smul (p : ℝ) (hp : p ≠ 0) (c : ℝ) (hc : 0 ≤ c) (a : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) :
    lpNorm p (fun j => c * a j) = c * lpNorm p a := by
  unfold lpNorm
  have hS : 0 ≤ (∑ j, a j ^ p) / 4 :=
    div_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (ha j) p)) (by norm_num)
  have h1 : (∑ j, (c * a j) ^ p) / 4 = c ^ p * ((∑ j, a j ^ p) / 4) := by
    have h2 : ∀ j, (c * a j) ^ p = c ^ p * a j ^ p := fun j => Real.mul_rpow hc (ha j)
    simp_rw [h2]
    rw [← Finset.mul_sum]
    ring
  rw [h1, Real.mul_rpow (Real.rpow_nonneg hc p) hS, ← Real.rpow_mul hc, mul_one_div_cancel hp,
    Real.rpow_one]

/-- Scaling of the permanent expectation by row factors. -/
theorem D_permExp_scale (ν : Law) (c : Site → ℝ) (g : Functions) :
    permanentExpectation ν (fun i j => c i * g i j) = (∏ i, c i) * permanentExpectation ν g := by
  unfold permanentExpectation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun π _ => ?_)
  rw [Finset.prod_mul_distrib]
  ring

/-- The inequality for a matrix with rows `c i • g i`, `g` normalized. -/
theorem D_scaled (ν : Law) (hp : IsProbability ν) (htv : totalVariation ν < 1 / 25000)
    (hm : UniformMarginals ν) (c : Site → ℝ) (hc : ∀ i, 0 ≤ c i) (g : Functions)
    (hg : ∀ i j, 0 ≤ g i j) (hn : ∀ i, rowSq (g i) = 4) :
    permanentExpectation ν (fun i j => c i * g i j) ≤
      ∏ i, lpNorm (2 - 1 / 2000) (fun j => c i * g i j) := by
  have hnorm := D_normalized ν hp htv hm g hg hn
  have hprod : ∏ i, lpNorm (2 - 1 / 2000) (fun j => c i * g i j) =
      (∏ i, c i) * ∏ i, lpNorm (2 - 1 / 2000) (g i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact D_lpNorm_smul (2 - 1 / 2000) (by norm_num) (c i) (hc i) (g i) (hg i)
  rw [D_permExp_scale, hprod]
  exact mul_le_mul_of_nonneg_left hnorm (Finset.prod_nonneg (fun i _ => hc i))

/-- The general case: zero rows and homogeneity. -/
theorem D_general (ν : Law) (hp : IsProbability ν) (htv : totalVariation ν < 1 / 25000)
    (hm : UniformMarginals ν) (f : Functions) (hf : ∀ i j, 0 ≤ f i j) :
    permanentExpectation ν f ≤ ∏ i, lpNorm (2 - 1 / 2000) (f i) := by
  by_cases hz : ∃ i, rowSq (f i) = 0
  · obtain ⟨i, hi⟩ := hz
    have hzero : permanentExpectation ν f = 0 := by
      unfold permanentExpectation
      apply Finset.sum_eq_zero
      intro π _
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (D_row_zero (f i) hi (π i)), mul_zero]
    rw [hzero]
    exact D_prod_lpNorm_nonneg _ f hf
  · simp only [not_exists] at hz
    have hpos : ∀ i, 0 < rowSq (f i) := fun i =>
      lt_of_le_of_ne (D_rowSq_nonneg _) (Ne.symm (hz i))
    obtain ⟨c, hc⟩ : ∃ c : Site → ℝ, c = fun i => Real.sqrt (rowSq (f i) / 4) := ⟨_, rfl⟩
    have hcpos : ∀ i, 0 < c i := by
      intro i
      rw [hc]
      exact Real.sqrt_pos.mpr (by linarith [hpos i])
    have hcsq : ∀ i, c i ^ 2 = rowSq (f i) / 4 := by
      intro i
      rw [hc]
      exact Real.sq_sqrt (by linarith [hpos i])
    obtain ⟨g, hg⟩ : ∃ g : Functions, g = fun i j => f i j / c i := ⟨_, rfl⟩
    have hfg : f = fun i j => c i * g i j := by
      funext i j
      rw [hg]
      field_simp [(hcpos i).ne']
    have hg0 : ∀ i j, 0 ≤ g i j := by
      intro i j
      rw [hg]
      exact div_nonneg (hf i j) (hcpos i).le
    have hgn : ∀ i, rowSq (g i) = 4 := by
      intro i
      have hci : c i ≠ 0 := (hcpos i).ne'
      have h1 : rowSq (g i) = rowSq (f i) / c i ^ 2 := by
        unfold rowSq
        rw [hg, Finset.sum_div]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [div_pow]
      rw [h1, hcsq i]
      field_simp [(hpos i).ne']
    rw [hfg]
    exact D_scaled ν hp htv hm c (fun i => (hcpos i).le) g hg0 hgn

end OAI.FourRow.Sol

open OAI.FourRow OAI.FourRow.Sol

theorem solution :
  ∃ p₀ : ℝ, 4 / 3 < p₀ ∧ p₀ < 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Law,
      IsProbability ν → totalVariation ν < ε → UniformMarginals ν →
      ∀ f : Functions, (∀ i j, 0 ≤ f i j) →
        permanentExpectation ν f ≤ ∏ i, lpNorm p₀ (f i) := by
  refine ⟨2 - 1 / 2000, by norm_num, by norm_num, 1 / 25000, by norm_num, ?_⟩
  intro ν hp htv hm f hf
  exact D_general ν hp htv hm f hf

end
