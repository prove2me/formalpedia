-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:28:26.116608+00:00
-- url     : https://prove2.me/submissions/235042ce-d16d-422c-8cfd-34665f4d2f6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MixedCloning_Optimal_Schur
import Theorems.Thm_MixedCloning_Optimal_wss_first_row
import Theorems.Thm_MixedCloning_Optimal_wss_normalization

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

open MixedCloning.Optimal

/-- `∏ (1 - u_i) ≤ 1 / (1 + Σ u_i)` for `u_i ∈ [0,1]` (the first two links of the chain in the
proof of Lemma 17), stated multiplied out. -/
theorem l17_prod_mul_le {ι : Type} (s : Finset ι) (u : ι → ℝ)
    (h0 : ∀ i, 0 ≤ u i) (h1 : ∀ i, u i ≤ 1) :
    (∏ i ∈ s, (1 - u i)) * (1 + ∑ i ∈ s, u i) ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hP : 0 ≤ ∏ i ∈ s, (1 - u i) := Finset.prod_nonneg (fun i _ => by linarith [h1 i])
    have hS : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg (fun i _ => h0 i)
    have hu0 := h0 a
    have hu1 := h1 a
    have key : (1 - u a) * (1 + (u a + ∑ i ∈ s, u i)) ≤ 1 + ∑ i ∈ s, u i := by nlinarith
    calc (1 - u a) * (∏ i ∈ s, (1 - u i)) * (1 + (u a + ∑ i ∈ s, u i))
        = (∏ i ∈ s, (1 - u i)) * ((1 - u a) * (1 + (u a + ∑ i ∈ s, u i))) := by ring
      _ ≤ (∏ i ∈ s, (1 - u i)) * (1 + ∑ i ∈ s, u i) := mul_le_mul_of_nonneg_left key hP
      _ ≤ 1 := ih

/-- `1/(1 + m/B) = 1 - m/(B+m)` for `B > 0`, `m ≥ 0`. -/
theorem l17_one_div_eq (B m : ℝ) (hB : 0 < B) (hm : 0 ≤ m) :
    1 / (1 + m / B) = 1 - m * (B + m)⁻¹ := by
  have h1 : B + m ≠ 0 := by linarith
  rw [one_add_div hB.ne', one_div_div, ← div_eq_mul_inv, one_sub_div h1]
  congr 1
  ring

/-- Product bound of Lemma 17: with `u_j = (d-r)/(d+λ₁+j)`,
`∏_{j<k} (r+λ₁+j)/(d+λ₁+j) = ∏ (1-u_j) ≤ 1/(1+Σ u_j) ≤ 1/(1+k·min u_j)
  = 1 - k(d-r)/(d+λ₁+k-1+k(d-r))`. -/
theorem l17_extra_le (d r k : ℕ) (hrd : r ≤ d) (hk : 1 ≤ k) (hd : 1 ≤ d) (L : YoungDiagram) :
    extraProduct d r k L ≤
      1 - (k : ℝ) * ((d : ℝ) - r) * ((d : ℝ) + k - 1 + k * ((d : ℝ) - r) + L.rowLen 0)⁻¹ := by
  have ha : (0 : ℝ) ≤ (L.rowLen 0 : ℝ) := Nat.cast_nonneg _
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hrdR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hden : ∀ j : Fin k, (0 : ℝ) < (d : ℝ) + L.rowLen 0 + j.val := fun j => by
    have : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    linarith
  let u : Fin k → ℝ := fun j => ((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + j.val)
  have hu0 : ∀ j, 0 ≤ u j := fun j => div_nonneg (by linarith) (hden j).le
  have hu1 : ∀ j, u j ≤ 1 := fun j => by
    show ((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + j.val) ≤ 1
    rw [div_le_one (hden j)]
    have : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    linarith
  have heq : extraProduct d r k L = ∏ j : Fin k, (1 - u j) := by
    unfold extraProduct
    apply Finset.prod_congr rfl
    intro j _
    have h := (hden j).ne'
    show ((r : ℝ) + L.rowLen 0 + j.val) / ((d : ℝ) + L.rowLen 0 + j.val) =
      1 - ((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + j.val)
    rw [one_sub_div h]
    congr 1
    ring
  have hB : (0 : ℝ) < (d : ℝ) + L.rowLen 0 + (k - 1) := by linarith
  have hmin : ∀ j : Fin k, ((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + (k - 1)) ≤ u j := by
    intro j
    have hj : (j.val : ℝ) + 1 ≤ k := by exact_mod_cast j.isLt
    show ((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + (k - 1)) ≤
      ((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + j.val)
    exact div_le_div_of_nonneg_left (by linarith) (hden j) (by linarith)
  have hsum : (k : ℝ) * (((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + (k - 1))) ≤
      ∑ j : Fin k, u j := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hmin j)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hprod := l17_prod_mul_le (Finset.univ : Finset (Fin k)) u hu0 hu1
  have hS0 : 0 ≤ ∑ j : Fin k, u j := Finset.sum_nonneg (fun j _ => hu0 j)
  have hm0 : 0 ≤ (k : ℝ) * (((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + (k - 1))) :=
    mul_nonneg (by linarith) (div_nonneg (by linarith) hB.le)
  rw [heq]
  calc ∏ j : Fin k, (1 - u j) ≤ 1 / (1 + ∑ j : Fin k, u j) := by
        rw [le_div_iff₀ (by linarith)]; exact hprod
    _ ≤ 1 / (1 + (k : ℝ) * (((d : ℝ) - r) / ((d : ℝ) + L.rowLen 0 + (k - 1)))) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
    _ = 1 - (k : ℝ) * ((d : ℝ) - r) *
          ((d : ℝ) + k - 1 + k * ((d : ℝ) - r) + L.rowLen 0)⁻¹ := by
        have hm : (0 : ℝ) ≤ (k : ℝ) * ((d : ℝ) - r) :=
          mul_nonneg (by linarith) (by linarith)
        rw [mul_div_assoc', l17_one_div_eq _ _ hB hm,
          show (d : ℝ) + L.rowLen 0 + (k - 1) + k * ((d : ℝ) - r) =
            (d : ℝ) + k - 1 + k * ((d : ℝ) - r) + L.rowLen 0 by ring]

theorem solution (d r n k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : 2*r ≤ d)
    (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) (heps16 : eps ≤ 1/16)
    (h : 1-eps ≤ wssExpectation n r (extraProduct d r k)) :
    (k : ℝ)*r*d/(8*eps) ≤ n := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrdR : 2 * (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hrpos : (0 : ℝ) < r := by linarith
  -- the weak Schur sampling weights form a probability distribution
  obtain ⟨w, hw_def⟩ : ∃ w : YoungDiagram → ℝ,
      w = fun L => (spechtDim L : ℝ) * schurCount L r / (r : ℝ)^n := ⟨_, rfl⟩
  have hrn : (0 : ℝ) < (r : ℝ)^n := pow_pos hrpos n
  have hw0 : ∀ L, 0 ≤ w L := fun L => by
    rw [hw_def]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hrn.le
  have hw1 : ∑ L ∈ partitions n r, w L = 1 := by
    simp only [hw_def]
    rw [← Finset.sum_div, wss_normalization n r, div_self hrn.ne']
  have hE : ∀ f : YoungDiagram → ℝ,
      wssExpectation n r f = ∑ L ∈ partitions n r, w L * f L := by
    intro f
    rw [hw_def]
    rfl
  -- constants `c = k(d-r)` and `A = d+k-1+k(d-r)`
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (k : ℝ) * ((d : ℝ) - r) := ⟨_, rfl⟩
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = (d : ℝ) + k - 1 + k * ((d : ℝ) - r) := ⟨_, rfl⟩
  have hkdr : (0 : ℝ) < (k : ℝ) * ((d : ℝ) - r) := mul_pos (by linarith) (by linarith)
  have hc : 0 < c := by rw [hc_def]; exact hkdr
  have hA : 0 < A := by rw [hA_def]; linarith
  obtain ⟨X, hX_def⟩ : ∃ X : YoungDiagram → ℝ, X = fun L => ((L.rowLen 0 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hX0 : ∀ L, 0 ≤ X L := fun L => by rw [hX_def]; exact Nat.cast_nonneg _
  -- Step 1: average the pointwise product bound
  have h1 : c * ∑ L ∈ partitions n r, w L * (A + X L)⁻¹ ≤ eps := by
    have hle : wssExpectation n r (extraProduct d r k) ≤
        1 - c * ∑ L ∈ partitions n r, w L * (A + X L)⁻¹ := by
      rw [hE]
      calc ∑ L ∈ partitions n r, w L * extraProduct d r k L
          ≤ ∑ L ∈ partitions n r, w L * (1 - c * (A + X L)⁻¹) := by
            apply Finset.sum_le_sum
            intro L _
            apply mul_le_mul_of_nonneg_left _ (hw0 L)
            rw [hc_def, hA_def, hX_def]
            exact l17_extra_le d r k (by omega) hk (by omega) L
        _ = (∑ L ∈ partitions n r, w L) - c * ∑ L ∈ partitions n r, w L * (A + X L)⁻¹ := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro L _
            ring
        _ = 1 - c * ∑ L ∈ partitions n r, w L * (A + X L)⁻¹ := by rw [hw1]
    linarith
  -- Step 2: Jensen for the convex function `x ↦ x⁻¹` on `(0, ∞)`
  have hJ : (A + wssExpectation n r X)⁻¹ ≤ ∑ L ∈ partitions n r, w L * (A + X L)⁻¹ := by
    have hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => x⁻¹) := by
      have h0 : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun x : ℝ => x ^ (-1 : ℤ) := convexOn_zpow (-1)
      simpa only [_root_.zpow_neg_one] using h0
    have hJ' := hconv.map_sum_le (t := partitions n r) (w := w) (p := fun L => A + X L)
      (fun L _ => hw0 L) hw1 (fun L _ => by
        show (0 : ℝ) < A + X L
        linarith [hX0 L])
    simp only [smul_eq_mul] at hJ'
    have hsum : ∑ L ∈ partitions n r, w L * (A + X L) = A + wssExpectation n r X := by
      rw [hE]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hw1, one_mul]
    rw [hsum] at hJ'
    exact hJ'
  -- Step 3: first-row bound [OW17, Thm. 5.2] (imported) and AM-GM
  have hF : wssExpectation n r X ≤ (n : ℝ)/r + 2 * Real.sqrt n := by
    rw [hX_def]
    exact wss_first_row n r hr
  have hAMGM : 2 * Real.sqrt n ≤ (n : ℝ)/r + r := by
    have hs := Real.sq_sqrt hnR
    rw [div_add' _ _ _ hrpos.ne', le_div_iff₀ hrpos]
    nlinarith [sq_nonneg (Real.sqrt n - r)]
  have hEX0 : 0 ≤ wssExpectation n r X := by
    rw [hE]
    exact Finset.sum_nonneg (fun L _ => mul_nonneg (hw0 L) (hX0 L))
  have hEXle : wssExpectation n r X ≤ 2 * (n : ℝ)/r + r := by
    have : 2 * (n : ℝ)/r = (n : ℝ)/r + (n : ℝ)/r := by ring
    linarith
  -- combine: `c/(A + 2n/r + r) ≤ c/(A + E[λ₁]) ≤ ε`, i.e. `c ≤ ε(A + 2n/r + r)`
  have hAE : 0 < A + wssExpectation n r X := by linarith
  have h2 : c * (A + wssExpectation n r X)⁻¹ ≤ eps := by
    have := mul_le_mul_of_nonneg_left hJ hc.le
    linarith
  have h3 : c ≤ eps * (A + wssExpectation n r X) := by
    rw [← div_le_iff₀ hAE]
    simpa [div_eq_mul_inv] using h2
  have h4 : c ≤ eps * (A + (2 * (n : ℝ)/r + r)) :=
    h3.trans (mul_le_mul_of_nonneg_left (by linarith) heps.le)
  -- Step 4: rearrange to `n ≥ ½(kr(d-r)/ε - r(A + r))`, then use `2r ≤ d` and `ε ≤ 1/16`
  have h5 : (k : ℝ) * r * ((d : ℝ) - r) ≤ eps * (r * (A + r) + 2 * n) := by
    have := mul_le_mul_of_nonneg_left h4 hrpos.le
    have e : (r : ℝ) * (eps * (A + (2 * (n : ℝ)/r + r))) =
        eps * (r * (A + r)) + 2 * eps * (r * ((n : ℝ) / r)) := by ring
    rw [e, mul_div_cancel₀ _ hrpos.ne', hc_def] at this
    linarith
  have hkrd : (0 : ℝ) ≤ (k : ℝ) * r * d := by positivity
  have hA2 : A + r ≤ 2 * k * d := by
    rw [hA_def]
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k - 1) (by linarith : (0 : ℝ) ≤ d + r - 1)]
  have h6 : (r : ℝ) * (A + r) ≤ 4 * ((k : ℝ) * r * d) := by
    linarith [mul_le_mul_of_nonneg_left hA2 hrpos.le]
  have h7 : (k : ℝ) * r * d / 2 ≤ (k : ℝ) * r * ((d : ℝ) - r) := by
    linarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ k) hrpos.le)
      (by linarith : (0 : ℝ) ≤ d - 2 * r)]
  have h8 : eps * ((r : ℝ) * (A + r)) ≤ (k : ℝ) * r * d / 4 := by
    linarith [mul_le_mul_of_nonneg_left h6 heps.le, mul_le_mul_of_nonneg_right heps16 hkrd]
  rw [div_le_iff₀ (by linarith)]
  linarith
