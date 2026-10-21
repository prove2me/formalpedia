-- Prove2me | solution 1 for GivenDegreeSeq.FixedPoint.eq_6_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:44:40.08622+00:00
-- url     : https://prove2.me/submissions/00c4b732-fca9-4e52-bdae-6b1e82e699ef

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

set_option autoImplicit false
open GivenDegreeSeq.FixedPoint

lemma gdf_r_pos {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) : 0 < r x i j := by
  unfold r; positivity

lemma gdf_S_pos {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (i : Fin n) :
    0 < ∑ j ∈ Finset.univ.erase i, r x i j := by
  apply Finset.sum_pos (fun j _ => gdf_r_pos x i j)
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp
  omega

lemma gdf_edgeProb {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    edgeProb x i j = Real.exp (x i) * r x i j := by
  unfold edgeProb r
  have h1 : (0:ℝ) < Real.exp (x j) := Real.exp_pos _
  have h2 : Real.exp (x i + x j) = Real.exp (x i) * Real.exp (x j) := Real.exp_add _ _
  have h3 : Real.exp (-x j) * Real.exp (x j) = 1 := by rw [← Real.exp_add]; simp
  rw [h2]
  field_simp
  nlinarith [h3]

lemma gdf_ml_sum {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, edgeProb x i j =
      Real.exp (x i) * ∑ j ∈ Finset.univ.erase i, r x i j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => gdf_edgeProb x i j)

open ContinuousLinearMap in
lemma gdf_hasFDeriv {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    ∃ L : (Fin n → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun y => phi d y i) L x ∧
      ∀ v : Fin n → ℝ, L v = (∑ k ∈ Finset.univ.erase i, r x i k ^ 2 *
          (-Real.exp (-x k) * v k + Real.exp (x i) * v i)) / ∑ k ∈ Finset.univ.erase i, r x i k := by
  have hF : ∀ k ∈ Finset.univ.erase i, HasFDerivAt (fun y : Fin n → ℝ => r y i k)
      ((-(r x i k ^ 2)) • ((-Real.exp (-x k)) • (proj k : (Fin n → ℝ) →L[ℝ] ℝ)
        + Real.exp (x i) • (proj i : (Fin n → ℝ) →L[ℝ] ℝ))) x := by
    intro k _
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => Real.exp (-y k) + Real.exp (y i))
        ((-Real.exp (-x k)) • (proj k : (Fin n → ℝ) →L[ℝ] ℝ)
        + Real.exp (x i) • (proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
      have a : HasFDerivAt (fun y : Fin n → ℝ => Real.exp (-y k) + Real.exp (y i)) _ x :=
        ((hasFDerivAt_apply k x).neg.exp).add ((hasFDerivAt_apply i x).exp)
      refine a.congr_fderiv ?_
      ext v
      simp
    have h2 := (hasDerivAt_inv (x := Real.exp (-x k) + Real.exp (x i)) (by positivity)).comp_hasFDerivAt x h1
    have e : (fun y : Fin n → ℝ => r y i k) = (fun y => (Real.exp (-y k) + Real.exp (y i))⁻¹) := by
      funext y; unfold r; rw [one_div]
    rw [e]
    have h3 : HasFDerivAt (fun y : Fin n → ℝ => (Real.exp (-y k) + Real.exp (y i))⁻¹) _ x := h2
    refine h3.congr_fderiv ?_
    unfold r; rw [one_div]; simp
  have hS := HasFDerivAt.fun_sum hF
  have hS' : HasFDerivAt (fun y : Fin n → ℝ => ∑ k ∈ Finset.univ.erase i, r y i k) _ x :=
    hS
  have hL := (hS'.log (gdf_S_pos hn x i).ne').const_sub (Real.log (d i))
  refine ⟨_, hL, ?_⟩
  intro v
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  have e : ∑ k ∈ Finset.univ.erase i, -r x i k ^ 2 * (-Real.exp (-x k) * v k + Real.exp (x i) * v i)
      = -∑ k ∈ Finset.univ.erase i, r x i k ^ 2 * (-Real.exp (-x k) * v k + Real.exp (x i) * v i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [e]
  ring

lemma gdf_clm_apply {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ j, L (Pi.single j 1) * v j := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have : (fun k => if j = k then (1:ℝ) else 0) = Pi.single j 1 := by
    funext k; simp [Pi.single_apply, eq_comm]
  rw [this, map_smul, smul_eq_mul, mul_comm]

lemma gdf_fderiv_apply {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n)
    (v : Fin n → ℝ) :
    fderiv ℝ (fun y => phi d y i) x v = ∑ j, partialPhi d x i j * v j := by
  obtain ⟨L, hL, _⟩ := gdf_hasFDeriv hn d x i
  unfold partialPhi
  rw [hL.fderiv]
  exact gdf_clm_apply L v

lemma gdf_partial_off {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x : Fin n → ℝ) {i j : Fin n}
    (h : i ≠ j) :
    partialPhi d x i j = -(r x i j ^ 2 * Real.exp (-x j)) / ∑ k ∈ Finset.univ.erase i, r x i k := by
  obtain ⟨L, hL, hLv⟩ := gdf_hasFDeriv hn d x i
  unfold partialPhi
  rw [hL.fderiv, hLv]
  congr 1
  have hj : j ∈ Finset.univ.erase i := by simp [Ne.symm h]
  have : ∀ k, r x i k ^ 2 * (-Real.exp (-x k) * (Pi.single j (1:ℝ) : Fin n → ℝ) k +
      Real.exp (x i) * (Pi.single j (1:ℝ) : Fin n → ℝ) i) =
      if k = j then -(r x i j ^ 2 * Real.exp (-x j)) else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk; simp [Pi.single_apply, h]
    · simp [Pi.single_apply, hk, h]
  simp_rw [this]
  rw [Finset.sum_ite_eq' _ j]
  simp [hj]

lemma gdf_partial_diag {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    partialPhi d x i i = (∑ k ∈ Finset.univ.erase i, r x i k ^ 2 * Real.exp (x i)) /
      ∑ k ∈ Finset.univ.erase i, r x i k := by
  obtain ⟨L, hL, hLv⟩ := gdf_hasFDeriv hn d x i
  unfold partialPhi
  rw [hL.fderiv, hLv]
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hki : k ≠ i := Finset.ne_of_mem_erase hk
  simp [Pi.single_apply, hki]

lemma gdf_r_mul {n : ℕ} (x : Fin n → ℝ) (i k : Fin n) :
    r x i k * (Real.exp (-x k) + Real.exp (x i)) = 1 := by
  unfold r
  have : (0:ℝ) < Real.exp (-x k) + Real.exp (x i) := by positivity
  field_simp

lemma gdf_partial_off_neg {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x : Fin n → ℝ) {i j : Fin n}
    (h : i ≠ j) : partialPhi d x i j < 0 := by
  rw [gdf_partial_off hn d x h]
  have := gdf_r_pos x i j
  have := gdf_S_pos hn x i
  have : 0 < r x i j ^ 2 * Real.exp (-x j) := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos this) (by assumption)

lemma gdf_partial_diag_pos {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    0 < partialPhi d x i i := by
  rw [gdf_partial_diag hn d x i]
  apply div_pos _ (gdf_S_pos hn x i)
  apply Finset.sum_pos (fun k _ => by have := gdf_r_pos x i k; positivity)
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp
  omega

lemma gdf_row_sum {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    ∑ j, |partialPhi d x i j| = 1 := by
  have hS := gdf_S_pos hn x i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [abs_of_pos (gdf_partial_diag_pos hn d x i), gdf_partial_diag hn d x i]
  have : ∀ j ∈ Finset.univ.erase i, |partialPhi d x i j| =
      (r x i j ^ 2 * Real.exp (-x j)) / ∑ k ∈ Finset.univ.erase i, r x i k := by
    intro j hj
    have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [abs_of_neg (gdf_partial_off_neg hn d x hji), gdf_partial_off hn d x hji, neg_div, neg_neg]
  rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← add_div, div_eq_one_iff_eq hS.ne',
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h1 := gdf_r_mul x i k
  calc r x i k ^ 2 * Real.exp (x i) + r x i k ^ 2 * Real.exp (-x k)
      = r x i k * (r x i k * (Real.exp (-x k) + Real.exp (x i))) := by ring
    _ = r x i k := by rw [h1, mul_one]

lemma gdf_exp_bds {K t : ℝ} (h : |t| ≤ K) :
    Real.exp (-K) ≤ Real.exp t ∧ Real.exp t ≤ Real.exp K := by
  rw [abs_le] at h
  exact ⟨Real.exp_le_exp.2 h.1, Real.exp_le_exp.2 h.2⟩

/-- bounds on r given |x_i|, |x_k| ≤ K -/
lemma gdf_r_bds {n : ℕ} (x : Fin n → ℝ) (i k : Fin n) {K : ℝ} (hi : |x i| ≤ K) (hk : |x k| ≤ K) :
    Real.exp (-K) / 2 ≤ r x i k ∧ r x i k ≤ Real.exp K / 2 := by
  have hrF := gdf_r_mul x i k
  have hrp := gdf_r_pos x i k
  have hab : Real.exp K * Real.exp (-K) = 1 := by rw [← Real.exp_add]; simp
  have ha := Real.exp_pos K
  have hb := Real.exp_pos (-K)
  have e1 := gdf_exp_bds hi
  have e2 := gdf_exp_bds (K := K) (t := -x k) (by rw [abs_neg]; exact hk)
  have F1 : 2 * Real.exp (-K) ≤ Real.exp (-x k) + Real.exp (x i) := by linarith [e1.1, e2.1]
  have F2 : Real.exp (-x k) + Real.exp (x i) ≤ 2 * Real.exp K := by linarith [e1.2, e2.2]
  constructor
  · -- b/2 ≤ r : 1 = r F ≤ r 2a
    have : 1 ≤ r x i k * (2 * Real.exp K) := by
      calc (1:ℝ) = r x i k * (Real.exp (-x k) + Real.exp (x i)) := hrF.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left F2 hrp.le
    have h2 := mul_le_mul_of_nonneg_left this hb.le
    nlinarith
  · have : r x i k * (2 * Real.exp (-K)) ≤ 1 := by
      calc r x i k * (2 * Real.exp (-K)) ≤ r x i k * (Real.exp (-x k) + Real.exp (x i)) :=
            mul_le_mul_of_nonneg_left F1 hrp.le
        _ = 1 := hrF
    have h2 := mul_le_mul_of_nonneg_left this ha.le
    nlinarith

lemma gdf_r_sq_exp_le {n : ℕ} (x : Fin n → ℝ) (i k : Fin n) :
    r x i k ^ 2 * Real.exp (x i) ≤ r x i k ∧ r x i k ^ 2 * Real.exp (-x k) ≤ r x i k := by
  have hrF := gdf_r_mul x i k
  have hrp := gdf_r_pos x i k
  have e1 := Real.exp_pos (x i)
  have e2 := Real.exp_pos (-x k)
  constructor
  · calc r x i k ^ 2 * Real.exp (x i) ≤ r x i k ^ 2 * (Real.exp (-x k) + Real.exp (x i)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = r x i k * (r x i k * (Real.exp (-x k) + Real.exp (x i))) := by ring
      _ = r x i k := by rw [hrF, mul_one]
  · calc r x i k ^ 2 * Real.exp (-x k) ≤ r x i k ^ 2 * (Real.exp (-x k) + Real.exp (x i)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = r x i k * (r x i k * (Real.exp (-x k) + Real.exp (x i))) := by ring
      _ = r x i k := by rw [hrF, mul_one]

lemma gdf_S_bds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (i : Fin n) {K : ℝ} (hx : ‖x‖ ≤ K) :
    ((n:ℝ) - 1) * (Real.exp (-K) / 2) ≤ ∑ k ∈ Finset.univ.erase i, r x i k ∧
    ∑ k ∈ Finset.univ.erase i, r x i k ≤ ((n:ℝ) - 1) * (Real.exp K / 2) := by
  have hcard : ((Finset.univ.erase i).card : ℝ) = (n:ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
    rw [Nat.cast_sub (by omega)]; simp
  have hb : ∀ k, |x k| ≤ K := fun k => by
    have := norm_le_pi_norm x k
    rw [Real.norm_eq_abs] at this
    linarith
  constructor
  · calc ((n:ℝ) - 1) * (Real.exp (-K) / 2) = ∑ k ∈ Finset.univ.erase i, Real.exp (-K) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ _ := Finset.sum_le_sum (fun k _ => (gdf_r_bds x i k (hb i) (hb k)).1)
  · calc ∑ k ∈ Finset.univ.erase i, r x i k ≤ ∑ k ∈ Finset.univ.erase i, Real.exp K / 2 :=
          Finset.sum_le_sum (fun k _ => (gdf_r_bds x i k (hb i) (hb k)).2)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

lemma gdf_ab_off {a b N S m : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (hm : 0 < m)
    (hS : m * (b / 2) ≤ S) (hS' : S ≤ m * (a / 2)) (hN : N ≤ a / 2) (hN' : b ^ 3 / 4 ≤ N) :
    N / S ≤ a ^ 2 / m ∧ b ^ 4 / (2 * m) ≤ N / S := by
  have hSp : 0 < S := lt_of_lt_of_le (by positivity) hS
  constructor
  · rw [div_le_div_iff₀ hSp hm]
    have h1 : a ^ 2 * (m * (b / 2)) = m * (a / 2) := by
      have : a ^ 2 * b = a := by calc a ^ 2 * b = a * (a * b) := by ring
        _ = a := by rw [hab, mul_one]
      calc a ^ 2 * (m * (b / 2)) = m * (a ^ 2 * b) / 2 := by ring
        _ = m * (a / 2) := by rw [this]; ring
    nlinarith [mul_le_mul_of_nonneg_left hS (by positivity : (0:ℝ) ≤ a ^ 2), mul_le_mul_of_nonneg_right hN hm.le]
  · rw [div_le_div_iff₀ (by positivity) hSp]
    have h1 : b ^ 4 * (m * (a / 2)) = m * (b ^ 3 / 2) := by
      have : b ^ 4 * a = b ^ 3 := by calc b ^ 4 * a = b ^ 3 * (a * b) := by ring
        _ = b ^ 3 := by rw [hab, mul_one]
      calc b ^ 4 * (m * (a / 2)) = m * (b ^ 4 * a) / 2 := by ring
        _ = m * (b ^ 3 / 2) := by rw [this]; ring
    nlinarith [mul_le_mul_of_nonneg_left hS' (by positivity : (0:ℝ) ≤ b ^ 4), mul_le_mul_of_nonneg_right hN' hm.le]

theorem solution {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (K : ℝ) (x : Fin n → ℝ) (hx : ‖x‖ ≤ K) :
    (∀ i j : Fin n, i ≠ j →
        -Real.exp (2 * K) / ((n : ℝ) - 1) ≤ partialPhi d x i j ∧
        partialPhi d x i j ≤ -Real.exp (-4 * K) / (2 * ((n : ℝ) - 1))) ∧
    (∀ i : Fin n,
        Real.exp (-4 * K) / 2 ≤ partialPhi d x i i ∧
        partialPhi d x i i ≤ Real.exp (2 * K)) := by
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hm : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hK : 0 ≤ K := le_trans (norm_nonneg _) hx
  have hab : Real.exp K * Real.exp (-K) = 1 := by rw [← Real.exp_add]; simp
  have ha := Real.exp_pos K
  have hb := Real.exp_pos (-K)
  have e4 : Real.exp (-4 * K) = Real.exp (-K) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; try ring
  have e2 : Real.exp (2 * K) = Real.exp K ^ 2 := by
    rw [show (2:ℝ) * K = ((2:ℕ):ℝ) * K by norm_num, Real.exp_nat_mul]
  have hbd : ∀ k, |x k| ≤ K := fun k => by
    have := norm_le_pi_norm x k
    rw [Real.norm_eq_abs] at this
    linarith
  rw [e4, e2]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gdf_partial_off hn d x hij]
    obtain ⟨hS1, hS2⟩ := gdf_S_bds hn x i hx
    have hr := gdf_r_bds x i j (hbd i) (hbd j)
    have hexp := gdf_exp_bds (K := K) (t := -x j) (by rw [abs_neg]; exact hbd j)
    have hN1 : r x i j ^ 2 * Real.exp (-x j) ≤ Real.exp K / 2 :=
      (gdf_r_sq_exp_le x i j).2.trans hr.2
    have hN2 : Real.exp (-K) ^ 3 / 4 ≤ r x i j ^ 2 * Real.exp (-x j) := by
      have h1 : (Real.exp (-K) / 2) ^ 2 ≤ r x i j ^ 2 :=
        pow_le_pow_left₀ (by positivity) hr.1 2
      calc Real.exp (-K) ^ 3 / 4 = (Real.exp (-K) / 2) ^ 2 * Real.exp (-K) := by ring
        _ ≤ r x i j ^ 2 * Real.exp (-x j) :=
          mul_le_mul h1 hexp.1 hb.le (by positivity)
    obtain ⟨c1, c2⟩ := gdf_ab_off ha hb hab hm hS1 hS2 hN1 hN2
    constructor
    · rw [neg_div, neg_div, neg_le_neg_iff]; exact c1
    · rw [neg_div, neg_div, neg_le_neg_iff]; exact c2
  · rw [gdf_partial_diag hn d x i]
    obtain ⟨hS1, hS2⟩ := gdf_S_bds hn x i hx
    have hSp := gdf_S_pos hn x i
    have hr := fun k => gdf_r_bds x i k (hbd i) (hbd k)
    have hexp := gdf_exp_bds (K := K) (t := x i) (hbd i)
    have hcard : ((Finset.univ.erase i).card : ℝ) = (n:ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp
      rw [Nat.cast_sub (by omega)]; simp
    constructor
    · rw [le_div_iff₀ hSp]
      have hT : ((n:ℝ) - 1) * (Real.exp (-K) ^ 3 / 4) ≤
          ∑ k ∈ Finset.univ.erase i, r x i k ^ 2 * Real.exp (x i) := by
        calc ((n:ℝ) - 1) * (Real.exp (-K) ^ 3 / 4)
            = ∑ k ∈ Finset.univ.erase i, Real.exp (-K) ^ 3 / 4 := by
              rw [Finset.sum_const, nsmul_eq_mul, hcard]
          _ ≤ _ := Finset.sum_le_sum (fun k _ => by
              have h1 : (Real.exp (-K) / 2) ^ 2 ≤ r x i k ^ 2 :=
                pow_le_pow_left₀ (by positivity) (hr k).1 2
              calc Real.exp (-K) ^ 3 / 4 = (Real.exp (-K) / 2) ^ 2 * Real.exp (-K) := by ring
                _ ≤ r x i k ^ 2 * Real.exp (x i) :=
                  mul_le_mul h1 hexp.1 hb.le (by positivity))
      have h1 : Real.exp (-K) ^ 4 / 2 * (((n:ℝ) - 1) * (Real.exp K / 2)) =
          ((n:ℝ) - 1) * (Real.exp (-K) ^ 3 / 4) := by
        have : Real.exp (-K) ^ 4 * Real.exp K = Real.exp (-K) ^ 3 := by
          calc Real.exp (-K) ^ 4 * Real.exp K = Real.exp (-K) ^ 3 * (Real.exp K * Real.exp (-K)) := by ring
            _ = _ := by rw [hab, mul_one]
        calc _ = ((n:ℝ) - 1) * (Real.exp (-K) ^ 4 * Real.exp K) / 4 := by ring
          _ = _ := by rw [this]; ring
      calc Real.exp (-K) ^ 4 / 2 * ∑ k ∈ Finset.univ.erase i, r x i k
          ≤ Real.exp (-K) ^ 4 / 2 * (((n:ℝ) - 1) * (Real.exp K / 2)) :=
            mul_le_mul_of_nonneg_left hS2 (by positivity)
        _ = _ := h1
        _ ≤ _ := hT
    · have hT : ∑ k ∈ Finset.univ.erase i, r x i k ^ 2 * Real.exp (x i) ≤
          ∑ k ∈ Finset.univ.erase i, r x i k :=
        Finset.sum_le_sum (fun k _ => (gdf_r_sq_exp_le x i k).1)
      have h1 : (1:ℝ) ≤ Real.exp K := Real.one_le_exp hK
      calc _ ≤ (∑ k ∈ Finset.univ.erase i, r x i k) / ∑ k ∈ Finset.univ.erase i, r x i k :=
            div_le_div_of_nonneg_right hT hSp.le
        _ = 1 := div_self hSp.ne'
        _ ≤ Real.exp K ^ 2 := by nlinarith
