-- Prove2me | solution 1 for GivenDegreeSeq.FixedPoint.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:49:01.506142+00:00
-- url     : https://prove2.me/submissions/4ec40415-6c82-4a0f-9d1b-1cf38dbc0472

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

lemma gdf_r_cont {n : ℕ} (i k : Fin n) : Continuous (fun z : Fin n → ℝ => r z i k) := by
  unfold r
  exact continuous_const.div (by fun_prop) (fun z => by positivity)

lemma gdf_S_cont {n : ℕ} (i : Fin n) :
    Continuous (fun z : Fin n → ℝ => ∑ k ∈ Finset.univ.erase i, r z i k) :=
  continuous_finset_sum _ (fun k _ => gdf_r_cont i k)

lemma gdf_partial_cont {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (i j : Fin n) :
    Continuous (fun z : Fin n → ℝ => partialPhi d z i j) := by
  by_cases h : i = j
  · subst h
    have : (fun z : Fin n → ℝ => partialPhi d z i i) = fun z =>
        (∑ k ∈ Finset.univ.erase i, r z i k ^ 2 * Real.exp (z i)) /
          ∑ k ∈ Finset.univ.erase i, r z i k := funext (fun z => gdf_partial_diag hn d z i)
    rw [this]
    refine Continuous.div ?_ (gdf_S_cont i) (fun z => (gdf_S_pos hn z i).ne')
    exact continuous_finset_sum _ (fun k _ => (gdf_r_cont i k).pow 2 |>.mul (by fun_prop))
  · have : (fun z : Fin n → ℝ => partialPhi d z i j) = fun z =>
        -(r z i j ^ 2 * Real.exp (-z j)) /
          ∑ k ∈ Finset.univ.erase i, r z i k := funext (fun z => gdf_partial_off hn d z h)
    rw [this]
    refine Continuous.div ?_ (gdf_S_cont i) (fun z => (gdf_S_pos hn z i).ne')
    exact ((gdf_r_cont i j).pow 2 |>.mul (by fun_prop)).neg

lemma gdf_ftc {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    phi d x i - phi d y i = ∑ j, (∫ t in (0:ℝ)..1, partialPhi d (t • x + (1 - t) • y) i j) * (x - y) j := by
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • x + (1 - t) • y) (x - y) t := by
    intro t
    have a := ((hasDerivAt_id t).smul_const x).add (((hasDerivAt_id t).const_sub 1).smul_const y)
    refine a.congr_deriv ?_
    simp [sub_eq_add_neg]
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => phi d (t • x + (1 - t) • y) i)
      (∑ j, partialPhi d (t • x + (1 - t) • y) i j * (x - y) j) t := by
    intro t _
    obtain ⟨L, hL, _⟩ := gdf_hasFDeriv hn d (t • x + (1 - t) • y) i
    have := hL.comp_hasDerivAt t (hγ t)
    refine this.congr_deriv ?_
    have h2 := gdf_fderiv_apply hn d (t • x + (1 - t) • y) i (x - y)
    rw [hL.fderiv] at h2
    exact h2
  have hc : ∀ j : Fin n, Continuous (fun t : ℝ => partialPhi d (t • x + (1 - t) • y) i j) := by
    intro j
    exact (gdf_partial_cont hn d i j).comp (by fun_prop)
  have hint : IntervalIntegrable (fun t : ℝ => ∑ j, partialPhi d (t • x + (1 - t) • y) i j * (x - y) j)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_finset_sum _ (fun j _ => (hc j).mul continuous_const)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [one_smul, zero_smul, sub_zero, zero_add, sub_self, add_zero] at this
  rw [← this, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [intervalIntegral.integral_mul_const]
  · intro j _
    exact ((hc j).mul continuous_const).intervalIntegrable _ _

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

lemma gdf_split {n : ℕ} (f : Fin n → ℝ) (i k : Fin n) (h : k ≠ i) :
    ∑ j, f j = f i + f k + ∑ j ∈ (Finset.univ.erase i).erase k, f j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ k⟩)]
  ring

lemma gdf_L21 {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA1 : ∀ i, ∑ j, |A i j| ≤ 1) (hAd : ∀ i, δ ≤ A i i)
    (hAo : ∀ i j, i ≠ j → A i j ≤ -δ / ((n : ℝ) - 1))
    (hB1 : ∀ i, ∑ j, |B i j| ≤ 1) (hBd : ∀ i, δ ≤ B i i)
    (hBo : ∀ i j, i ≠ j → B i j ≤ -δ / ((n : ℝ) - 1)) (i : Fin n) :
    ∑ k, |(A * B) i k| ≤ 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  set ε : ℝ := δ / ((n:ℝ) - 1) with hε
  have hεpos : 0 < ε := div_pos hδ hn1
  have hεδ : ((n:ℝ) - 2) * ε ≤ δ := by
    have : ((n:ℝ) - 2) * ε = ((n:ℝ) - 2) / ((n:ℝ) - 1) * δ := by rw [hε]; ring
    rw [this]
    have : ((n:ℝ) - 2) / ((n:ℝ) - 1) ≤ 1 := by
      rw [div_le_one hn1]; linarith
    nlinarith
  have hAo' : ∀ i j, i ≠ j → A i j ≤ -ε := fun i j h => by
    have := hAo i j h; rw [hε]; rw [neg_div] at this; exact this
  have hBo' : ∀ i j, i ≠ j → B i j ≤ -ε := fun i j h => by
    have := hBo i j h; rw [hε]; rw [neg_div] at this; exact this
  have hcard : ((Finset.univ.erase i).card : ℝ) = (n:ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
    rw [Nat.cast_sub (by omega)]; simp
  have key : ∀ k, k ≠ i → |(A * B) i k| ≤ ∑ j, |A i j| * |B j k| - 2 * (((n:ℝ) - 2) * ε ^ 2) := by
    intro k hk
    have hcc : ((((Finset.univ.erase i).erase k).card : ℕ) : ℝ) = (n:ℝ) - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp; ring
    have e1 : (A * B) i k = ∑ j, A i j * B j k := rfl
    rw [e1, gdf_split (fun j => A i j * B j k) i k hk,
      gdf_split (fun j => |A i j| * |B j k|) i k hk]
    have rest : ∀ j ∈ (Finset.univ.erase i).erase k, ε ^ 2 ≤ A i j * B j k := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hj).2).1
      have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
      have a := hAo' i j (Ne.symm hji)
      have b := hBo' j k hjk
      nlinarith
    have restabs : ∑ j ∈ (Finset.univ.erase i).erase k, |A i j| * |B j k| =
        ∑ j ∈ (Finset.univ.erase i).erase k, A i j * B j k := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← abs_mul, abs_of_nonneg]
      exact le_trans (by positivity) (rest j hj)
    have hP : ((n:ℝ) - 2) * ε ^ 2 ≤ ∑ j ∈ (Finset.univ.erase i).erase k, A i j * B j k := by
      calc ((n:ℝ) - 2) * ε ^ 2 = ∑ j ∈ (Finset.univ.erase i).erase k, ε ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, hcc]
        _ ≤ _ := Finset.sum_le_sum rest
    rw [restabs]
    have ti : A i i * B i k ≤ -(δ * ε) := by
      have a := hAd i
      have b := hBo' i k (Ne.symm hk)
      nlinarith
    have tk : A i k * B k k ≤ -(δ * ε) := by
      have a := hAo' i k (Ne.symm hk)
      have b := hBd k
      nlinarith
    have hm : ((n:ℝ) - 2) * ε ^ 2 ≤ δ * ε := by nlinarith
    have hde : 0 < δ * ε := mul_pos hδ hεpos
    rw [← abs_mul, ← abs_mul, abs_of_nonpos (by linarith : A i i * B i k ≤ 0),
      abs_of_nonpos (by linarith : A i k * B k k ≤ 0), abs_le]
    constructor <;> linarith
  set m' : ℝ := ((n:ℝ) - 2) * ε ^ 2 with hm'
  have hii : |(A * B) i i| ≤ ∑ j, |A i j| * |B j i| := by
    have e1 : (A * B) i i = ∑ j, A i j * B j i := rfl
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact le_of_eq (Finset.sum_congr rfl (fun j _ => abs_mul _ _))
  set W : Fin n → ℝ := fun k => ∑ j, |A i j| * |B j k| with hW
  have hWsum : ∑ k, W k ≤ 1 := by
    have : ∑ k, W k = ∑ j, |A i j| * ∑ k, |B j k| := by
      simp only [hW]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    rw [this]
    calc ∑ j, |A i j| * ∑ k, |B j k| ≤ ∑ j, |A i j| * 1 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hB1 j) (abs_nonneg _))
      _ ≤ 1 := by simpa using hA1 i
  have h1 : ∑ k, |(A * B) i k| ≤ ∑ k, W k - ((n:ℝ) - 1) * (2 * m') := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have h2 : ∑ k ∈ Finset.univ.erase i, |(A * B) i k| ≤
        ∑ k ∈ Finset.univ.erase i, (W k - 2 * m') :=
      Finset.sum_le_sum (fun k hk => key k (Finset.ne_of_mem_erase hk))
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard] at h2
    have h3 : |(A * B) i i| ≤ W i := hii
    linarith
  have h4 : ((n:ℝ) - 1) * (2 * m') = 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) := by
    rw [hm', hε]
    field_simp
  linarith

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

theorem gdf_eq67 {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
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

lemma gdf_gamma_norm {n : ℕ} {x y : Fin n → ℝ} {K : ℝ} (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖t • x + (1 - t) • y‖ ≤ K := by
  calc ‖t • x + (1 - t) • y‖ ≤ ‖t • x‖ + ‖(1 - t) • y‖ := norm_add_le _ _
    _ = t * ‖x‖ + (1 - t) * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1,
          abs_of_nonneg (by linarith [ht.2])]
    _ ≤ t * K + (1 - t) * K := by
        gcongr
        · exact ht.1
        · linarith [ht.2]
    _ = K := by ring

lemma gdf_J_row {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    ∑ j, |J d x y i j| ≤ 1 := by
  have hc : ∀ j : Fin n, Continuous (fun t : ℝ => partialPhi d (t • x + (1 - t) • y) i j) :=
    fun j => (gdf_partial_cont hn d i j).comp (by fun_prop)
  calc ∑ j, |J d x y i j| ≤ ∑ j, ∫ t in (0:ℝ)..1, |partialPhi d (t • x + (1 - t) • y) i j| :=
        Finset.sum_le_sum (fun j _ => intervalIntegral.abs_integral_le_integral_abs zero_le_one)
    _ = ∫ t in (0:ℝ)..1, ∑ j, |partialPhi d (t • x + (1 - t) • y) i j| := by
        rw [intervalIntegral.integral_finset_sum]
        intro j _
        exact (continuous_abs.comp (hc j)).intervalIntegrable _ _
    _ = 1 := by
        simp_rw [gdf_row_sum hn d]
        simp

lemma gdf_J_bds {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) {x y : Fin n → ℝ}
    {K : ℝ} (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) :
    (∀ i j, i ≠ j → J d x y i j ≤ -(Real.exp (-4 * K) / 2) / ((n:ℝ) - 1)) ∧
    (∀ i, Real.exp (-4 * K) / 2 ≤ J d x y i i) := by
  have hc : ∀ i j : Fin n, Continuous (fun t : ℝ => partialPhi d (t • x + (1 - t) • y) i j) :=
    fun i j => (gdf_partial_cont hn d i j).comp (by fun_prop)
  constructor
  · intro i j hij
    have : ∫ t in (0:ℝ)..1, partialPhi d (t • x + (1 - t) • y) i j ≤
        ∫ t in (0:ℝ)..1, (-(Real.exp (-4 * K) / 2) / ((n:ℝ) - 1)) := by
      apply intervalIntegral.integral_mono_on zero_le_one ((hc i j).intervalIntegrable _ _)
        intervalIntegrable_const
      intro t ht
      have := ((gdf_eq67 hn d hd K (t • x + (1 - t) • y) (gdf_gamma_norm hx hy ht)).1 i j hij).2
      have e : -Real.exp (-4 * K) / (2 * ((n : ℝ) - 1)) =
          -(Real.exp (-4 * K) / 2) / ((n:ℝ) - 1) := by
        have : ((n:ℝ) - 1) ≠ 0 := by
          have : (2:ℝ) ≤ n := by exact_mod_cast hn
          linarith
        field_simp
      linarith
    simpa [J] using this
  · intro i
    have : ∫ t in (0:ℝ)..1, (Real.exp (-4 * K) / 2) ≤
        ∫ t in (0:ℝ)..1, partialPhi d (t • x + (1 - t) • y) i i := by
      apply intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
        ((hc i i).intervalIntegrable _ _)
      intro t ht
      exact ((gdf_eq67 hn d hd K (t • x + (1 - t) • y) (gdf_gamma_norm hx hy ht)).2 i).1
    simpa [J] using this

lemma gdf_mulVec_norm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hM : ∀ i, ∑ j, |M i j| ≤ c) (v : Fin n → ℝ) : ‖M.mulVec v‖ ≤ c * ‖v‖ := by
  have hv := norm_nonneg v
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
  calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖v‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul]
        have := norm_le_pi_norm v j
        rw [Real.norm_eq_abs] at this
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_right (hM i) hv

lemma gdf_phi_sub {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x y : Fin n → ℝ) :
    phi d x - phi d y = (J d x y).mulVec (x - y) := by
  funext i
  rw [Pi.sub_apply, gdf_ftc hn d x y i]
  simp only [Matrix.mulVec, dotProduct, J]

lemma gdf_nonexp {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (x y : Fin n → ℝ) :
    ‖phi d x - phi d y‖ ≤ ‖x - y‖ := by
  rw [gdf_phi_sub hn d x y]
  have := gdf_mulVec_norm (J d x y) 1 zero_le_one (gdf_J_row hn d x y) (x - y)
  linarith

theorem gdf_eq9 {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (x y : Fin n → ℝ) :
    let K : ℝ := max (max ‖x‖ ‖y‖) (max ‖phi d x‖ ‖phi d y‖)
    let δ : ℝ := Real.exp (-4 * K) / 2
    let θ : ℝ := 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1)
    ‖phi d (phi d x) - phi d (phi d y)‖ ≤ θ * ‖x - y‖ ∧
    0 ≤ θ ∧ (3 ≤ n → θ < 1) ∧
    ‖phi d x - phi d y‖ ≤ ‖x - y‖ := by
  intro K δ θ
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hm : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hxK : ‖x‖ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hyK : ‖y‖ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hpxK : ‖phi d x‖ ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hpyK : ‖phi d y‖ ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hxK
  have hδpos : 0 < δ := by show 0 < Real.exp (-4 * K) / 2; positivity
  have hδle : δ ≤ 1 / 2 := by
    show Real.exp (-4 * K) / 2 ≤ 1 / 2
    have : Real.exp (-4 * K) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hθ0 : 0 ≤ θ := by
    show 0 ≤ 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1)
    have : 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) ≤ 1 := by
      rw [div_le_one hm]
      have hd2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hd2 (by linarith : (0:ℝ) ≤ (n:ℝ) - 2)]
    linarith
  refine ⟨?_, hθ0, ?_, gdf_nonexp hn d x y⟩
  · have b1 := gdf_J_bds hn d hd hxK hyK
    have b2 := gdf_J_bds hn d hd hpxK hpyK
    have e : phi d (phi d x) - phi d (phi d y) =
        (J d (phi d x) (phi d y) * J d x y).mulVec (x - y) := by
      rw [gdf_phi_sub hn d (phi d x) (phi d y), gdf_phi_sub hn d x y, Matrix.mulVec_mulVec]
    rw [e]
    refine gdf_mulVec_norm _ θ hθ0 (fun i => ?_) _
    have := gdf_L21 hn hδpos (A := J d (phi d x) (phi d y)) (B := J d x y)
      (fun i => gdf_J_row hn d _ _ i) b2.2 b2.1 (fun i => gdf_J_row hn d _ _ i) b1.2 b1.1 i
    exact this
  · intro h3
    have h3' : (1:ℝ) ≤ (n:ℝ) - 2 := by
      have : (3:ℝ) ≤ n := by exact_mod_cast h3
      linarith
    show 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) < 1
    have : 0 < 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) := by
      apply div_pos _ hm
      have : 0 < (n:ℝ) - 2 := by linarith
      positivity
    linarith

lemma gdf_two_step {n : ℕ} (hn : 3 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    {x y : Fin n → ℝ} {L : ℝ} (hx : ‖x‖ ≤ L) (hy : ‖y‖ ≤ L) (hpx : ‖phi d x‖ ≤ L)
    (hpy : ‖phi d y‖ ≤ L) :
    ‖phi d (phi d x) - phi d (phi d y)‖ ≤ (1 - (Real.exp (-4 * L) / 2) ^ 2) * ‖x - y‖ := by
  have h := (gdf_eq9 (by omega) d hd x y).1
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hm : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hKL : max (max ‖x‖ ‖y‖) (max ‖phi d x‖ ‖phi d y‖) ≤ L :=
    max_le (max_le hx hy) (max_le hpx hpy)
  have hexp : Real.exp (-4 * L) ≤ Real.exp (-4 * max (max ‖x‖ ‖y‖) (max ‖phi d x‖ ‖phi d y‖)) :=
    Real.exp_le_exp.2 (by linarith)
  set δK : ℝ := Real.exp (-4 * max (max ‖x‖ ‖y‖) (max ‖phi d x‖ ‖phi d y‖)) / 2 with hδK
  set δL : ℝ := Real.exp (-4 * L) / 2 with hδL
  have hδL0 : 0 ≤ δL := by positivity
  have hδ : δL ≤ δK := by rw [hδK, hδL]; linarith
  have h2 : δL ^ 2 ≤ δK ^ 2 := pow_le_pow_left₀ hδL0 hδ 2
  have h3 : δL ^ 2 ≤ 2 * ((n:ℝ) - 2) * δK ^ 2 / ((n:ℝ) - 1) := by
    rw [le_div_iff₀ hm]
    nlinarith [sq_nonneg δK, sq_nonneg δL]
  have h4 : 1 - 2 * ((n:ℝ) - 2) * δK ^ 2 / ((n:ℝ) - 1) ≤ 1 - δL ^ 2 := by linarith
  exact h.trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg _))

lemma gdf_iter_nonexp {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) {β : Fin n → ℝ} (hβ : phi d β = β)
    (x : Fin n → ℝ) (k : ℕ) : ‖(phi d)^[k] x - β‖ ≤ ‖x - β‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := gdf_nonexp hn d ((phi d)^[k] x) β
    rw [hβ] at this
    exact this.trans ih

lemma gdf_iter_bound {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) {β : Fin n → ℝ} (hβ : phi d β = β)
    (x : Fin n → ℝ) (k : ℕ) : ‖(phi d)^[k] x‖ ≤ 2 * ‖β‖ + ‖x‖ := by
  have h1 := gdf_iter_nonexp hn d hβ x k
  have h2 : ‖x - β‖ ≤ ‖x‖ + ‖β‖ := norm_sub_le _ _
  have h3 : ‖(phi d)^[k] x‖ ≤ ‖(phi d)^[k] x - β‖ + ‖β‖ := by
    have := norm_add_le ((phi d)^[k] x - β) β
    simpa using this
  linarith

/-- two-step contraction along the orbit towards a fixed point -/
lemma gdf_orbit_two {n : ℕ} (hn : 3 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) {β : Fin n → ℝ}
    (hβ : phi d β = β) (x₀ : Fin n → ℝ) (k : ℕ) :
    ‖(phi d)^[k + 2] x₀ - β‖ ≤
      (1 - (Real.exp (-4 * (2 * ‖β‖ + ‖x₀‖)) / 2) ^ 2) * ‖(phi d)^[k] x₀ - β‖ := by
  have hn2 : 2 ≤ n := by omega
  have hb := fun j => gdf_iter_bound hn2 d hβ x₀ j
  have hβL : ‖β‖ ≤ 2 * ‖β‖ + ‖x₀‖ := by linarith [norm_nonneg β, norm_nonneg x₀]
  have e := gdf_two_step hn d hd (x := (phi d)^[k] x₀) (y := β) (L := 2 * ‖β‖ + ‖x₀‖)
    (hb k) hβL (by rw [← Function.iterate_succ_apply' (phi d)]; exact hb (k+1))
    (by rw [hβ]; exact hβL)
  rw [hβ, hβ] at e
  have e2 : (phi d)^[k + 2] x₀ = phi d (phi d ((phi d)^[k] x₀)) := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  rw [e2]
  exact e

lemma gdf_orbit_step {n : ℕ} (hn : 3 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) (x₀ : Fin n → ℝ)
    {L : ℝ} (hb : ∀ j, ‖(phi d)^[j] x₀‖ ≤ L) (k : ℕ) :
    ‖(phi d)^[k + 3] x₀ - (phi d)^[k + 2] x₀‖ ≤
      (1 - (Real.exp (-4 * L) / 2) ^ 2) * ‖(phi d)^[k + 1] x₀ - (phi d)^[k] x₀‖ := by
  have e := gdf_two_step hn d hd (x := (phi d)^[k + 1] x₀) (y := (phi d)^[k] x₀) (L := L)
    (hb _) (hb _) (by rw [← Function.iterate_succ_apply' (phi d)]; exact hb _)
    (by rw [← Function.iterate_succ_apply' (phi d)]; exact hb _)
  have e1 : (phi d)^[k + 3] x₀ = phi d (phi d ((phi d)^[k + 1] x₀)) := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
  have e2 : (phi d)^[k + 2] x₀ = phi d (phi d ((phi d)^[k] x₀)) := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  rw [e1, e2]
  exact e

theorem solution :
    ∃ Θ : ℝ → ℝ → ℝ, Continuous (Function.uncurry Θ) ∧ (∀ a b, 0 ≤ Θ a b ∧ Θ a b < 1) ∧
      ∀ n : ℕ, 3 ≤ n → ∀ d : Fin n → ℝ, (∀ i, 0 < d i) →
        ∀ βhat : Fin n → ℝ, phi d βhat = βhat → ∀ (x₀ : Fin n → ℝ) (k : ℕ),
          ‖(phi d)^[k + 1] x₀ - βhat‖ ≤ ‖(phi d)^[k] x₀ - βhat‖ ∧
          ‖(phi d)^[k + 3] x₀ - (phi d)^[k + 2] x₀‖ ≤
            Θ ‖βhat‖ ‖x₀‖ * ‖(phi d)^[k + 1] x₀ - (phi d)^[k] x₀‖ ∧
          ‖(phi d)^[k + 2] x₀ - βhat‖ ≤ Θ ‖βhat‖ ‖x₀‖ * ‖(phi d)^[k] x₀ - βhat‖ := by
  refine ⟨fun a b => 1 - (Real.exp (-4 * (2 * |a| + |b|)) / 2) ^ 2, ?_, ?_, ?_⟩
  · show Continuous (fun p : ℝ × ℝ => 1 - (Real.exp (-4 * (2 * |p.1| + |p.2|)) / 2) ^ 2)
    fun_prop
  · intro a b
    have h0 : 0 < Real.exp (-4 * (2 * |a| + |b|)) / 2 := by positivity
    have h1 : Real.exp (-4 * (2 * |a| + |b|)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith [abs_nonneg a, abs_nonneg b])
    constructor
    · nlinarith
    · nlinarith
  · intro n hn d hd β hβ x₀ k
    have hn2 : 2 ≤ n := by omega
    have habs : (2 * |‖β‖| + |‖x₀‖|) = 2 * ‖β‖ + ‖x₀‖ := by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    simp only [habs]
    refine ⟨?_, ?_, gdf_orbit_two hn d hd hβ x₀ k⟩
    · rw [Function.iterate_succ_apply']
      have := gdf_nonexp hn2 d ((phi d)^[k] x₀) β
      rwa [hβ] at this
    · exact gdf_orbit_step hn d hd x₀ (gdf_iter_bound hn2 d hβ x₀) k
