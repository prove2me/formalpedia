-- Prove2me | solution 1 for GivenDegreeSeq.FixedPoint.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:37:26.850954+00:00
-- url     : https://prove2.me/submissions/35648614-cf69-46ba-8c4d-87e9f4f94ad0

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

theorem solution {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    (∀ x y : Fin n → ℝ, phi d x - phi d y = (J d x y).mulVec (x - y)) ∧
    (∀ (z : Fin n → ℝ) (i j : Fin n), i ≠ j → partialPhi d z i j < 0) ∧
    (∀ (z : Fin n → ℝ) (i : Fin n), 0 < partialPhi d z i i) ∧
    (∀ (z : Fin n → ℝ) (i : Fin n), ∑ j : Fin n, |partialPhi d z i j| = 1) := by
  refine ⟨?_, fun z i j h => gdf_partial_off_neg hn d z h, fun z i => gdf_partial_diag_pos hn d z i,
    fun z i => gdf_row_sum hn d z i⟩
  intro x y
  funext i
  rw [Pi.sub_apply, gdf_ftc hn d x y i]
  simp only [Matrix.mulVec, dotProduct, J]
