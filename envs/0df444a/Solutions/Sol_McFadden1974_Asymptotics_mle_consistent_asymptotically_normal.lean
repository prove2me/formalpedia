-- Prove2me | solution 1 for McFadden1974.Asymptotics.mle_consistent_asymptotically_normal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T00:19:18.604604+00:00
-- url     : https://prove2.me/submissions/c94975ec-debb-46e0-91d3-5397535fcf49

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

set_option autoImplicit false

namespace McFadden1974.Asymptotics
open MeasureTheory ProbabilityTheory Filter Topology

variable {K : ℕ}

lemma sumExp_pos (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    0 < ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ) := by
  have : Nonempty (Fin (D.J m)) := ⟨⟨0, D.one_le_J m⟩⟩
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

lemma prob_pos' (D : SerialData K) (m : ℕ) (i : Fin (D.J m)) (θ : EuclideanSpace ℝ (Fin K)) :
    0 < prob D m i θ := div_pos (Real.exp_pos _) (sumExp_pos D m θ)

lemma sum_prob (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    ∑ i : Fin (D.J m), prob D m i θ = 1 := by
  unfold prob
  rw [← Finset.sum_div]
  exact div_self (sumExp_pos D m θ).ne'

lemma prob_eq (D : SerialData K) (m : ℕ) (i : Fin (D.J m)) (θ : EuclideanSpace ℝ (Fin K)) :
    prob D m i θ = Real.exp (inner ℝ (D.z m i) θ -
      Real.log (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ))) := by
  rw [Real.exp_sub, Real.exp_log (sumExp_pos D m θ)]; rfl

lemma hasFDerivAt_inner_left (z : EuclideanSpace ℝ (Fin K)) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ' : EuclideanSpace ℝ (Fin K) => inner ℝ z θ') (innerSL ℝ z) θ :=
  (innerSL ℝ z).hasFDerivAt

lemma hasFDerivAt_logSumExp (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ' => Real.log (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ')))
      (innerSL ℝ (zbar D m θ)) θ := by
  have h1 : HasFDerivAt (fun θ' : EuclideanSpace ℝ (Fin K) =>
      ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ'))
      (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ) • innerSL ℝ (D.z m j)) θ := by
    apply HasFDerivAt.fun_sum
    intro j _
    exact (hasFDerivAt_inner_left (D.z m j) θ).exp
  have h2 := h1.log (sumExp_pos D m θ).ne'
  have e : innerSL ℝ (zbar D m θ) = (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ))⁻¹ •
      ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ) • innerSL ℝ (D.z m j) := by
    unfold zbar prob
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul, div_eq_inv_mul]
  rw [e]; exact h2


lemma toEuclideanLin_vecMulVec (u v h : EuclideanSpace ℝ (Fin K)) :
    Matrix.toEuclideanLin (Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp v)) h =
      inner ℝ v h • u := by
  ext a
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    PiLp.inner_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma hasGradientAt_logProb (D : SerialData K) (m : ℕ) (i : Fin (D.J m))
    (θ : EuclideanSpace ℝ (Fin K)) :
    HasGradientAt (fun θ' => Real.log (prob D m i θ')) (D.z m i - zbar D m θ) θ := by
  have h := (hasFDerivAt_inner_left (D.z m i) θ).sub (hasFDerivAt_logSumExp D m θ)
  have hf : (fun θ' => Real.log (prob D m i θ')) = fun θ' => inner ℝ (D.z m i) θ' -
      Real.log (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ')) := by
    funext θ'; rw [prob_eq, Real.log_exp]
  rw [hf, hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv h ?_
  ext w
  simp [inner_sub_left]

lemma hasFDerivAt_prob (D : SerialData K) (m : ℕ) (j : Fin (D.J m))
    (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ' => prob D m j θ')
      (prob D m j θ • innerSL ℝ (D.z m j - zbar D m θ)) θ := by
  have h := ((hasFDerivAt_inner_left (D.z m j) θ).sub (hasFDerivAt_logSumExp D m θ)).exp
  have hf : (fun θ' => prob D m j θ') = fun θ' => Real.exp (inner ℝ (D.z m j) θ' -
      Real.log (∑ i : Fin (D.J m), Real.exp (inner ℝ (D.z m i) θ'))) := by
    funext θ'; exact prob_eq D m j θ'
  rw [hf]
  refine HasFDerivAt.congr_fderiv h ?_
  simp only [Pi.sub_apply]
  rw [← prob_eq, map_sub]


lemma sum_prob_sub_zbar (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    ∑ i : Fin (D.J m), prob D m i θ • (D.z m i - zbar D m θ) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_prob, one_smul]
  rw [← zbar]; simp

lemma momentMatrix_apply (D : SerialData K) (m : ℕ) (θ h : EuclideanSpace ℝ (Fin K)) :
    Matrix.toEuclideanLin (momentMatrix D θ m) h =
      ∑ i : Fin (D.J m), (prob D m i θ * inner ℝ (D.z m i - zbar D m θ) h) • (D.z m i - zbar D m θ) := by
  unfold momentMatrix
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, toEuclideanLin_vecMulVec, smul_smul]

lemma hasFDerivAt_zbar (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ' => zbar D m θ')
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (momentMatrix D θ m))) θ := by
  have h : HasFDerivAt (fun θ' => ∑ j : Fin (D.J m), prob D m j θ' • D.z m j)
      (∑ j : Fin (D.J m), (prob D m j θ • innerSL ℝ (D.z m j - zbar D m θ)).smulRight (D.z m j)) θ := by
    apply HasFDerivAt.fun_sum
    intro j _
    exact (hasFDerivAt_prob D m j θ).smul_const (D.z m j)
  unfold zbar
  refine HasFDerivAt.congr_fderiv h ?_
  ext1 w
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, LinearMap.coe_toContinuousLinearMap',
    momentMatrix_apply, smul_eq_mul]
  have hz : ∑ i : Fin (D.J m), (prob D m i θ * inner ℝ (D.z m i - zbar D m θ) w) • (D.z m i - zbar D m θ)
      = ∑ i : Fin (D.J m), (prob D m i θ * inner ℝ (D.z m i - zbar D m θ) w) • D.z m i := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    have : ∑ i : Fin (D.J m), (prob D m i θ * inner ℝ (D.z m i - zbar D m θ) w) • zbar D m θ = 0 := by
      rw [← Finset.sum_smul]
      have : ∑ i : Fin (D.J m), prob D m i θ * inner ℝ (D.z m i - zbar D m θ) w = 0 := by
        have := congrArg (fun v => inner ℝ v w) (sum_prob_sub_zbar D m θ)
        simp only [sum_inner, inner_smul_left, inner_zero_left] at this
        simpa using this
      rw [this, zero_smul]
    rw [this, sub_zero]
  rw [hz]

lemma hasFDerivAt_score (D : SerialData K) (m : ℕ) (i : Fin (D.J m))
    (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ' => D.z m i - zbar D m θ')
      (-(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (momentMatrix D θ m)))) θ := by
  have := (hasFDerivAt_const (D.z m i) θ).sub (hasFDerivAt_zbar D m θ)
  exact this.congr_fderiv (by simp)


lemma prob_nonneg' (D : SerialData K) (m : ℕ) (i : Fin (D.J m)) (θ : EuclideanSpace ℝ (Fin K)) :
    0 ≤ prob D m i θ := (prob_pos' D m i θ).le

lemma prob_le_one (D : SerialData K) (m : ℕ) (i : Fin (D.J m)) (θ : EuclideanSpace ℝ (Fin K)) :
    prob D m i θ ≤ 1 := by
  rw [← sum_prob D m θ]
  exact Finset.single_le_sum (f := fun i => prob D m i θ) (fun j _ => prob_nonneg' D m j θ)
    (Finset.mem_univ i)

lemma norm_zbar_le (D : SerialData K) {m : ℕ} (M : ℝ) (hM : ∀ i : Fin (D.J m), ‖D.z m i‖ ≤ M)
    (θ : EuclideanSpace ℝ (Fin K)) : ‖zbar D m θ‖ ≤ M := by
  unfold zbar
  calc ‖∑ i : Fin (D.J m), prob D m i θ • D.z m i‖ ≤ ∑ i : Fin (D.J m), ‖prob D m i θ • D.z m i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin (D.J m), prob D m i θ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (prob_nonneg' D m i θ)]
        exact mul_le_mul_of_nonneg_left (hM i) (prob_nonneg' D m i θ)
    _ = M := by rw [← Finset.sum_mul, sum_prob, one_mul]

lemma lip_prob (D : SerialData K) (m : ℕ) (M : ℝ) (hM : ∀ i : Fin (D.J m), ‖D.z m i‖ ≤ M)
    (j : Fin (D.J m)) (θ θ' : EuclideanSpace ℝ (Fin K)) :
    |prob D m j θ - prob D m j θ'| ≤ 2 * M * ‖θ - θ'‖ := by
  have hb : ∀ x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin K))),
      ‖prob D m j x • innerSL ℝ (D.z m j - zbar D m x)‖ ≤ 2 * M := by
    intro x _
    calc ‖prob D m j x • innerSL ℝ (D.z m j - zbar D m x)‖
        = prob D m j x * ‖innerSL ℝ (D.z m j - zbar D m x)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (prob_nonneg' D m j x)]
      _ ≤ 1 * ‖D.z m j - zbar D m x‖ := by
          calc prob D m j x * ‖innerSL ℝ (D.z m j - zbar D m x)‖
              ≤ 1 * ‖innerSL ℝ (D.z m j - zbar D m x)‖ :=
                mul_le_mul_of_nonneg_right (prob_le_one D m j x) (norm_nonneg _)
            _ = 1 * ‖D.z m j - zbar D m x‖ := by rw [innerSL_apply_norm]
      _ ≤ 2 * M := by
          have h1 := norm_sub_le (D.z m j) (zbar D m x)
          have h2 := hM j
          have h3 := norm_zbar_le D M hM x
          linarith
  have := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun θ' => prob D m j θ') (f' := fun x => prob D m j x • innerSL ℝ (D.z m j - zbar D m x))
    (fun x _ => (hasFDerivAt_prob D m j x).hasFDerivWithinAt) hb (Set.mem_univ θ') (Set.mem_univ θ)
  simpa [Real.norm_eq_abs] using this


lemma lip_zbar (D : SerialData K) {m : ℕ} (Jstar : ℕ) (M : ℝ) (hJ : D.J m ≤ Jstar)
    (hM : ∀ i : Fin (D.J m), ‖D.z m i‖ ≤ M) (θ θ' : EuclideanSpace ℝ (Fin K)) :
    ‖zbar D m θ - zbar D m θ'‖ ≤ (Jstar * (2 * M * M)) * ‖θ - θ'‖ := by
  unfold zbar
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ i : Fin (D.J m), (prob D m i θ • D.z m i - prob D m i θ' • D.z m i)‖
      ≤ ∑ i : Fin (D.J m), ‖prob D m i θ • D.z m i - prob D m i θ' • D.z m i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (D.J m), (2 * M * ‖θ - θ'‖) * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        have h0 : 0 ≤ M := (norm_nonneg _).trans (hM i)
        exact mul_le_mul (lip_prob D m M hM i θ θ') (hM i) (norm_nonneg _)
          (by positivity)
    _ = (Fintype.card (Fin (D.J m)) : ℝ) * ((2 * M * ‖θ - θ'‖) * M) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Jstar * (2 * M * M)) * ‖θ - θ'‖ := by
        have h0 : 0 ≤ M := by
          have : Nonempty (Fin (D.J m)) := ⟨⟨0, D.one_le_J m⟩⟩
          obtain ⟨i⟩ := this
          exact (norm_nonneg _).trans (hM i)
        have hc : (Fintype.card (Fin (D.J m)) : ℝ) ≤ Jstar := by
          rw [Fintype.card_fin]; exact_mod_cast hJ
        have : 0 ≤ (2 * M * ‖θ - θ'‖) * M := by positivity
        calc (Fintype.card (Fin (D.J m)) : ℝ) * ((2 * M * ‖θ - θ'‖) * M)
            ≤ Jstar * ((2 * M * ‖θ - θ'‖) * M) := mul_le_mul_of_nonneg_right hc this
          _ = (Jstar * (2 * M * M)) * ‖θ - θ'‖ := by ring


lemma abs_coord_le (x : EuclideanSpace ℝ (Fin K)) (a : Fin K) : |WithLp.ofLp x a| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x a
  simpa [Real.norm_eq_abs] using this

lemma momentMatrix_entry (D : SerialData K) (θ : EuclideanSpace ℝ (Fin K)) (m : ℕ) (a b : Fin K) :
    momentMatrix D θ m a b = ∑ i : Fin (D.J m), prob D m i θ *
      (WithLp.ofLp (D.z m i - zbar D m θ) a * WithLp.ofLp (D.z m i - zbar D m θ) b) := by
  unfold momentMatrix
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply]

lemma real_prod_diff (p p' u u' v v' A B d : ℝ) (hp' : 0 ≤ p') (hu : |u| ≤ A) (hv : |v'| ≤ B)
    (hv2 : |v| ≤ B) (hu' : |u'| ≤ A) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdu : |u - u'| ≤ d) (hdv : |v - v'| ≤ d) :
    |p * (u * v) - p' * (u' * v')| ≤ |p - p'| * (A * B) + p' * (d * B + A * d) := by
  have e : p * (u * v) - p' * (u' * v') = (p - p') * (u * v) + p' * ((u - u') * v) + p' * (u' * (v - v')) := by ring
  rw [e]
  have h1 : |(p - p') * (u * v)| ≤ |p - p'| * (A * B) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hu hv2 (abs_nonneg _) hA) (abs_nonneg _)
  have h2 : |p' * ((u - u') * v)| ≤ p' * (d * B) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp']
    exact mul_le_mul_of_nonneg_left (mul_le_mul hdu hv2 (abs_nonneg _) (hdu.trans' (abs_nonneg _))) hp'
  have h3 : |p' * (u' * (v - v'))| ≤ p' * (A * d) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hp']
    exact mul_le_mul_of_nonneg_left (mul_le_mul hu' hdv (abs_nonneg _) hA) hp'
  calc _ ≤ |(p - p') * (u * v) + p' * ((u - u') * v)| + |p' * (u' * (v - v'))| := abs_add_le _ _
    _ ≤ |(p - p') * (u * v)| + |p' * ((u - u') * v)| + |p' * (u' * (v - v'))| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

lemma lip_moment (D : SerialData K) {m : ℕ} (Jstar : ℕ) (M : ℝ) (hJ : D.J m ≤ Jstar)
    (hM : ∀ i : Fin (D.J m), ‖D.z m i‖ ≤ M) (θ θ' : EuclideanSpace ℝ (Fin K)) (a b : Fin K) :
    |momentMatrix D θ m a b - momentMatrix D θ' m a b| ≤
      (16 * Jstar * M ^ 3) * ‖θ - θ'‖ := by
  have h0 : 0 ≤ M := by
    have : Nonempty (Fin (D.J m)) := ⟨⟨0, D.one_le_J m⟩⟩
    obtain ⟨i⟩ := this
    exact (norm_nonneg _).trans (hM i)
  set δ := ‖θ - θ'‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hz := lip_zbar D Jstar M hJ hM θ θ'
  have hcard : (Fintype.card (Fin (D.J m)) : ℝ) ≤ Jstar := by
    rw [Fintype.card_fin]; exact_mod_cast hJ
  set d := (Jstar * (2 * M * M)) * δ with hd
  have hd0 : 0 ≤ d := by positivity
  rw [momentMatrix_entry, momentMatrix_entry, ← Finset.sum_sub_distrib]
  have hterm : ∀ i : Fin (D.J m), |prob D m i θ *
      (WithLp.ofLp (D.z m i - zbar D m θ) a * WithLp.ofLp (D.z m i - zbar D m θ) b) -
      prob D m i θ' * (WithLp.ofLp (D.z m i - zbar D m θ') a * WithLp.ofLp (D.z m i - zbar D m θ') b)|
      ≤ (2 * M * δ) * (2 * M * (2 * M)) + prob D m i θ' * (d * (2 * M) + 2 * M * d) := by
    intro i
    have hu : ∀ x, |WithLp.ofLp (D.z m i - zbar D m x) a| ≤ 2 * M := fun x =>
      (abs_coord_le _ a).trans ((norm_sub_le _ _).trans (by
        have := hM i; have := norm_zbar_le D M hM x; linarith))
    have hv : ∀ x, |WithLp.ofLp (D.z m i - zbar D m x) b| ≤ 2 * M := fun x =>
      (abs_coord_le _ b).trans ((norm_sub_le _ _).trans (by
        have := hM i; have := norm_zbar_le D M hM x; linarith))
    have hdiff : ∀ c : Fin K, |WithLp.ofLp (D.z m i - zbar D m θ) c -
        WithLp.ofLp (D.z m i - zbar D m θ') c| ≤ d := fun c => by
      have : WithLp.ofLp (D.z m i - zbar D m θ) c - WithLp.ofLp (D.z m i - zbar D m θ') c =
          WithLp.ofLp (zbar D m θ' - zbar D m θ) c := by simp
      rw [this]
      refine (abs_coord_le _ c).trans ?_
      rw [norm_sub_rev]; exact hz
    refine (real_prod_diff _ _ _ _ _ _ (2 * M) (2 * M) d (prob_nonneg' D m i θ') (hu θ) (hv θ')
      (hv θ) (hu θ') (by positivity) (by positivity) (hdiff a) (hdiff b)).trans ?_
    gcongr
    exact lip_prob D m M hM i θ θ'
  calc |∑ i : Fin (D.J m), _| ≤ ∑ i : Fin (D.J m), |_| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (D.J m), ((2 * M * δ) * (2 * M * (2 * M)) + prob D m i θ' * (d * (2 * M) + 2 * M * d)) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card (Fin (D.J m)) : ℝ) * ((2 * M * δ) * (2 * M * (2 * M))) +
        (d * (2 * M) + 2 * M * d) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.sum_mul, sum_prob, one_mul]
    _ ≤ (16 * Jstar * M ^ 3) * δ := by
        have hc : (Fintype.card (Fin (D.J m)) : ℝ) * ((2 * M * δ) * (2 * M * (2 * M))) ≤
            Jstar * ((2 * M * δ) * (2 * M * (2 * M))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        have : d * (2 * M) + 2 * M * d = 8 * Jstar * M ^ 3 * δ := by rw [hd]; ring
        nlinarith [hc, this]


lemma avg_moment_entry (D : SerialData K) (θ : EuclideanSpace ℝ (Fin K)) (q : ℕ) (a b : Fin K) :
    ((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ m) a b =
      (q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, momentMatrix D θ m a b := by
  simp [Matrix.sum_apply]

/-- C3: uniform convergence of the averaged moment matrices near θ₀ (entrywise). -/
theorem hessian_avg_uniform (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) :
    ∀ η > 0, ∃ r > 0, ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ θ : EuclideanSpace ℝ (Fin K), ‖θ - θ₀‖ ≤ r →
      ∀ a b : Fin K,
        |((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ m) a b - Ωlim a b| ≤ η := by
  intro η hη
  set L : ℝ := 16 * Jstar * M ^ 3 with hL
  have hL0 : 0 ≤ L := by
    have h0 : 0 ≤ M := by
      have : Nonempty (Fin (D.J 0)) := ⟨⟨0, D.one_le_J 0⟩⟩
      obtain ⟨i⟩ := this
      exact (norm_nonneg _).trans (h7.bounded.norm_z_le 0 i)
    rw [hL]; positivity
  refine ⟨η / (2 * (L + 1)), by positivity, ?_⟩
  have hev : ∀ᶠ q : ℕ in atTop, ∀ a b : Fin K,
      |((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ₀ m) a b - Ωlim a b| ≤ η / 2 := by
    rw [Filter.eventually_all]; intro a
    rw [Filter.eventually_all]; intro b
    have h1 := (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h7.tendsto_avg a) b)
    have h2 := Metric.tendsto_nhds.1 h1 (η / 2) (by positivity)
    filter_upwards [h2] with q hq
    exact (Real.dist_eq _ _ ▸ hq).le
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 1))
  refine ⟨q₀, fun q hq θ hθ a b => ?_⟩
  obtain ⟨hq1, hq2⟩ := hq₀ q hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq2
  have hlip : |(q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, momentMatrix D θ m a b -
      (q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, momentMatrix D θ₀ m a b| ≤ L * ‖θ - θ₀‖ := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hqpos)]
    calc (q : ℝ)⁻¹ * |∑ m ∈ Finset.range q, (momentMatrix D θ m a b - momentMatrix D θ₀ m a b)|
        ≤ (q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, (L * ‖θ - θ₀‖) := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
          exact lip_moment D Jstar M (h7.bounded.J_le m) (h7.bounded.norm_z_le m) θ θ₀ a b
      _ = L * ‖θ - θ₀‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hr : L * ‖θ - θ₀‖ ≤ η / 2 := by
    calc L * ‖θ - θ₀‖ ≤ L * (η / (2 * (L + 1))) := mul_le_mul_of_nonneg_left hθ hL0
      _ ≤ (L + 1) * (η / (2 * (L + 1))) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = η / 2 := by field_simp
  have h1 := hq1 a b
  rw [avg_moment_entry] at h1
  rw [avg_moment_entry]
  calc _ = |((q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, momentMatrix D θ m a b -
      (q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, momentMatrix D θ₀ m a b) +
      ((q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, momentMatrix D θ₀ m a b - Ωlim a b)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)


/-- C5 (coordinatewise mean value form). -/
theorem score_linearization_coord {Ω : Type*} (D : SerialData K)
    (Y : (m : ℕ) → Ω → Fin (D.J m)) (θ₀ θ : EuclideanSpace ℝ (Fin K)) (q : ℕ) (ω : Ω)
    (a : Fin K) :
    ∃ t ∈ Set.Icc (0:ℝ) 1,
      WithLp.ofLp (∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀) -
        ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ)) a =
      ∑ b : Fin K, (∑ m ∈ Finset.range q, momentMatrix D (θ₀ + t • (θ - θ₀)) m a b) *
        WithLp.ofLp (θ - θ₀) b := by
  set v := θ - θ₀ with hv
  set g : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K) :=
    fun θ' => ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ') with hg
  set f : ℝ → ℝ := fun t => WithLp.ofLp (g (θ₀ + t • v)) a with hf
  have hderiv : ∀ t : ℝ, HasDerivAt f
      (- ∑ b : Fin K, (∑ m ∈ Finset.range q, momentMatrix D (θ₀ + t • v) m a b) *
        WithLp.ofLp v b) t := by
    intro t
    have h1 : HasFDerivAt g (∑ m ∈ Finset.range q,
        (-(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (momentMatrix D (θ₀ + t • v) m)))))
        (θ₀ + t • v) := by
      apply HasFDerivAt.fun_sum
      intro m _
      exact hasFDerivAt_score D m (Y m ω) (θ₀ + t • v)
    have h2 : HasDerivAt (fun t : ℝ => θ₀ + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add θ₀
    have h3 := (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (h1.comp_hasDerivAt t h2)
    refine h3.congr_deriv ?_
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Finset.sum_mul, Finset.sum_comm (s := Finset.range q)]
  have hcont : ContinuousOn f (Set.Icc 0 1) := fun t _ => (hderiv t).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f (fun t =>
    - ∑ b : Fin K, (∑ m ∈ Finset.range q, momentMatrix D (θ₀ + t • v) m a b) * WithLp.ofLp v b)
    (zero_lt_one) hcont (fun t _ => hderiv t)
  refine ⟨c, Set.Ioo_subset_Icc_self hc, ?_⟩
  simp only [hf, hg, zero_smul, add_zero, one_smul, sub_zero, div_one] at hc'
  have e : θ₀ + v = θ := by simp [hv]
  rw [e] at hc'
  have : WithLp.ofLp (∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀) -
        ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ)) a =
      WithLp.ofLp (g θ₀) a - WithLp.ofLp (g θ) a := by simp [hg]
  rw [this]
  linarith


lemma descent_lemma (φ φ' φ'' : ℝ → ℝ) (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (h1 : ∀ t, HasDerivAt φ (φ' t) t) (h2 : ∀ t, HasDerivAt φ' (φ'' t) t)
    (hneg : ∀ t, φ'' t ≤ 0) (hstrong : ∀ t ∈ Set.Icc (0:ℝ) ρ, φ'' t ≤ -κ)
    (h0 : φ' 0 < κ * ρ / 2) : ∀ t, ρ ≤ t → φ t < φ 0 := by
  -- φ' antitone everywhere
  have hanti : Antitone φ' := by
    refine antitone_of_deriv_nonpos (fun t => (h2 t).differentiableAt) (fun t => ?_)
    rw [(h2 t).deriv]; exact hneg t
  -- g t = φ' t + κ t antitone on [0, ρ]
  have hg : ∀ t ∈ Set.Icc (0:ℝ) ρ, φ' t ≤ φ' 0 - κ * t := by
    have hA : AntitoneOn (fun t => φ' t + κ * t) (Set.Icc 0 ρ) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 ρ) ?_ ?_ ?_
      · exact fun t _ => ((h2 t).add ((hasDerivAt_id t).const_mul κ)).continuousAt.continuousWithinAt
      · exact fun t _ => ((h2 t).add ((hasDerivAt_id t).const_mul κ)).differentiableAt.differentiableWithinAt
      · intro t ht
        have hd2 : HasDerivAt (fun t => φ' t + κ * t) (φ'' t + κ) t := by
          exact ((h2 t).add ((hasDerivAt_id' t).const_mul κ)).congr_deriv (by ring)
        rw [hd2.deriv]
        have := hstrong t (interior_subset ht)
        linarith
    intro t ht
    have := hA ⟨le_refl 0, hρ.le⟩ ht ht.1
    simp at this; linarith
  -- h t = φ t - φ 0 - φ' 0 * t + κ t^2/2 antitone on [0, ρ]
  have hh : φ ρ - φ 0 - φ' 0 * ρ + κ * ρ ^ 2 / 2 ≤ 0 := by
    have hd : ∀ t, HasDerivAt (fun t => φ t - φ 0 - φ' 0 * t + κ * t ^ 2 / 2)
        (φ' t - φ' 0 + κ * t) t := by
      intro t
      have h3 : HasDerivAt (fun t : ℝ => κ * t ^ 2 / 2) (κ * t) t := by
        have := ((hasDerivAt_pow 2 t).const_mul κ).div_const 2
        exact this.congr_deriv (by simp; ring)
      have h4 : HasDerivAt (fun t : ℝ => φ' 0 * t) (φ' 0) t := by
        exact ((hasDerivAt_id' t).const_mul (φ' 0)).congr_deriv (by ring)
      exact ((((h1 t).sub_const (φ 0)).sub h4).add h3)
    have hA : AntitoneOn (fun t => φ t - φ 0 - φ' 0 * t + κ * t ^ 2 / 2) (Set.Icc 0 ρ) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 ρ) ?_ ?_ ?_
      · exact fun t _ => (hd t).continuousAt.continuousWithinAt
      · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hd t).deriv]
        have := hg t (interior_subset ht)
        linarith
    have := hA ⟨le_refl 0, hρ.le⟩ ⟨hρ.le, le_refl ρ⟩ hρ.le
    simpa using this
  have hφρ : φ ρ < φ 0 := by nlinarith
  have hφ'ρ : φ' ρ < 0 := by
    have := hg ρ ⟨hρ.le, le_refl ρ⟩
    nlinarith
  intro t ht
  have hφanti : AntitoneOn φ (Set.Ici ρ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici ρ) ?_ ?_ ?_
    · exact fun t _ => (h1 t).continuousAt.continuousWithinAt
    · exact fun t _ => (h1 t).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(h1 s).deriv]
      have hs' : ρ ≤ s := by simpa using interior_subset hs
      exact ((hanti hs').trans hφ'ρ.le)
  exact (hφanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht).trans_lt hφρ


/-- the score sum -/
noncomputable def scoreSum {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (q : ℕ) (ω : Ω) (θ : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K) :=
  ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ)

lemma hasFDerivAt_logProb (D : SerialData K) (m : ℕ) (i : Fin (D.J m))
    (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ' => Real.log (prob D m i θ')) (innerSL ℝ (D.z m i - zbar D m θ)) θ := by
  have h := (hasGradientAt_logProb D m i θ).hasFDerivAt
  refine h.congr_fderiv ?_
  ext w
  simp

lemma hasFDerivAt_logLik {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (q : ℕ) (ω : Ω) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ' => logLik D Y q θ' ω) (innerSL ℝ (scoreSum D Y q ω θ)) θ := by
  have h : HasFDerivAt (fun θ' => ∑ m ∈ Finset.range q, Real.log (prob D m (Y m ω) θ'))
      (∑ m ∈ Finset.range q, innerSL ℝ (D.z m (Y m ω) - zbar D m θ)) θ :=
    HasFDerivAt.fun_sum fun m _ => hasFDerivAt_logProb D m (Y m ω) θ
  unfold logLik scoreSum
  rw [map_sum]
  exact h

lemma continuous_logLik {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (q : ℕ) (ω : Ω) : Continuous (fun θ' => logLik D Y q θ' ω) :=
  continuous_iff_continuousAt.2 fun θ => (hasFDerivAt_logLik D Y q ω θ).continuousAt

lemma inner_moment (D : SerialData K) (m : ℕ) (θ u : EuclideanSpace ℝ (Fin K)) :
    inner ℝ (Matrix.toEuclideanLin (momentMatrix D θ m) u) u =
      ∑ i : Fin (D.J m), prob D m i θ * (inner ℝ (D.z m i - zbar D m θ) u) ^ 2 := by
  rw [momentMatrix_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left]
  simp [sq]; ring

lemma inner_moment_nonneg (D : SerialData K) (m : ℕ) (θ u : EuclideanSpace ℝ (Fin K)) :
    0 ≤ inner ℝ (Matrix.toEuclideanLin (momentMatrix D θ m) u) u := by
  rw [inner_moment]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (prob_nonneg' D m i θ) (sq_nonneg _)

lemma inner_toEuclideanLin (A : Matrix (Fin K) (Fin K) ℝ) (u : EuclideanSpace ℝ (Fin K)) :
    inner ℝ (Matrix.toEuclideanLin A u) u =
      ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a * (A a b * WithLp.ofLp u b) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- derivative of the profile along a ray -/
lemma hasDerivAt_ray {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (q : ℕ) (ω : Ω) (θ₀ u : EuclideanSpace ℝ (Fin K)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => logLik D Y q (θ₀ + t • u) ω)
      (inner ℝ (scoreSum D Y q ω (θ₀ + t • u)) u) t := by
  have h2 : HasDerivAt (fun t : ℝ => θ₀ + t • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add θ₀
  have := (hasFDerivAt_logLik D Y q ω (θ₀ + t • u)).comp_hasDerivAt t h2
  exact this.congr_deriv (by simp)

lemma hasDerivAt_ray_deriv {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (q : ℕ) (ω : Ω) (θ₀ u : EuclideanSpace ℝ (Fin K)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => inner ℝ (scoreSum D Y q ω (θ₀ + t • u)) u)
      (- ∑ m ∈ Finset.range q, inner ℝ (Matrix.toEuclideanLin (momentMatrix D (θ₀ + t • u) m) u) u) t := by
  have h1 : HasFDerivAt (fun θ' => scoreSum D Y q ω θ')
      (∑ m ∈ Finset.range q,
        (-(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (momentMatrix D (θ₀ + t • u) m)))))
      (θ₀ + t • u) := by
    unfold scoreSum
    apply HasFDerivAt.fun_sum
    intro m _
    exact hasFDerivAt_score D m (Y m ω) (θ₀ + t • u)
  have h2 : HasDerivAt (fun t : ℝ => θ₀ + t • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add θ₀
  have h3 := (innerSL ℝ u : EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
    (h1.comp_hasDerivAt t h2)
  have e : (fun t : ℝ => inner ℝ (scoreSum D Y q ω (θ₀ + t • u)) u) =
      (innerSL ℝ u) ∘ (fun t : ℝ => scoreSum D Y q ω (θ₀ + t • u)) := by
    funext t; simp [real_inner_comm]
  rw [e]
  refine h3.congr_deriv ?_
  simp [real_inner_comm, inner_sum]

lemma exists_posdef_const (Ωlim : Matrix (Fin K) (Fin K) ℝ) (hP : Ωlim.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin K),
      c * ‖u‖ ^ 2 ≤ ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a * (Ωlim a b * WithLp.ofLp u b) := by
  set F : EuclideanSpace ℝ (Fin K) → ℝ := fun u =>
    ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a * (Ωlim a b * WithLp.ofLp u b) with hF
  have hFc : Continuous F := by
    simp only [hF]; fun_prop
  have hFpos : ∀ u : EuclideanSpace ℝ (Fin K), u ≠ 0 → 0 < F u := by
    intro u hu
    have hx : (WithLp.ofLp u) ≠ 0 := fun h => hu (by ext i; simpa using congrFun h i)
    have := hP.dotProduct_mulVec_pos hx
    simp only [hF]
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using this
  by_cases hs : (Metric.sphere (0 : EuclideanSpace ℝ (Fin K)) 1).Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin K)) 1).exists_isMinOn hs
      hFc.continuousOn
    have hu₀n : u₀ ≠ 0 := by
      intro h; rw [h] at hu₀; simp at hu₀
    refine ⟨F u₀, hFpos u₀ hu₀n, fun u => ?_⟩
    by_cases hu : u = 0
    · subst hu; simp [hF]
    · have hnorm : 0 < ‖u‖ := norm_pos_iff.2 hu
      have hmem : (‖u‖⁻¹ • u) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin K)) 1 := by
        simp [norm_smul, hnorm.ne']
      have h1 := hmin hmem
      have hscale : F (‖u‖⁻¹ • u) = ‖u‖⁻¹ ^ 2 * F u := by
        simp only [hF]
        simp [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      have h2 : F u₀ ≤ ‖u‖⁻¹ ^ 2 * F u := by rw [← hscale]; exact h1
      have h3 : F u₀ * ‖u‖ ^ 2 ≤ F u := by
        have := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖u‖)
        calc F u₀ * ‖u‖ ^ 2 = ‖u‖ ^ 2 * F u₀ := by ring
          _ ≤ ‖u‖ ^ 2 * (‖u‖⁻¹ ^ 2 * F u) := this
          _ = F u := by field_simp
      exact h3
  · refine ⟨1, one_pos, fun u => ?_⟩
    have : u = 0 := by
      by_contra hu
      exact hs ⟨‖u‖⁻¹ • u, by simp [norm_smul, norm_pos_iff.2 hu |>.ne']⟩
    subst this; simp [hF]


/-- Deterministic consistency: strong curvature near θ₀ and a small score at θ₀ force the
maximizers into the ball. -/
theorem det_consistency {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (θ₀ : EuclideanSpace ℝ (Fin K)) (q : ℕ) (ω : Ω) (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ)
    (hcurv : ∀ θ : EuclideanSpace ℝ (Fin K), ‖θ - θ₀‖ ≤ ρ → ∀ u : EuclideanSpace ℝ (Fin K),
      (q : ℝ) * c * ‖u‖ ^ 2 ≤
        ∑ m ∈ Finset.range q, inner ℝ (Matrix.toEuclideanLin (momentMatrix D θ m) u) u)
    (hscore : 2 * ‖scoreSum D Y q ω θ₀‖ < q * c * ρ) :
    (∃ θ, ∀ θ', logLik D Y q θ' ω ≤ logLik D Y q θ ω) ∧
    (∀ θhat, (∀ θ', logLik D Y q θ' ω ≤ logLik D Y q θhat ω) →
      ‖θhat - θ₀‖ < ρ ∧ scoreSum D Y q ω θhat = 0) := by
  have hqc : 0 < (q : ℝ) * c := by
    have : 0 < (q : ℝ) * c * ρ := lt_of_le_of_lt (by positivity) hscore
    exact (mul_pos_iff_of_pos_right hρ).mp this
  have hA : ∀ θ, ρ ≤ ‖θ - θ₀‖ → logLik D Y q θ ω < logLik D Y q θ₀ ω := by
    intro θ hθ
    set v := θ - θ₀ with hv
    have hvpos : 0 < ‖v‖ := lt_of_lt_of_le hρ hθ
    set u : EuclideanSpace ℝ (Fin K) := ‖v‖⁻¹ • v with hu
    have hun : ‖u‖ = 1 := by simp [hu, norm_smul, hvpos.ne']
    have key := descent_lemma (fun t => logLik D Y q (θ₀ + t • u) ω)
      (fun t => inner ℝ (scoreSum D Y q ω (θ₀ + t • u)) u)
      (fun t => - ∑ m ∈ Finset.range q, inner ℝ (Matrix.toEuclideanLin (momentMatrix D (θ₀ + t • u) m) u) u)
      ((q : ℝ) * c) ρ hqc hρ (fun t => hasDerivAt_ray D Y q ω θ₀ u t)
      (fun t => hasDerivAt_ray_deriv D Y q ω θ₀ u t)
      (fun t => by
        simp only [neg_nonpos]
        exact Finset.sum_nonneg fun m _ => inner_moment_nonneg D m _ u)
      (fun t ht => by
        have h1 : ‖(θ₀ + t • u) - θ₀‖ ≤ ρ := by
          simp [norm_smul, hun, abs_of_nonneg ht.1, ht.2]
        have := hcurv _ h1 u
        rw [hun] at this
        simp only [neg_le_neg_iff] at *
        linarith)
      (by
        simp only [zero_smul, add_zero]
        have h1 : inner ℝ (scoreSum D Y q ω θ₀) u ≤ ‖scoreSum D Y q ω θ₀‖ := by
          calc _ ≤ ‖scoreSum D Y q ω θ₀‖ * ‖u‖ := real_inner_le_norm _ _
            _ = _ := by rw [hun, mul_one]
        linarith)
    have := key ‖v‖ hθ
    have e : θ₀ + ‖v‖ • u = θ := by
      rw [hu, smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul, hv]; abel
    simp only [e, zero_smul, add_zero] at this
    exact this
  -- existence
  have hex : ∃ θ ∈ Metric.closedBall θ₀ ρ, IsMaxOn (fun θ' => logLik D Y q θ' ω)
      (Metric.closedBall θ₀ ρ) θ :=
    (isCompact_closedBall θ₀ ρ).exists_isMaxOn ⟨θ₀, Metric.mem_closedBall_self hρ.le⟩
      (continuous_logLik D Y q ω).continuousOn
  obtain ⟨θs, hθs, hmax⟩ := hex
  have hglob : ∀ θ', logLik D Y q θ' ω ≤ logLik D Y q θs ω := by
    intro θ'
    by_cases h : θ' ∈ Metric.closedBall θ₀ ρ
    · exact hmax h
    · have : ρ ≤ ‖θ' - θ₀‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm] at h; exact (not_le.1 h).le
      exact (hA θ' this).le.trans (hmax (Metric.mem_closedBall_self hρ.le))
  refine ⟨⟨θs, hglob⟩, fun θhat hθhat => ⟨?_, ?_⟩⟩
  · by_contra hcon
    have h1 := hA θhat (not_lt.1 hcon)
    have h2 : logLik D Y q θ₀ ω ≤ logLik D Y q θs ω := hmax (Metric.mem_closedBall_self hρ.le)
    have h3 := hθhat θs
    linarith
  · have hloc : IsLocalMax (fun θ' => logLik D Y q θ' ω) θhat :=
      Filter.Eventually.of_forall hθhat
    have h0 := hloc.hasFDerivAt_eq_zero (hasFDerivAt_logLik D Y q ω θhat)
    have : inner ℝ (scoreSum D Y q ω θhat) (scoreSum D Y q ω θhat) = 0 := by
      have := congrArg (fun L => L (scoreSum D Y q ω θhat)) h0
      simpa using this
    exact inner_self_eq_zero.1 this


/-- strong curvature near θ₀ from Axiom 7. -/
theorem curv_from_axiom7 (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) :
    ∃ c : ℝ, 0 < c ∧ ∃ r : ℝ, 0 < r ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ θ : EuclideanSpace ℝ (Fin K),
      ‖θ - θ₀‖ ≤ r → ∀ u : EuclideanSpace ℝ (Fin K), (q : ℝ) * c * ‖u‖ ^ 2 ≤
        ∑ m ∈ Finset.range q, inner ℝ (Matrix.toEuclideanLin (momentMatrix D θ m) u) u := by
  obtain ⟨c₀, hc₀, hQ⟩ := exists_posdef_const Ωlim h7.posDef
  set η : ℝ := c₀ / (2 * ((K : ℝ) ^ 2 + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨r, hr, q₀, hq₀⟩ := hessian_avg_uniform D Jstar M θ₀ Ωlim h7 η hη0
  refine ⟨c₀ / 2, by positivity, r, hr, max q₀ 1, fun q hq θ hθ u => ?_⟩
  have hq1 : 1 ≤ q := (le_max_right _ _).trans hq
  have hqq : q₀ ≤ q := (le_max_left _ _).trans hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hent := hq₀ q hqq θ hθ
  -- rewrite the sum
  have hsum : ∑ m ∈ Finset.range q, inner ℝ (Matrix.toEuclideanLin (momentMatrix D θ m) u) u =
      ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a *
        (((q : ℝ) * ((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ m) a b) * WithLp.ofLp u b) := by
    simp only [inner_toEuclideanLin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [avg_moment_entry, mul_inv_cancel_left₀ hqpos.ne', Finset.sum_mul, Finset.mul_sum]
  rw [hsum]
  set A := ((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ m) with hA
  have hdiff : ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a *
        (((q : ℝ) * A a b) * WithLp.ofLp u b) -
      (q : ℝ) * ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a * (Ωlim a b * WithLp.ofLp u b) =
      (q : ℝ) * ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a * ((A a b - Ωlim a b) * WithLp.ofLp u b) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hbound : |∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a *
      ((A a b - Ωlim a b) * WithLp.ofLp u b)| ≤ η * ((K : ℝ) ^ 2 * ‖u‖ ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a : Fin K, |∑ b : Fin K, WithLp.ofLp u a * ((A a b - Ωlim a b) * WithLp.ofLp u b)|
        ≤ ∑ a : Fin K, ∑ b : Fin K, η * ‖u‖ ^ 2 := by
          refine Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_mul, abs_mul]
          have h1 := abs_coord_le u a
          have h2 := abs_coord_le u b
          have h3 := hent a b
          calc |WithLp.ofLp u a| * (|A a b - Ωlim a b| * |WithLp.ofLp u b|)
              ≤ ‖u‖ * (η * ‖u‖) := by gcongr
            _ = η * ‖u‖ ^ 2 := by ring
      _ = η * ((K : ℝ) ^ 2 * ‖u‖ ^ 2) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hKη : η * ((K : ℝ) ^ 2 * ‖u‖ ^ 2) ≤ c₀ / 2 * ‖u‖ ^ 2 := by
    rw [hη]
    have hK0 : (0:ℝ) ≤ (K : ℝ) ^ 2 := by positivity
    have : (K : ℝ) ^ 2 / (2 * ((K : ℝ) ^ 2 + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc c₀ / (2 * ((K : ℝ) ^ 2 + 1)) * ((K : ℝ) ^ 2 * ‖u‖ ^ 2)
        = c₀ * ((K : ℝ) ^ 2 / (2 * ((K : ℝ) ^ 2 + 1))) * ‖u‖ ^ 2 := by field_simp
      _ ≤ c₀ * (1 / 2) * ‖u‖ ^ 2 := by gcongr
      _ = c₀ / 2 * ‖u‖ ^ 2 := by ring
  have hQu := hQ u
  have hlow := (abs_le.1 hbound).1
  have := mul_le_mul_of_nonneg_left (show -(c₀ / 2 * ‖u‖ ^ 2) ≤
      ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp u a * ((A a b - Ωlim a b) * WithLp.ofLp u b) by linarith)
    hqpos.le
  nlinarith [hdiff, hQu, this]


lemma wlln_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (B : ℝ) (hmeas : ∀ m, Measurable (X m)) (hind : iIndepFun X μ)
    (hB : ∀ m ω, |X m ω| ≤ B) (hmean : ∀ m, ∫ ω, X m ω ∂μ = 0) (ε : ℝ) (hε : 0 < ε)
    (q : ℕ) (hq : 1 ≤ q) :
    μ {ω | ε ≤ |(q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, X m ω|} ≤
      ENNReal.ofReal (B ^ 2 / (q * ε ^ 2)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hmem : ∀ m, MemLp (X m) 2 μ := fun m =>
    MemLp.of_bound (hmeas m).aestronglyMeasurable B (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hB m ω)
  have hSmem : MemLp (∑ m ∈ Finset.range q, X m) 2 μ := memLp_finsetSum' _ (fun m _ => hmem m)
  have hSmean : μ[∑ m ∈ Finset.range q, X m] = 0 := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun m _ => (hmem m).integrable (by norm_num))]
    simp [hmean]
  have hvar : variance (∑ m ∈ Finset.range q, X m) μ ≤ q * B ^ 2 := by
    rw [IndepFun.variance_sum (fun m _ => hmem m)
      (fun i _ j _ hij => hind.indepFun hij)]
    calc ∑ m ∈ Finset.range q, variance (X m) μ ≤ ∑ m ∈ Finset.range q, B ^ 2 := by
          refine Finset.sum_le_sum fun m _ => ?_
          have := variance_le_sq_of_bounded (μ := μ) (a := -B) (b := B) (X := X m)
            (Filter.Eventually.of_forall fun ω => abs_le.1 (hB m ω)) (hmeas m).aemeasurable
          calc variance (X m) μ ≤ ((B - -B) / 2) ^ 2 := this
            _ = B ^ 2 := by ring
      _ = q * B ^ 2 := by simp
  have hcheb := meas_ge_le_variance_div_sq hSmem (c := q * ε) (by positivity)
  have hset : {ω | ε ≤ |(q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, X m ω|} ⊆
      {ω | (q : ℝ) * ε ≤ |(∑ m ∈ Finset.range q, X m) ω - μ[∑ m ∈ Finset.range q, X m]|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hSmean, sub_zero, Finset.sum_apply]
    rw [abs_mul, abs_of_pos (inv_pos.2 hqpos)] at hω
    have := mul_le_mul_of_nonneg_left hω hqpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hqpos.ne', one_mul] at this
    exact this
  refine (measure_mono hset).trans (hcheb.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : variance (∑ m ∈ Finset.range q, X m) μ * (q * ε ^ 2) ≤ q * B ^ 2 * (q * ε ^ 2) :=
    mul_le_mul_of_nonneg_right hvar (by positivity)
  nlinarith [this]


lemma score_mean_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : SerialData K) (θ₀ : EuclideanSpace ℝ (Fin K)) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (m : ℕ) (a : Fin K) :
    ∫ ω, WithLp.ofLp (D.z m (Y m ω) - zbar D m θ₀) a ∂μ = 0 := by
  set f : Fin (D.J m) → ℝ := fun i => WithLp.ofLp (D.z m i - zbar D m θ₀) a with hf
  have h1 : ∫ ω, f (Y m ω) ∂μ = ∫ i, f i ∂(μ.map (Y m)) :=
    (integral_map (hY.measurable m).aemeasurable (measurable_of_finite f).aestronglyMeasurable).symm
  have hlaw : ∀ i, (μ.map (Y m)) {i} = ENNReal.ofReal (prob D m i θ₀) := fun i => by
    rw [Measure.map_apply (hY.measurable m) (measurableSet_singleton i)]
    exact hY.law m i
  haveI : IsProbabilityMeasure (μ.map (Y m)) := Measure.isProbabilityMeasure_map (hY.measurable m).aemeasurable
  show ∫ ω, f (Y m ω) ∂μ = 0
  rw [h1, integral_fintype (Integrable.of_finite)]
  have hlaw' : ∀ i, (μ.map (Y m)).real {i} = prob D m i θ₀ := fun i => by
    rw [measureReal_def, hlaw, ENNReal.toReal_ofReal (prob_nonneg' D m _ θ₀)]
  simp only [hlaw', smul_eq_mul]
  have := congrArg (fun v : EuclideanSpace ℝ (Fin K) => WithLp.ofLp v a) (sum_prob_sub_zbar D m θ₀)
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    WithLp.ofLp_zero, Pi.zero_apply] at this
  simpa [hf, mul_comm] using this


lemma norm_le_sum_abs (x : EuclideanSpace ℝ (Fin K)) : ‖x‖ ≤ ∑ a : Fin K, |WithLp.ofLp x a| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simp only [Real.norm_eq_abs, sq_abs]
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin K)))
    (f := fun a => |WithLp.ofLp x a|) (fun _ _ => abs_nonneg _)
  simpa [sq_abs] using this

/-- C4: weak law of large numbers for the scores at θ₀. -/
theorem score_avg_tendstoInMeasure_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) :
    TendstoInMeasure μ
      (fun (q : ℕ) (ω : Ω) => (q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set B : ℝ := 2 * M with hB
  have hbd : ∀ m (ω : Ω) (a : Fin K), |WithLp.ofLp (D.z m (Y m ω) - zbar D m θ₀) a| ≤ B := by
    intro m ω a
    refine (abs_coord_le _ a).trans ((norm_sub_le _ _).trans ?_)
    have := h7.bounded.norm_z_le m (Y m ω)
    have := norm_zbar_le D M (h7.bounded.norm_z_le m) θ₀
    linarith
  set ε' : ℝ := ε / ((K : ℝ) + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  set X : Fin K → ℕ → Ω → ℝ := fun a m ω => WithLp.ofLp (D.z m (Y m ω) - zbar D m θ₀) a with hX
  have hXmeas : ∀ a m, Measurable (X a m) := fun a m =>
    (measurable_of_finite (fun i : Fin (D.J m) => WithLp.ofLp (D.z m i - zbar D m θ₀) a)).comp
      (hY.measurable m)
  have hXind : ∀ a, iIndepFun (X a) μ := fun a =>
    hY.indep.comp (fun m (i : Fin (D.J m)) => WithLp.ofLp (D.z m i - zbar D m θ₀) a)
      (fun m => measurable_of_finite _)
  have hsub : ∀ (q : ℕ),
      {ω | ε ≤ ‖(q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀)‖} ⊆
      ⋃ a : Fin K, {ω | ε' ≤ |(q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, X a m ω|} := by
    intro q ω hω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hω ⊢
    by_contra hcon
    push_neg at hcon
    have h1 := norm_le_sum_abs ((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀))
    have h2 : ∑ a : Fin K, |WithLp.ofLp ((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q,
        (D.z m (Y m ω) - zbar D m θ₀)) a| ≤ ∑ a : Fin K, ε' := by
      refine Finset.sum_le_sum fun a _ => ?_
      have := hcon a
      simp only [hX, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
        Finset.sum_apply] at this ⊢
      exact this.le
    have h3 : ∑ a : Fin K, ε' = K * ε' := by simp
    have h4 : (K : ℝ) * ε' < ε := by
      rw [hε']
      have : (K : ℝ) * (ε / ((K : ℝ) + 1)) = ε - ε / ((K : ℝ) + 1) := by field_simp; ring
      rw [this]
      have : 0 < ε / ((K : ℝ) + 1) := by positivity
      linarith
    linarith
  have hbound : ∀ q : ℕ, 1 ≤ q → μ {ω | ε ≤ ‖(q : ℝ)⁻¹ • ∑ m ∈ Finset.range q,
      (D.z m (Y m ω) - zbar D m θ₀)‖} ≤ K * ENNReal.ofReal (B ^ 2 / (q * ε' ^ 2)) := by
    intro q hq
    refine (measure_mono (hsub q)).trans ((measure_iUnion_fintype_le _ _).trans ?_)
    calc ∑ a : Fin K, μ {ω | ε' ≤ |(q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, X a m ω|}
        ≤ ∑ a : Fin K, ENNReal.ofReal (B ^ 2 / (q * ε' ^ 2)) :=
          Finset.sum_le_sum fun a _ =>
            wlln_bounded μ (X a) B (hXmeas a) (hXind a) (fun m ω => hbd m ω a)
              (fun m => score_mean_zero μ D θ₀ Y hY m a) ε' hε'0 q hq
      _ = K * ENNReal.ofReal (B ^ 2 / (q * ε' ^ 2)) := by simp
  have hlim : Tendsto (fun q : ℕ => (K : ENNReal) * ENNReal.ofReal (B ^ 2 / (q * ε' ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun q : ℕ => B ^ 2 / (q * ε' ^ 2)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (B ^ 2 / ε' ^ 2))
      refine this.congr fun q => ?_
      by_cases hq : (q : ℝ) = 0
      · simp [hq]
      · field_simp
    have h2 := (ENNReal.tendsto_ofReal h1)
    simp only [ENNReal.ofReal_zero] at h2
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.natCast_ne_top K))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun q => bot_le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with q hq
  simpa only [sub_zero] using hbound q hq


/-- **mle_consistent** (sibling 3af1eeff), proved from the pieces above. -/
theorem mle_consistent_aux {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hθ : IsMLE D Y θhat) :
    TendstoInMeasure μ θhat atTop (fun _ => θ₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  obtain ⟨c, hc, r, hr, q₀, hq₀⟩ := curv_from_axiom7 D Jstar M θ₀ Ωlim h7
  set ρ : ℝ := min ε r with hρ
  have hρ0 : 0 < ρ := lt_min hε hr
  have hC4 := score_avg_tendstoInMeasure_zero μ D Jstar M θ₀ Ωlim h7 Y hY
  rw [tendstoInMeasure_iff_norm] at hC4
  have hC4' := hC4 (c * ρ / 2) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC4'
    (Filter.Eventually.of_forall fun q => bot_le) ?_
  filter_upwards [Filter.eventually_ge_atTop (max q₀ 1)] with q hq
  have hq1 : 1 ≤ q := (le_max_right _ _).trans hq
  have hqq : q₀ ≤ q := (le_max_left _ _).trans hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_setOf_eq, sub_zero] at hω ⊢
  by_contra hcon
  push_neg at hcon
  -- hcon : ‖q⁻¹ • S‖ < c ρ / 2
  have hS : 2 * ‖scoreSum D Y q ω θ₀‖ < q * c * ρ := by
    have h1 : ‖(q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀)‖ =
        (q : ℝ)⁻¹ * ‖scoreSum D Y q ω θ₀‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hqpos.le)]; rfl
    rw [h1] at hcon
    have := mul_lt_mul_of_pos_left hcon hqpos
    rw [← mul_assoc, mul_inv_cancel₀ hqpos.ne', one_mul] at this
    nlinarith
  obtain ⟨hex, hcrit⟩ := det_consistency D Y θ₀ q ω c ρ hc hρ0
    (fun θ hθρ u => hq₀ q hqq θ (hθρ.trans (min_le_right _ _)) u) hS
  have hmax := hθ.isMax q ω hex
  have := (hcrit (θhat q ω) hmax).1
  have h2 : ‖θhat q ω - θ₀‖ < ε := this.trans_le (min_le_left _ _)
  exact absurd hω (not_le.2 h2)


/-! ## Glue (C6): asymptotic normality from consistency and the score CLT -/

open scoped MatrixOrder in
lemma sqrt_facts (Ωlim : Matrix (Fin K) (Fin K) ℝ) (hP : Ωlim.PosDef) :
    (∀ x, invSqrtMap Ωlim (sqrtMap Ωlim x) = x) ∧
    (∀ x, invSqrtMap Ωlim (Matrix.toEuclideanLin Ωlim x) = sqrtMap Ωlim x) := by
  have h0 : (0 : Matrix (Fin K) (Fin K) ℝ) ≤ Ωlim := hP.posSemidef.nonneg
  have hsq : CFC.sqrt Ωlim * CFC.sqrt Ωlim = Ωlim := CFC.sqrt_mul_sqrt_self Ωlim h0
  have hdet : IsUnit (CFC.sqrt Ωlim).det := by
    rw [isUnit_iff_ne_zero]
    intro h
    have := congrArg Matrix.det hsq
    rw [Matrix.det_mul, h, zero_mul] at this
    exact hP.det_pos.ne' this.symm
  have hinv : (CFC.sqrt Ωlim)⁻¹ * CFC.sqrt Ωlim = 1 := Matrix.nonsing_inv_mul _ hdet
  refine ⟨fun x => ?_, fun x => ?_⟩
  · simp only [sqrtMap, invSqrtMap, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, WithLp.toLp_ofLp]
  · have : (CFC.sqrt Ωlim)⁻¹ * Ωlim = CFC.sqrt Ωlim := by
      calc (CFC.sqrt Ωlim)⁻¹ * Ωlim = (CFC.sqrt Ωlim)⁻¹ * (CFC.sqrt Ωlim * CFC.sqrt Ωlim) := by
            rw [hsq]
        _ = CFC.sqrt Ωlim := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    simp only [sqrtMap, invSqrtMap, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, this]

lemma matrix_entry_bound (E : Matrix (Fin K) (Fin K) ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ a b, |E a b| ≤ η) (x : EuclideanSpace ℝ (Fin K)) :
    ‖Matrix.toEuclideanLin E x‖ ≤ (K : ℝ) ^ 2 * η * ‖x‖ := by
  refine (norm_le_sum_abs _).trans ?_
  have h1 : ∀ a : Fin K, |WithLp.ofLp (Matrix.toEuclideanLin E x) a| ≤ (K : ℝ) * η * ‖x‖ := by
    intro a
    rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b : Fin K, |E a b * WithLp.ofLp x b| ≤ ∑ b : Fin K, η * ‖x‖ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hE a b) (abs_coord_le x b) (abs_nonneg _) hη
      _ = (K : ℝ) * η * ‖x‖ := by simp; ring
  calc ∑ a : Fin K, |WithLp.ofLp (Matrix.toEuclideanLin E x) a| ≤ ∑ a : Fin K, (K : ℝ) * η * ‖x‖ :=
        Finset.sum_le_sum fun a _ => h1 a
    _ = (K : ℝ) ^ 2 * η * ‖x‖ := by simp; ring

/-- The pure linear-algebra step of the glue. -/
lemma glue_linalg (Ωlim A : Matrix (Fin K) (Fin K) ℝ)
    (Pm Pinv : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ (Fin K))
    (hPP : ∀ x, Pinv (Pm x) = x) (hPΩ : ∀ x, Pinv (Matrix.toEuclideanLin Ωlim x) = Pm x)
    (CP η : ℝ) (hCP0 : 0 ≤ CP) (hCP : ∀ x, ‖Pinv x‖ ≤ CP * ‖x‖) (hη : 0 ≤ η)
    (hA : ∀ a b, |A a b - Ωlim a b| ≤ η) (hκ : CP ^ 2 * (K : ℝ) ^ 2 * η ≤ 1 / 2)
    (q : ℝ) (hq : 0 < q) (s v : EuclideanSpace ℝ (Fin K))
    (hs : s = q • Matrix.toEuclideanLin A v) :
    ‖Real.sqrt q • Pm v - (Real.sqrt q)⁻¹ • Pinv s‖ ≤
      2 * CP ^ 3 * (K : ℝ) ^ 2 * η * ((Real.sqrt q)⁻¹ * ‖s‖) := by
  set r := Real.sqrt q with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hq
  have hrr : r * r = q := Real.mul_self_sqrt hq.le
  set E := Ωlim - A with hE
  have hEb : ∀ a b, |E a b| ≤ η := fun a b => by
    rw [hE, Matrix.sub_apply, abs_sub_comm]; exact hA a b
  set Yv := r • Pm v with hYv
  set T := r⁻¹ • Pinv s with hT
  have hAv : Matrix.toEuclideanLin A v =
      Matrix.toEuclideanLin Ωlim v - Matrix.toEuclideanLin E v := by
    rw [hE, map_sub, LinearMap.sub_apply]; abel
  have hdiff : Yv - T = Pinv (Matrix.toEuclideanLin E (Pinv Yv)) := by
    have h1 : Pinv Yv = r • v := by rw [hYv, map_smul, hPP]
    rw [h1, map_smul, map_smul, hT, hs, map_smul, hAv, map_sub, hPΩ, hYv]
    rw [smul_smul, smul_sub, ← hrr, inv_mul_cancel_left₀ hr0.ne']
    abel
  have hb : ‖Yv - T‖ ≤ CP ^ 2 * (K : ℝ) ^ 2 * η * ‖Yv‖ := by
    rw [hdiff]
    refine (hCP _).trans ?_
    calc CP * ‖Matrix.toEuclideanLin E (Pinv Yv)‖ ≤ CP * ((K : ℝ) ^ 2 * η * ‖Pinv Yv‖) :=
          mul_le_mul_of_nonneg_left (matrix_entry_bound E η hη hEb _) hCP0
      _ ≤ CP * ((K : ℝ) ^ 2 * η * (CP * ‖Yv‖)) := by
          gcongr
          exact hCP _
      _ = CP ^ 2 * (K : ℝ) ^ 2 * η * ‖Yv‖ := by ring
  have hTn : ‖T‖ ≤ CP * (r⁻¹ * ‖s‖) := by
    rw [hT, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le)]
    calc r⁻¹ * ‖Pinv s‖ ≤ r⁻¹ * (CP * ‖s‖) := mul_le_mul_of_nonneg_left (hCP s) (by positivity)
      _ = _ := by ring
  have hY2 : ‖Yv‖ ≤ 2 * ‖T‖ := by
    have : ‖Yv‖ ≤ ‖Yv - T‖ + ‖T‖ := by
      have := norm_add_le (Yv - T) T; simpa using this
    nlinarith [norm_nonneg Yv]
  calc ‖Yv - T‖ ≤ CP ^ 2 * (K : ℝ) ^ 2 * η * ‖Yv‖ := hb
    _ ≤ CP ^ 2 * (K : ℝ) ^ 2 * η * (2 * (CP * (r⁻¹ * ‖s‖))) := by
        gcongr
        exact hY2.trans (by linarith)
    _ = _ := by ring

/-- On the event that `θh` is a critical point within `ρ` of `θ₀`, the score at `θ₀` is
`q • A (θh - θ₀)` for a matrix `A` entrywise within `η` of `Ωlim` (mean value theorem per row). -/
lemma exists_hessian_rows {Ω : Type*} (D : SerialData K) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (θ₀ θh : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ) (q : ℕ) (ω : Ω)
    (hq : 0 < q) (η ρ : ℝ)
    (hH : ∀ θ : EuclideanSpace ℝ (Fin K), ‖θ - θ₀‖ ≤ ρ → ∀ a b : Fin K,
        |((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ m) a b - Ωlim a b| ≤ η)
    (hθh : ‖θh - θ₀‖ ≤ ρ) (hcrit : scoreSum D Y q ω θh = 0) :
    ∃ A : Matrix (Fin K) (Fin K) ℝ, (∀ a b, |A a b - Ωlim a b| ≤ η) ∧
      scoreSum D Y q ω θ₀ = (q : ℝ) • Matrix.toEuclideanLin A (θh - θ₀) := by
  have hlin := fun a => score_linearization_coord D Y θ₀ θh q ω a
  choose t ht heq using hlin
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨Matrix.of fun a b => ((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q,
      momentMatrix D (θ₀ + t a • (θh - θ₀)) m) a b, ?_, ?_⟩
  · intro a b
    simp only [Matrix.of_apply]
    apply hH
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (ht a).1]
    calc t a * ‖θh - θ₀‖ ≤ 1 * ‖θh - θ₀‖ := mul_le_mul_of_nonneg_right (ht a).2 (norm_nonneg _)
      _ ≤ ρ := by rw [one_mul]; exact hθh
  · have h0 : ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θh) = 0 := hcrit
    ext a
    have h1 := heq a
    rw [h0, sub_zero] at h1
    show WithLp.ofLp (∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀)) a = _
    rw [h1]
    simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, avg_moment_entry]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp

/-- Tightness of `q^{-1/2} ‖S_q(θ₀)‖` (Chebyshev, coordinatewise). -/
lemma score_tight {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : SerialData K) (Jstar : ℕ) (M : ℝ) (θ₀ : EuclideanSpace ℝ (Fin K))
    (Ωlim : Matrix (Fin K) (Fin K) ℝ) (h7 : Axiom7 D Jstar M θ₀ Ωlim)
    (Y : (m : ℕ) → Ω → Fin (D.J m)) (hY : IsLogitSample μ D θ₀ Y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ q : ℕ, 1 ≤ q →
      μ {ω | R ≤ (Real.sqrt q)⁻¹ * ‖scoreSum D Y q ω θ₀‖} ≤ ENNReal.ofReal δ := by
  set B : ℝ := 2 * M with hB
  have hbd : ∀ m (ω : Ω) (a : Fin K), |WithLp.ofLp (D.z m (Y m ω) - zbar D m θ₀) a| ≤ B := by
    intro m ω a
    refine (abs_coord_le _ a).trans ((norm_sub_le _ _).trans ?_)
    have := h7.bounded.norm_z_le m (Y m ω)
    have := norm_zbar_le D M (h7.bounded.norm_z_le m) θ₀
    linarith
  set X : Fin K → ℕ → Ω → ℝ := fun a m ω => WithLp.ofLp (D.z m (Y m ω) - zbar D m θ₀) a with hX
  have hXmeas : ∀ a m, Measurable (X a m) := fun a m =>
    (measurable_of_finite (fun i : Fin (D.J m) => WithLp.ofLp (D.z m i - zbar D m θ₀) a)).comp
      (hY.measurable m)
  have hXind : ∀ a, iIndepFun (X a) μ := fun a =>
    hY.indep.comp (fun m (i : Fin (D.J m)) => WithLp.ofLp (D.z m i - zbar D m θ₀) a)
      (fun m => measurable_of_finite _)
  set C : ℝ := (K : ℝ) * B ^ 2 * ((K : ℝ) + 1) ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  set R : ℝ := Real.sqrt (C / δ) + 1 with hR
  have hR0 : 0 < R := by positivity
  have hRsq : C / δ ≤ R ^ 2 := by
    have h1 : Real.sqrt (C / δ) ^ 2 = C / δ := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (C / δ)]
  refine ⟨R, hR0, fun q hq => ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  set ε' : ℝ := R / (((K : ℝ) + 1) * Real.sqrt q) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hsub : {ω | R ≤ (Real.sqrt q)⁻¹ * ‖scoreSum D Y q ω θ₀‖} ⊆
      ⋃ a : Fin K, {ω | ε' ≤ |(q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, X a m ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hω ⊢
    by_contra hcon
    push_neg at hcon
    have hcoord : ∀ a, |WithLp.ofLp (scoreSum D Y q ω θ₀) a| ≤ q * ε' := by
      intro a
      have := (hcon a).le
      have e : WithLp.ofLp (scoreSum D Y q ω θ₀) a = ∑ m ∈ Finset.range q, X a m ω := by
        simp [scoreSum, hX, WithLp.ofLp_sum, Finset.sum_apply]
      rw [e]
      rw [abs_mul, abs_of_pos (inv_pos.2 hqpos)] at this
      rwa [inv_mul_le_iff₀ hqpos] at this
    have h1 := norm_le_sum_abs (scoreSum D Y q ω θ₀)
    have h2 : ∑ a : Fin K, |WithLp.ofLp (scoreSum D Y q ω θ₀) a| ≤ K * (q * ε') := by
      calc _ ≤ ∑ a : Fin K, ((q : ℝ) * ε') := Finset.sum_le_sum fun a _ => hcoord a
        _ = _ := by simp
    have h3 : (K : ℝ) * (q * ε') < R * Real.sqrt q := by
      have key : ∀ s : ℝ, 0 < s → (K : ℝ) * (s ^ 2 * (R / (((K : ℝ) + 1) * s))) =
          (K : ℝ) / ((K : ℝ) + 1) * (R * s) := by
        intro s hs; field_simp
      have e2 : (K : ℝ) * (q * ε') = (K : ℝ) / ((K : ℝ) + 1) * (R * Real.sqrt q) := by
        have := key (Real.sqrt q) hsq
        rw [Real.sq_sqrt hqpos.le] at this
        rw [hε']; exact this
      rw [e2]
      have : (K : ℝ) / ((K : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      have hRq : 0 < R * Real.sqrt q := by positivity
      nlinarith
    have h4 : (Real.sqrt q)⁻¹ * ‖scoreSum D Y q ω θ₀‖ < R := by
      rw [inv_mul_lt_iff₀ hsq]; linarith
    linarith
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  have hper : ∀ a : Fin K, μ {ω | ε' ≤ |(q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, X a m ω|} ≤
      ENNReal.ofReal (B ^ 2 * ((K : ℝ) + 1) ^ 2 / R ^ 2) := by
    intro a
    refine (wlln_bounded μ (X a) B (hXmeas a) (hXind a) (fun m ω => hbd m ω a)
      (fun m => score_mean_zero μ D θ₀ Y hY m a) ε' hε'0 q hq).trans (le_of_eq ?_)
    congr 1
    have key : ∀ s : ℝ, 0 < s → B ^ 2 / (s ^ 2 * (R / (((K : ℝ) + 1) * s)) ^ 2) =
        B ^ 2 * ((K : ℝ) + 1) ^ 2 / R ^ 2 := by
      intro s hs; field_simp
    have := key (Real.sqrt q) hsq
    rw [Real.sq_sqrt hqpos.le] at this
    rw [hε']; exact this
  calc _ ≤ ∑ a : Fin K, ENNReal.ofReal (B ^ 2 * ((K : ℝ) + 1) ^ 2 / R ^ 2) :=
        Finset.sum_le_sum fun a _ => hper a
    _ = ENNReal.ofReal (C / R ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; rw [hC]; ring
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hδ] at hRsq
        linarith [hRsq]

/-- C6 (glue): asymptotic normality of the MLE from consistency and the score CLT. -/
theorem asymptotic_normal_of_score_clt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hθ : IsMLE D Y θhat)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (Z : Ω' → EuclideanSpace ℝ (Fin K))
    (hclt : TendstoInDistribution
      (fun (q : ℕ) (ω : Ω) => (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q,
        invSqrtMap Ωlim (gradient (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀))
      atTop Z (fun _ => μ) μ') :
    TendstoInDistribution
      (fun (q : ℕ) (ω : Ω) => Real.sqrt q • sqrtMap Ωlim (θhat q ω - θ₀))
      atTop Z (fun _ => μ) μ' := by
  obtain ⟨hPP, hPΩ⟩ := sqrt_facts Ωlim h7.posDef
  set Pinv := invSqrtMap Ωlim with hPinv
  set CP : ℝ := ‖LinearMap.toContinuousLinearMap Pinv‖ with hCPdef
  have hCP0 : 0 ≤ CP := norm_nonneg _
  have hCP : ∀ x, ‖Pinv x‖ ≤ CP * ‖x‖ := fun x =>
    (LinearMap.toContinuousLinearMap Pinv).le_opNorm x
  set T := (fun (q : ℕ) (ω : Ω) => (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q,
        invSqrtMap Ωlim (gradient (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀)) with hTdef
  have hTeq : ∀ (q : ℕ) (ω : Ω), T q ω = (Real.sqrt q)⁻¹ • Pinv (scoreSum D Y q ω θ₀) := by
    intro q ω
    simp only [hTdef, scoreSum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(hasGradientAt_logProb D m (Y m ω) θ₀).gradient]
  set Yq := fun (q : ℕ) (ω : Ω) => Real.sqrt q • sqrtMap Ωlim (θhat q ω - θ₀) with hYq
  have hmeas : ∀ q, AEMeasurable (Yq q) μ := by
    intro q
    have hc : Continuous (sqrtMap Ωlim) := LinearMap.continuous_of_finiteDimensional _
    have h1 : Measurable (fun ω => sqrtMap Ωlim (θhat q ω - θ₀)) :=
      hc.measurable.comp ((hθ.measurable q).sub measurable_const)
    exact (h1.const_smul (Real.sqrt q)).aemeasurable
  refine tendstoInDistribution_of_tendstoInMeasure_sub Yq Z hclt ?_ hmeas
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨δ1, -, hδ1pos, hδ1⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hδ10 : 0 < δ1 := ENNReal.ofReal_pos.1 hδ1pos
  obtain ⟨R, hR, htight⟩ := score_tight μ D Jstar M θ₀ Ωlim h7 Y hY (δ1 / 2) (by positivity)
  obtain ⟨c, hc, r0, hr0, q₁, hcurv⟩ := curv_from_axiom7 D Jstar M θ₀ Ωlim h7
  set κ0 : ℝ := CP ^ 2 * (K : ℝ) ^ 2 with hκ0
  set κ1 : ℝ := 2 * CP ^ 3 * (K : ℝ) ^ 2 with hκ1
  have hκ00 : 0 ≤ κ0 := by positivity
  have hκ10 : 0 ≤ κ1 := by positivity
  set η : ℝ := min (1 / (2 * (κ0 + 1))) (ε / (2 * (κ1 + 1) * R)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hκ : CP ^ 2 * (K : ℝ) ^ 2 * η ≤ 1 / 2 := by
    have h1 : η ≤ 1 / (2 * (κ0 + 1)) := min_le_left _ _
    have h2 : κ0 * η ≤ κ0 * (1 / (2 * (κ0 + 1))) := mul_le_mul_of_nonneg_left h1 hκ00
    have h3 : κ0 * (1 / (2 * (κ0 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    linarith
  have hκR : κ1 * η * R < ε := by
    have h1 : η ≤ ε / (2 * (κ1 + 1) * R) := min_le_right _ _
    have h2 : κ1 * η * R ≤ κ1 * (ε / (2 * (κ1 + 1) * R)) * R := by
      apply mul_le_mul_of_nonneg_right _ hR.le
      exact mul_le_mul_of_nonneg_left h1 hκ10
    have h3 : κ1 * (ε / (2 * (κ1 + 1) * R)) * R = ε * (κ1 / (2 * (κ1 + 1))) := by
      field_simp
    have h4 : κ1 / (2 * (κ1 + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have h5 : ε * (κ1 / (2 * (κ1 + 1))) < ε := by
      calc ε * (κ1 / (2 * (κ1 + 1))) < ε * 1 := mul_lt_mul_of_pos_left h4 hε
        _ = ε := mul_one ε
    linarith
  obtain ⟨r1, hr1, q₂, hH⟩ := hessian_avg_uniform D Jstar M θ₀ Ωlim h7 η hη0
  set ρ : ℝ := min r0 r1 with hρ
  have hρ0 : 0 < ρ := lt_min hr0 hr1
  have hC4 := (tendstoInMeasure_iff_norm.1
    (score_avg_tendstoInMeasure_zero μ D Jstar M θ₀ Ωlim h7 Y hY)) (c * ρ / 2) (by positivity)
  have hev := (ENNReal.tendsto_nhds_zero.1 hC4) (ENNReal.ofReal (δ1 / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  filter_upwards [hev, Filter.eventually_ge_atTop (max (max q₁ q₂) 1)] with q hq1 hq
  have hqa : q₁ ≤ q := ((le_max_left _ _).trans (le_max_left _ _)).trans hq
  have hqb : q₂ ≤ q := ((le_max_right _ _).trans (le_max_left _ _)).trans hq
  have hq1' : 1 ≤ q := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1'
  have hsub : {ω | ε ≤ ‖(Yq - T) q ω - (0 : ℕ → Ω → EuclideanSpace ℝ (Fin K)) q ω‖} ⊆
      {ω | c * ρ / 2 ≤ ‖(q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀) - 0‖} ∪
      {ω | R ≤ (Real.sqrt q)⁻¹ * ‖scoreSum D Y q ω θ₀‖} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨hA, hB⟩ := hcon
    have hS : 2 * ‖scoreSum D Y q ω θ₀‖ < q * c * ρ := by
      have h1 : ‖(q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, (D.z m (Y m ω) - zbar D m θ₀)‖ =
          (q : ℝ)⁻¹ * ‖scoreSum D Y q ω θ₀‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hqpos.le)]; rfl
      rw [h1] at hA
      have := mul_lt_mul_of_pos_left hA hqpos
      rw [← mul_assoc, mul_inv_cancel₀ hqpos.ne', one_mul] at this
      nlinarith
    obtain ⟨hex, hcrit⟩ := det_consistency D Y θ₀ q ω c ρ hc hρ0
      (fun θ hθρ u => hcurv q hqa θ (hθρ.trans (min_le_left _ _)) u) hS
    obtain ⟨hlt, hzero⟩ := hcrit (θhat q ω) (hθ.isMax q ω hex)
    obtain ⟨A, hAb, hAs⟩ := exists_hessian_rows D Y θ₀ (θhat q ω) Ωlim q ω (by omega) η ρ
      (fun θ hθ' a b => hH q hqb θ (hθ'.trans (min_le_right _ _)) a b) hlt.le hzero
    have hg := glue_linalg Ωlim A (sqrtMap Ωlim) Pinv hPP hPΩ CP η hCP0 hCP hη0.le hAb hκ
      q hqpos _ _ hAs
    have hω' : ε ≤ ‖Real.sqrt q • sqrtMap Ωlim (θhat q ω - θ₀) -
        (Real.sqrt q)⁻¹ • Pinv (scoreSum D Y q ω θ₀)‖ := by
      rw [← hTeq]; exact hω
    have hm : κ1 * η * ((Real.sqrt q)⁻¹ * ‖scoreSum D Y q ω θ₀‖) ≤ κ1 * η * R :=
      mul_le_mul_of_nonneg_left hB.le (by positivity)
    have : 2 * CP ^ 3 * (K : ℝ) ^ 2 * η = κ1 * η := by rw [hκ1]
    linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ1 / 2) + ENNReal.ofReal (δ1 / 2) := add_le_add hq1 (htight q hq1')
    _ = ENNReal.ofReal δ1 := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ δ := hδ1.le

/-! ## Score CLT (sibling b3d348fc) via characteristic functions -/

open scoped MatrixOrder in
lemma sqrt_facts2 (Ωlim : Matrix (Fin K) (Fin K) ℝ) (hP : Ωlim.PosDef) :
    (∀ x, sqrtMap Ωlim (invSqrtMap Ωlim x) = x) ∧
    (∀ x y, inner ℝ (invSqrtMap Ωlim x) y = inner ℝ x (invSqrtMap Ωlim y)) := by
  have h0 : (0 : Matrix (Fin K) (Fin K) ℝ) ≤ Ωlim := hP.posSemidef.nonneg
  have hsq : CFC.sqrt Ωlim * CFC.sqrt Ωlim = Ωlim := CFC.sqrt_mul_sqrt_self Ωlim h0
  have hdet : IsUnit (CFC.sqrt Ωlim).det := by
    rw [isUnit_iff_ne_zero]
    intro h
    have := congrArg Matrix.det hsq
    rw [Matrix.det_mul, h, zero_mul] at this
    exact hP.det_pos.ne' this.symm
  have hinv : CFC.sqrt Ωlim * (CFC.sqrt Ωlim)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hherm : ((CFC.sqrt Ωlim)⁻¹).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Ωlim)).isHermitian.inv
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · simp only [sqrtMap, invSqrtMap, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, WithLp.toLp_ofLp]
  · exact (Matrix.isSymmetric_toEuclideanLin_iff.2 hherm) x y

lemma prod_sub_prod_le (q : ℕ) (a b : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) :
    ‖∏ m ∈ Finset.range q, a m - ∏ m ∈ Finset.range q, b m‖ ≤
      ∑ m ∈ Finset.range q, ‖a m - b m‖ := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    have hB : ‖∏ m ∈ Finset.range n, b m‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun m _ => norm_nonneg _) (fun m _ => hb m)
    have e : (∏ m ∈ Finset.range n, a m) * a n - (∏ m ∈ Finset.range n, b m) * b n =
        (∏ m ∈ Finset.range n, a m - ∏ m ∈ Finset.range n, b m) * a n +
          (∏ m ∈ Finset.range n, b m) * (a n - b n) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖∏ m ∈ Finset.range n, a m - ∏ m ∈ Finset.range n, b m‖ * ‖a n‖ ≤
        ‖∏ m ∈ Finset.range n, a m - ∏ m ∈ Finset.range n, b m‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (ha n)
    have h2 : ‖∏ m ∈ Finset.range n, b m‖ * ‖a n - b n‖ ≤ ‖a n - b n‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hB
    linarith

lemma exp_I_bound (y : ℝ) (hy : |y| ≤ 1) :
    ‖Complex.exp ((y : ℂ) * Complex.I) - (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      |y| ^ 3 := by
  have e2 : ‖(y : ℂ) * Complex.I‖ = |y| := by simp [Complex.norm_real]
  have hx : ‖(y : ℂ) * Complex.I‖ ≤ 1 := by rw [e2]; exact hy
  have h := Complex.exp_bound hx (n := 3) (by norm_num)
  have e1 : ∑ m ∈ Finset.range 3, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one, div_one]
    push_cast
    linear_combination ((y : ℂ) ^ 2 / 2) * Complex.I_sq
  rw [e1, e2] at h
  refine h.trans ?_
  have h3 : (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℝ) * ((3 : ℕ) : ℝ))⁻¹) ≤ 1 := by
    norm_num [Nat.factorial]
  calc |y| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℝ) * ((3 : ℕ) : ℝ))⁻¹)
      ≤ |y| ^ 3 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = |y| ^ 3 := mul_one _

lemma factor_norm_le {ι : Type*} [Fintype ι] (p y : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    ‖∑ i, (p i : ℂ) * Complex.exp ((y i : ℂ) * Complex.I)‖ ≤ 1 := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  calc ∑ i, ‖(p i : ℂ) * Complex.exp ((y i : ℂ) * Complex.I)‖ = ∑ i, p i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (hp i)]
    _ = 1 := hsum

lemma factor_bound {ι : Type*} [Fintype ι] (p x : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hmean : ∑ i, p i * x i = 0) (b h : ℝ) (hb : ∀ i, |x i| ≤ b)
    (h0 : 0 ≤ h) (hbh : b * h ≤ 1) :
    ‖∑ i, (p i : ℂ) * Complex.exp (((h * x i : ℝ) : ℂ) * Complex.I) -
      ((1 - h ^ 2 * (∑ i, p i * x i ^ 2) / 2 : ℝ) : ℂ)‖ ≤ (b * h) ^ 3 := by
  have key : ((1 - h ^ 2 * (∑ i, p i * x i ^ 2) / 2 : ℝ) : ℂ) =
      ∑ i, (p i : ℂ) * (((1 - (h * x i) ^ 2 / 2 : ℝ) : ℂ) + ((h * x i : ℝ) : ℂ) * Complex.I) := by
    have e1 : ∑ i, (p i : ℂ) * (((1 - (h * x i) ^ 2 / 2 : ℝ) : ℂ) + ((h * x i : ℝ) : ℂ) * Complex.I) =
        ((∑ i, p i * (1 - (h * x i) ^ 2 / 2) : ℝ) : ℂ) +
          ((h * ∑ i, p i * x i : ℝ) : ℂ) * Complex.I := by
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e1, hmean, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    have : ∑ i, p i * (1 - (h * x i) ^ 2 / 2) = ∑ i, p i - h ^ 2 * (∑ i, p i * x i ^ 2) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, hsum]
  rw [key, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(p i : ℂ) * Complex.exp (((h * x i : ℝ) : ℂ) * Complex.I) -
        (p i : ℂ) * (((1 - (h * x i) ^ 2 / 2 : ℝ) : ℂ) + ((h * x i : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ i, p i * (b * h) ^ 3 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp i)]
        refine mul_le_mul_of_nonneg_left ?_ (hp i)
        have hyi : |h * x i| ≤ b * h := by
          rw [abs_mul, abs_of_nonneg h0, mul_comm]
          exact mul_le_mul_of_nonneg_right (hb i) h0
        refine (exp_I_bound (h * x i) (hyi.trans hbh)).trans ?_
        exact pow_le_pow_left₀ (abs_nonneg _) hyi 3
    _ = (b * h) ^ 3 := by rw [← Finset.sum_mul, hsum, one_mul]

lemma prod_tendsto_exp (a : ℕ → ℕ → ℂ) (σ2 : ℕ → ℝ) (B C v : ℝ) (q₀ : ℕ)
    (hσ0 : ∀ m, 0 ≤ σ2 m) (hσB : ∀ m, σ2 m ≤ B)
    (havg : Tendsto (fun q : ℕ => (q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, σ2 m) atTop (𝓝 v))
    (ha1 : ∀ q m, ‖a q m‖ ≤ 1)
    (hab : ∀ q ≥ q₀, ∀ m, ‖a q m - ((1 - σ2 m / (2 * q) : ℝ) : ℂ)‖ ≤ C / (q * Real.sqrt q)) :
    Tendsto (fun q : ℕ => ∏ m ∈ Finset.range q, a q m) atTop
      (𝓝 ((Real.exp (-(v / 2)) : ℝ) : ℂ)) := by
  set e : ℕ → ℝ := fun q => Real.exp (-(((q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, σ2 m) / 2)) with he
  have he_lim : Tendsto (fun q => ((e q : ℝ) : ℂ)) atTop (𝓝 ((Real.exp (-(v / 2)) : ℝ) : ℂ)) := by
    have : Tendsto e atTop (𝓝 (Real.exp (-(v / 2)))) :=
      (Real.continuous_exp.tendsto _).comp ((havg.div_const 2).neg)
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hprod_e : ∀ q : ℕ, 0 < q → ((e q : ℝ) : ℂ) =
      ∏ m ∈ Finset.range q, ((Real.exp (-(σ2 m / (2 * q))) : ℝ) : ℂ) := by
    intro q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 1
    simp only [he]
    congr 1
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  have hbound : ∀ᶠ q : ℕ in atTop, ‖∏ m ∈ Finset.range q, a q m - ((e q : ℝ) : ℂ)‖ ≤
      C / Real.sqrt q + B ^ 2 / (4 * q) := by
    filter_upwards [eventually_ge_atTop q₀, eventually_ge_atTop 1,
      eventually_ge_atTop (Nat.ceil B)] with q hq0 hq1 hqB
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hBq : B ≤ q := (Nat.le_ceil B).trans (by exact_mod_cast hqB)
    set bq : ℕ → ℂ := fun m => ((1 - σ2 m / (2 * q) : ℝ) : ℂ) with hbq
    set eq' : ℕ → ℂ := fun m => ((Real.exp (-(σ2 m / (2 * q))) : ℝ) : ℂ) with heq'
    have hy : ∀ m, 0 ≤ σ2 m / (2 * q) ∧ σ2 m / (2 * q) ≤ 1 / 2 := by
      intro m
      refine ⟨by have := hσ0 m; positivity, ?_⟩
      rw [div_le_iff₀ (by positivity)]
      linarith [hσB m]
    have hb1 : ∀ m, ‖bq m‖ ≤ 1 := by
      intro m
      simp only [hbq, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]; constructor <;> linarith [hy m]
    have he1 : ∀ m, ‖eq' m‖ ≤ 1 := by
      intro m
      simp only [heq', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by linarith [(hy m).1])
    have h1 := prod_sub_prod_le q (a q) bq (ha1 q) hb1
    have h2 := prod_sub_prod_le q bq eq' hb1 he1
    have h1' : ∑ m ∈ Finset.range q, ‖a q m - bq m‖ ≤ C / Real.sqrt q := by
      calc _ ≤ ∑ m ∈ Finset.range q, C / (q * Real.sqrt q) :=
            Finset.sum_le_sum fun m _ => hab q hq0 m
        _ = C / Real.sqrt q := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
            field_simp
    have h2' : ∑ m ∈ Finset.range q, ‖bq m - eq' m‖ ≤ B ^ 2 / (4 * q) := by
      calc _ ≤ ∑ m ∈ Finset.range q, (B / (2 * q)) ^ 2 := by
            refine Finset.sum_le_sum fun m _ => ?_
            have hh := Real.abs_exp_sub_one_sub_id_le (x := -(σ2 m / (2 * q)))
              (by rw [abs_neg, abs_of_nonneg (hy m).1]; linarith [(hy m).2])
            simp only [hbq, heq', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            calc |1 - σ2 m / (2 * q) - Real.exp (-(σ2 m / (2 * q)))|
                = |Real.exp (-(σ2 m / (2 * q))) - 1 - -(σ2 m / (2 * q))| := by
                  rw [abs_sub_comm]; congr 1; ring
              _ ≤ (-(σ2 m / (2 * q))) ^ 2 := hh
              _ ≤ (B / (2 * q)) ^ 2 := by
                  rw [neg_sq]
                  exact pow_le_pow_left₀ (hy m).1
                    (div_le_div_of_nonneg_right (hσB m) (by positivity)) 2
        _ = B ^ 2 / (4 * q) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp
            ring
    rw [hprod_e q (by omega)]
    calc ‖∏ m ∈ Finset.range q, a q m - ∏ m ∈ Finset.range q, eq' m‖
        = ‖(∏ m ∈ Finset.range q, a q m - ∏ m ∈ Finset.range q, bq m) +
            (∏ m ∈ Finset.range q, bq m - ∏ m ∈ Finset.range q, eq' m)‖ := by ring_nf
      _ ≤ ‖∏ m ∈ Finset.range q, a q m - ∏ m ∈ Finset.range q, bq m‖ +
            ‖∏ m ∈ Finset.range q, bq m - ∏ m ∈ Finset.range q, eq' m‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hzero : Tendsto (fun q : ℕ => C / Real.sqrt q + B ^ 2 / (4 * q)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun q : ℕ => C / Real.sqrt q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun q : ℕ => B ^ 2 / (4 * (q : ℝ))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    simpa using h1.add h2
  have hdiff : Tendsto (fun q => ∏ m ∈ Finset.range q, a q m - ((e q : ℝ) : ℂ)) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound hzero
  have := hdiff.add he_lim
  simpa using this

lemma charFun_obs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : SerialData K) (θ₀ : EuclideanSpace ℝ (Fin K)) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (m : ℕ) (f : Fin (D.J m) → EuclideanSpace ℝ (Fin K))
    (s : EuclideanSpace ℝ (Fin K)) :
    charFun (μ.map (fun ω => f (Y m ω))) s =
      ∑ i, (prob D m i θ₀ : ℂ) * Complex.exp (((inner ℝ (f i) s : ℝ) : ℂ) * Complex.I) := by
  have hfm : Measurable f := measurable_of_finite f
  have hmap : μ.map (fun ω => f (Y m ω)) = (μ.map (Y m)).map f := by
    rw [Measure.map_map hfm (hY.measurable m)]; rfl
  haveI : IsProbabilityMeasure (μ.map (Y m)) :=
    Measure.isProbabilityMeasure_map (hY.measurable m).aemeasurable
  have hlaw' : ∀ i, (μ.map (Y m)).real {i} = prob D m i θ₀ := fun i => by
    rw [measureReal_def, Measure.map_apply (hY.measurable m) (measurableSet_singleton i),
      hY.law m i, ENNReal.toReal_ofReal (prob_nonneg' D m _ θ₀)]
  rw [hmap, charFun_apply, integral_map hfm.aemeasurable (by fun_prop),
    integral_fintype (Integrable.of_finite)]
  simp only [hlaw', Complex.real_smul]

/-- **score_clt** (sibling b3d348fc), Lyapunov-type CLT via characteristic functions. -/
theorem score_clt_aux {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (Z : Ω' → EuclideanSpace ℝ (Fin K))
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin K))) μ') :
    TendstoInDistribution
      (fun (q : ℕ) (ω : Ω) => (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q,
        invSqrtMap Ωlim (gradient (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀))
      atTop Z (fun _ => μ) μ' := by
  obtain ⟨hPmPinv, hsymm⟩ := sqrt_facts2 Ωlim h7.posDef
  obtain ⟨hPP, hPΩ⟩ := sqrt_facts Ωlim h7.posDef
  set Pinv := invSqrtMap Ωlim with hPinv
  set d : (m : ℕ) → Fin (D.J m) → EuclideanSpace ℝ (Fin K) :=
    fun m i => D.z m i - zbar D m θ₀ with hd
  set ξ : ℕ → Ω → EuclideanSpace ℝ (Fin K) := fun m ω => Pinv (d m (Y m ω)) with hξ
  have hfun : (fun (q : ℕ) (ω : Ω) => (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q,
        Pinv (gradient (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀)) =
      fun (q : ℕ) (ω : Ω) => (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q, ξ m ω := by
    funext q ω
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(hasGradientAt_logProb D m (Y m ω) θ₀).gradient]
  rw [hfun]
  have hξmeas : ∀ m, Measurable (ξ m) := fun m =>
    (measurable_of_finite (fun i : Fin (D.J m) => Pinv (d m i))).comp (hY.measurable m)
  have hξind : iIndepFun ξ μ :=
    hY.indep.comp (fun m (i : Fin (D.J m)) => Pinv (d m i)) (fun m => measurable_of_finite _)
  have hSmeas : ∀ q : ℕ, AEMeasurable (fun ω => ∑ m ∈ Finset.range q, ξ m ω) μ := fun q =>
    (Finset.measurable_fun_sum _ fun m _ => hξmeas m).aemeasurable
  refine ⟨fun q => ((Finset.measurable_fun_sum _ fun m _ => hξmeas m).const_smul
    ((Real.sqrt q)⁻¹)).aemeasurable, hZ.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  show Tendsto (fun q : ℕ => charFun (μ.map (fun ω =>
      (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q, ξ m ω)) t) atTop (𝓝 (charFun (μ'.map Z) t))
  rw [hZ.map_eq, charFun_stdGaussian]
  -- constants
  set CP : ℝ := ‖LinearMap.toContinuousLinearMap Pinv‖ with hCPdef
  have hCP0 : 0 ≤ CP := norm_nonneg _
  have hCP : ∀ v, ‖Pinv v‖ ≤ CP * ‖v‖ := fun v =>
    (LinearMap.toContinuousLinearMap Pinv).le_opNorm v
  have hM0 : 0 ≤ M := by
    obtain ⟨i⟩ : Nonempty (Fin (D.J 0)) := ⟨⟨0, D.one_le_J 0⟩⟩
    exact (norm_nonneg _).trans (h7.bounded.norm_z_le 0 i)
  have hdb : ∀ m i, ‖d m i‖ ≤ 2 * M := by
    intro m i
    refine (norm_sub_le _ _).trans ?_
    have := h7.bounded.norm_z_le m i
    have := norm_zbar_le D M (h7.bounded.norm_z_le m) θ₀
    linarith
  set b : ℝ := CP * (2 * M) * ‖t‖ with hb
  have hb0 : 0 ≤ b := by positivity
  -- per-observation data
  set x : (m : ℕ) → Fin (D.J m) → ℝ := fun m i => inner ℝ (Pinv (d m i)) t with hx
  set σ2 : ℕ → ℝ := fun m => ∑ i, prob D m i θ₀ * x m i ^ 2 with hσ2
  set a : ℕ → ℕ → ℂ := fun q m => ∑ i, (prob D m i θ₀ : ℂ) *
    Complex.exp ((((Real.sqrt q)⁻¹ * x m i : ℝ) : ℂ) * Complex.I) with ha
  have hcf : ∀ q : ℕ, charFun (μ.map (fun ω =>
      (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q, ξ m ω)) t = ∏ m ∈ Finset.range q, a q m := by
    intro q
    rw [charFun_map_smul_comp (hSmeas q), (hξind.restrict _).charFun_map_fun_finsetSum_eq_prod
      (fun m _ => (hξmeas m).aemeasurable), Finset.prod_apply]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [show ξ m = fun ω => (fun i => Pinv (d m i)) (Y m ω) from rfl,
      charFun_obs μ D θ₀ Y hY m (fun i => Pinv (d m i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right]
  have hxb : ∀ m i, |x m i| ≤ b := by
    intro m i
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ((hCP _).trans ?_) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (hdb m i) hCP0
  have hσ0 : ∀ m, 0 ≤ σ2 m := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (prob_nonneg' D m i θ₀) (sq_nonneg _)
  have hσB : ∀ m, σ2 m ≤ b ^ 2 := by
    intro m
    calc σ2 m ≤ ∑ i, prob D m i θ₀ * b ^ 2 := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (prob_nonneg' D m i θ₀)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hxb m i) 2
      _ = b ^ 2 := by rw [← Finset.sum_mul, sum_prob, one_mul]
  have hmean : ∀ m, ∑ i, prob D m i θ₀ * x m i = 0 := by
    intro m
    have := congrArg (fun v => inner ℝ (Pinv v) t) (sum_prob_sub_zbar D m θ₀)
    simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, map_zero, inner_zero_left]
      at this
    exact this
  have havg : Tendsto (fun q : ℕ => (q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, σ2 m) atTop
      (𝓝 (‖t‖ ^ 2)) := by
    set w := Pinv t with hw
    have hσw : ∀ m, σ2 m = inner ℝ (Matrix.toEuclideanLin (momentMatrix D θ₀ m) w) w := by
      intro m
      rw [inner_moment]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hx, hd]
      rw [hsymm]
    set F : Matrix (Fin K) (Fin K) ℝ → ℝ := fun A => inner ℝ (Matrix.toEuclideanLin A w) w
      with hF
    have hFc : Continuous F := by
      have : F = fun A => ∑ a : Fin K, ∑ b : Fin K, WithLp.ofLp w a * (A a b * WithLp.ofLp w b) :=
        funext fun A => inner_toEuclideanLin A w
      rw [this]
      fun_prop
    have h1 := (hFc.tendsto Ωlim).comp h7.tendsto_avg
    have e1 : ∀ q : ℕ, F ((q : ℝ)⁻¹ • ∑ m ∈ Finset.range q, momentMatrix D θ₀ m) =
        (q : ℝ)⁻¹ * ∑ m ∈ Finset.range q, σ2 m := by
      intro q
      simp only [hF, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
        real_inner_smul_left, sum_inner, hσw]
    have e2 : F Ωlim = ‖t‖ ^ 2 := by
      simp only [hF, hw]
      rw [← hsymm, hPΩ, hPmPinv, real_inner_self_eq_norm_sq]
    rw [e2] at h1
    exact h1.congr e1
  -- the factor estimates
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℕ, ∀ q ≥ q₀, 1 ≤ q ∧ b * (Real.sqrt q)⁻¹ ≤ 1 := by
    refine ⟨Nat.ceil (b ^ 2) + 1, fun q hq => ⟨by omega, ?_⟩⟩
    have hq' : b ^ 2 ≤ q := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : Nat.ceil (b ^ 2) ≤ q))
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
    rw [mul_inv_le_iff₀ hs, one_mul]
    exact Real.le_sqrt_of_sq_le hq'
  have ha1 : ∀ q m, ‖a q m‖ ≤ 1 := fun q m =>
    factor_norm_le (fun i => prob D m i θ₀) (fun i => (Real.sqrt q)⁻¹ * x m i)
      (fun i => prob_nonneg' D m i θ₀) (sum_prob D m θ₀)
  have hab : ∀ q ≥ q₀, ∀ m, ‖a q m - ((1 - σ2 m / (2 * q) : ℝ) : ℂ)‖ ≤
      b ^ 3 / (q * Real.sqrt q) := by
    intro q hq m
    obtain ⟨hq1, hbh⟩ := hq₀ q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
    have hfb := factor_bound (fun i => prob D m i θ₀) (x m) (fun i => prob_nonneg' D m i θ₀)
      (sum_prob D m θ₀) (hmean m) b (Real.sqrt q)⁻¹ (hxb m) (by positivity) hbh
    have e1 : ((1 - σ2 m / (2 * q) : ℝ) : ℂ) =
        ((1 - ((Real.sqrt q)⁻¹) ^ 2 * (∑ i, prob D m i θ₀ * x m i ^ 2) / 2 : ℝ) : ℂ) := by
      congr 1
      rw [inv_pow, Real.sq_sqrt hqpos.le]
      field_simp
      rfl
    have e2 : (b * (Real.sqrt q)⁻¹) ^ 3 = b ^ 3 / (q * Real.sqrt q) := by
      have : (Real.sqrt q) ^ 3 = q * Real.sqrt q := by
        rw [pow_succ, Real.sq_sqrt hqpos.le]
      rw [mul_pow, inv_pow, this, div_eq_mul_inv]
    rw [e1, ← e2]
    exact hfb
  have hlim := prod_tendsto_exp a σ2 (b ^ 2) (b ^ 3) (‖t‖ ^ 2) q₀ hσ0 hσB havg ha1 hab
  rw [show (fun q : ℕ => charFun (μ.map (fun ω =>
      (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q, ξ m ω)) t) =
      fun q : ℕ => ∏ m ∈ Finset.range q, a q m from funext hcf]
  convert hlim using 2
  push_cast
  ring_nf

end McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology McFadden1974.Asymptotics in
theorem solution {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hθ : IsMLE D Y θhat)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (Z : Ω' → EuclideanSpace ℝ (Fin K)) (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin K))) μ') :
    TendstoInMeasure μ θhat atTop (fun _ => θ₀) ∧
      TendstoInDistribution
        (fun (q : ℕ) (ω : Ω) => Real.sqrt q • sqrtMap Ωlim (θhat q ω - θ₀))
        atTop Z (fun _ => μ) μ' := by
  exact ⟨mle_consistent_aux μ D Jstar M θ₀ Ωlim h7 Y hY θhat hθ,
    asymptotic_normal_of_score_clt μ D Jstar M θ₀ Ωlim h7 Y hY θhat hθ μ' Z
      (score_clt_aux μ D Jstar M θ₀ Ωlim h7 Y hY μ' Z hZ)⟩
