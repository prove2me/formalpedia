-- Prove2me | solution 1 for McFadden1974.Asymptotics.mle_consistent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T23:47:40.105562+00:00
-- url     : https://prove2.me/submissions/fe496398-21fc-45de-b6c5-364fd0c420ef

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

end McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology McFadden1974.Asymptotics in
theorem solution {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hθ : IsMLE D Y θhat) :
    TendstoInMeasure μ θhat atTop (fun _ => θ₀) := by
  exact mle_consistent_aux μ D Jstar M θ₀ Ωlim h7 Y hY θhat hθ
