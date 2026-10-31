-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:00:53.049496+00:00
-- url     : https://prove2.me/submissions/4c4d6f0a-bca8-409e-a63e-b9c0875479d5

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Operator-norm bound from an entrywise bound on the matrix of `A` in the standard basis. -/
lemma IA17_opNorm_le {D : ℕ}
    (A : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i j : Fin D, |A (EuclideanSpace.single j 1) i| ≤ M) : ‖A‖ ≤ D * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hx : x = ∑ j, x j • EuclideanSpace.single j (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin D) ℝ).sum_repr x]
    simp
  have hAx : ∀ i, A x i = ∑ j, x j * A (EuclideanSpace.single j 1) i := by
    intro i
    conv_lhs => rw [hx]
    simp [map_sum, map_smul]
  have hsq : ‖A x‖ ^ 2 ≤ (D * M * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hxn : ‖x‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := EuclideanSpace.norm_sq_eq x
    calc ∑ i, ‖A x i‖ ^ 2 = ∑ i, (∑ j, x j * A (EuclideanSpace.single j 1) i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs, hAx]
      _ ≤ ∑ i : Fin D, (∑ j, x j ^ 2) * (∑ j : Fin D, (A (EuclideanSpace.single j 1) i) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ ∑ i : Fin D, (∑ j, x j ^ 2) * (∑ j : Fin D, M ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun j _ => sq_nonneg _)
          refine Finset.sum_le_sum fun j _ => ?_
          have := h i j
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (D * M * ‖x‖) ^ 2 := by
          rw [mul_pow, hxn]
          simp only [Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hsq

theorem solution {D : ℕ} (F : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D))
    (Θ : Set (EuclideanSpace ℝ (Fin D))) (θs : EuclideanSpace ℝ (Fin D)) (C1 C2 δ : ℝ)
    (hF : ContDiffOn ℝ 1 F Θ) (hinj : Set.InjOn F Θ) (hθs : θs ∈ Θ)
    (hball : Metric.closedBall θs (2 * C2 * δ) ⊆ Θ)
    (hJ : ∀ θ ∈ Metric.closedBall θs (2 * C2 * δ), ∀ i j : Fin D,
      |(fderivWithin ℝ F Θ θ - fderivWithin ℝ F Θ θs) (EuclideanSpace.single j 1) i| ≤ C1 * ‖θ - θs‖)
    (Jinv : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D))
    (hJinv : Jinv.comp (fderivWithin ℝ F Θ θs) = ContinuousLinearMap.id ℝ _ ∧
      (fderivWithin ℝ F Θ θs).comp Jinv = ContinuousLinearMap.id ℝ _)
    (hC2 : ‖Jinv‖ ≤ C2) (hsmall : 2 * Real.sqrt (D * D) * C1 * C2 ^ 2 * δ < 1 / 2) :
    ∀ θ ∈ Θ, ‖F θ - F θs‖ ≤ δ → ‖θ - θs‖ ≤ 2 * C2 * δ := by
  intro θ hθ hFθ
  set J := fderivWithin ℝ F Θ θs with hJdef
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hFθ
  have hC2n : 0 ≤ C2 := (norm_nonneg _).trans hC2
  rw [Real.sqrt_mul_self (Nat.cast_nonneg D)] at hsmall
  rcases eq_or_lt_of_le (norm_nonneg Jinv) with h0 | hpos
  · -- `Jinv = 0` forces the space to be trivial
    have hJ0 : Jinv = 0 := norm_eq_zero.mp h0.symm
    have hv : θ - θs = 0 := by
      have := congrArg (fun L : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D) =>
        L (θ - θs)) hJinv.1
      simpa [hJ0] using this.symm
    rw [hv, norm_zero]; positivity
  set ρ := 2 * C2 * δ with hρ
  have hρn : 0 ≤ ρ := by positivity
  have hC2p : 0 < C2 := lt_of_lt_of_le hpos hC2
  -- the linear equivalence `J` with inverse `Jinv`
  let e : EuclideanSpace ℝ (Fin D) ≃L[ℝ] EuclideanSpace ℝ (Fin D) :=
    ContinuousLinearEquiv.equivOfInverse J Jinv
      (fun v => by simpa using congrArg (fun L : EuclideanSpace ℝ (Fin D) →L[ℝ] _ => L v) hJinv.1)
      (fun v => by simpa using congrArg (fun L : EuclideanSpace ℝ (Fin D) →L[ℝ] _ => L v) hJinv.2)
  set cr : ℝ := D * max C1 0 * ρ with hcr
  have hcrn : 0 ≤ cr := by positivity
  let c : ℝ≥0 := ⟨cr, hcrn⟩
  -- Jacobian deviation bound on the ball
  have hdev : ∀ x ∈ Metric.closedBall θs ρ, ‖fderivWithin ℝ F Θ x - J‖ ≤ cr := by
    intro x hx
    rw [hcr, mul_assoc]
    apply IA17_opNorm_le _ _ (by positivity)
    intro i j
    refine (hJ x hx i j).trans ?_
    have hxr : ‖x - θs‖ ≤ ρ := by simpa [dist_eq_norm] using hx
    calc C1 * ‖x - θs‖ ≤ max C1 0 * ‖x - θs‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max C1 0 * ρ := mul_le_mul_of_nonneg_left hxr (le_max_right _ _)
  have hdiff : ∀ x ∈ Metric.closedBall θs ρ,
      HasFDerivWithinAt F (fderivWithin ℝ F Θ x) (Metric.closedBall θs ρ) x := by
    intro x hx
    have hd : DifferentiableOn ℝ F Θ := hF.differentiableOn (by norm_num)
    exact ((hd x (hball hx)).hasFDerivWithinAt).mono hball
  have happrox : ApproximatesLinearOn F ((e : EuclideanSpace ℝ (Fin D) →L[ℝ] _))
      (Metric.closedBall θs ρ) c := by
    intro x hx y hy
    show ‖F x - F y - J (x - y)‖ ≤ cr * ‖x - y‖
    exact (convex_closedBall θs ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      hdiff hdev hy hx
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse e.toNonlinearRightInverse
    hρn le_rfl
  have hnn : ((e.toNonlinearRightInverse.nnnorm : ℝ)) = ‖Jinv‖ := rfl
  rw [hnn] at hsurj
  -- radius comparison
  have hrad : δ ≤ (‖Jinv‖⁻¹ - cr) * ρ := by
    have h1 : C2⁻¹ ≤ ‖Jinv‖⁻¹ := inv_anti₀ hpos hC2
    have h2 : C2⁻¹ * ρ = 2 * δ := by rw [hρ]; field_simp
    have h3 : cr * ρ ≤ δ := by
      rcases le_total C1 0 with hc | hc
      · rw [hcr, max_eq_right hc]; simp [hδ]
      · rw [hcr, max_eq_left hc, hρ]
        have : 2 * (D : ℝ) * C1 * C2 ^ 2 * δ ≤ 1 / 2 := hsmall.le
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * δ)]
    nlinarith [mul_le_mul_of_nonneg_right h1 hρn]
  obtain ⟨θ', hθ'b, hθ'F⟩ := hsurj (Metric.closedBall_subset_closedBall hrad
    (by simpa [dist_eq_norm] using hFθ))
  have : θ' = θ := hinj (hball hθ'b) hθ hθ'F
  subst this
  simpa [dist_eq_norm] using hθ'b
