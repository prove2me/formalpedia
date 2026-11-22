-- Prove2me | solution 1 for NoHair.kerrNewman_regularTensors
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:07:32.960148+00:00
-- url     : https://prove2.me/submissions/40da3b40-bb62-43f3-a02e-a866ecceaa77

import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair Set
open scoped ContDiff Manifold BigOperators

private theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

private theorem entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private noncomputable def shear (K : E4 →ₗ[ℝ] ℝ) (n : E4) (c : ℝ) (hn : K n = 0) : E4 ≃ₗ[ℝ] E4 where
  toLinearMap := LinearMap.id - K.smulRight (c • n)
  invFun w := w + K w • (c • n)
  left_inv w := by
    change w - K w • (c • n) + K (w - K w • (c • n)) • (c • n) = w
    simp [hn]
  right_inv w := by
    change w + K w • (c • n) - K (w + K w • (c • n)) • (c • n) = w
    simp [hn]

private theorem ks_basis (f : ℝ) (k : Fin 4 → ℝ)
    (hnull : -(k 0)^2 + (k 1)^2 + (k 2)^2 + (k 3)^2 = 0) :
    ∃ B : Module.Basis (Fin 4) ℝ E4, ∀ i j,
      matrixBilin (fun p q => minkowski p q + f * k p * k q) (B i) (B j) = minkowski i j := by
  let K : E4 →ₗ[ℝ] ℝ := k 0 • EuclideanSpace.projₗ 0 + k 1 • EuclideanSpace.projₗ 1 +
    k 2 • EuclideanSpace.projₗ 2 + k 3 • EuclideanSpace.projₗ 3
  let n : E4 := WithLp.toLp 2 ![-k 0, k 1, k 2, k 3]
  have kv (v : E4) : K v = k 0 * v 0 + k 1 * v 1 + k 2 * v 2 + k 3 * v 3 := rfl
  have hn : K n = 0 := by
    rw [kv]
    change k 0 * (-k 0) + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0
    nlinarith only [hnull]
  have hleft (w : E4) : matrixBilin minkowski n w = K w := by
    rw [matrix_eval, kv]
    simp [Fin.sum_univ_four, minkowski, n] <;> ring
  have hright (v : E4) : matrixBilin minkowski v n = K v := by
    rw [matrix_eval, kv]
    simp [Fin.sum_univ_four, minkowski, n] <;> ring
  have metric (v w : E4) : matrixBilin (fun p q => minkowski p q + f * k p * k q) v w =
      matrixBilin minkowski v w + f * K v * K w := by
    rw [matrix_eval (fun p q => minkowski p q + f * k p * k q) v w, matrix_eval minkowski v w]
    simp only [kv, Fin.sum_univ_four]
    ring
  let P := shear K n (f / 2) hn
  have iso (v w : E4) : matrixBilin (fun p q => minkowski p q + f * k p * k q) (P v) (P w) =
      matrixBilin minkowski v w := by
    rw [metric]
    change matrixBilin minkowski (v - K v • ((f / 2) • n)) (w - K w • ((f / 2) • n)) +
      f * K (v - K v • ((f / 2) • n)) * K (w - K w • ((f / 2) • n)) = matrixBilin minkowski v w
    simp [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      hleft, hright, hn, smul_eq_mul] <;> ring
  let B := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
  refine ⟨B.map P, ?_⟩
  intro i j
  change matrixBilin _ (P (B i)) (P (B j)) = _
  rw [iso]
  have hb (l : Fin 4) : B l = coordBasis l := EuclideanSpace.basisFun_apply (Fin 4) ℝ l
  rw [hb, hb]
  exact entry minkowski i j

private theorem smooth_restrict (U : TopologicalSpace.Opens E4) (A : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ∞ (fun z => A z i j) y) :
    IsSmoothBilinField (M := U) (fun x => matrixBilin (A x.val)) := by
  intro c hc i j y hy
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : U) : c = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ c.target) : (c.symm z).val = z := by
    have eqval (x : U) : c x = x.val := by rw [hchart x] <;> rfl
    exact (eqval (c.symm z)).symm.trans (c.right_inv hz)
  have derivAt (x : U) :
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) c.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    rw [hchart x]
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E4)) (x := x)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
    exact hd
  have coeff (z : E4) (hz : z ∈ c.target) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm z i j = A z i j := by
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz, entry]
  have hs : ContDiffOn ℝ ∞ (fun z => A z i j) c.target := by
    intro z hz
    have hzU : z ∈ U := (hval z hz) ▸ (c.symm z).property
    exact (h z hzU i j).contDiffWithinAt
  exact (hs.congr coeff) y hy

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z := by
  have hr := radius_smooth a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

theorem solution (m a e : ℝ) :
    IsLorentzian (kerrNewmanMetricField m a e) ∧
    IsSmoothBilinField (kerrNewmanMetricField m a e) ∧
    IsSmoothBilinField (kerrNewmanFieldField a e) := by
  refine ⟨?_, smooth_restrict (kerrNewmanSpacetime a) (kerrNewmanMetric m a e) ?_,
    smooth_restrict (kerrNewmanSpacetime a) (kerrNewmanField a e) ?_⟩
  · intro x
    exact ks_basis (ksProfile m a e x.val) (ksNull a x.val) (ks_null a x.val x.property)
  · intro y hy i j
    have hpos : 0 < ksRadius a y := hy
    have hr := radius_smooth a y hpos
    have hi := null_smooth a y hpos i
    have hj := null_smooth a y hpos j
    have hd := (ks_den_pos a y hpos).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  · intro y hy i j
    have hpos : 0 < ksRadius a y := hy
    have hr := radius_smooth a y hpos
    have hd := (ks_den_pos a y hpos).ne'
    have hpot (l : Fin 4) : ContDiffAt ℝ ∞ (fun w => kerrNewmanPotential a e w l) y := by
      have hk := null_smooth a y hpos l
      unfold kerrNewmanPotential
      fun_prop (disch := assumption)
    have hpart (k l : Fin 4) : ContDiffAt ℝ ∞ (coordPartial (fun w => kerrNewmanPotential a e w l) k) y :=
      ((hpot l).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    exact (hpart i j).sub (hpart j i)
