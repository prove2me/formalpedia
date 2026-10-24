-- Prove2me | solution 1 for K24.Global.projected_actual_vector_defect_identity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:37:32.458727+00:00
-- url     : https://prove2.me/submissions/a70e7075-0699-4d53-9c99-313a121c4589

import Definitions.Def_K24GlobalGeometry

/-!
Exact operator algebra for the literal frozen K24 definitions.
No target file with admitted theorems is imported.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.Research20261024

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

@[simp] theorem covectorInChart_sub (eta theta : RawCovector M) (c : M) (x : FourSpace) :
    covectorInChart (eta - theta) c x = covectorInChart eta c x - covectorInChart theta c x := by
  rfl

@[simp] theorem covectorInChart_zero (c : M) (x : FourSpace) :
    covectorInChart (0 : RawCovector M) c x = 0 := by
  rfl

@[simp] theorem cov2InChart_zero (c : M) (x : FourSpace) :
    cov2InChart (0 : RawCov2 M) c x = 0 := by
  rfl

@[simp] theorem cov2FromCoordinates_zero :
    cov2FromCoordinates (fun (_ : M) (_ : FourSpace) => (0 : Mat4)) = 0 := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear]

@[simp] theorem cov2FromCoordinates_sub (a b : M → FourSpace → Mat4) :
    cov2FromCoordinates (a - b) = cov2FromCoordinates a - cov2FromCoordinates b := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear, sub_mul,
    mul_sub, Finset.sum_sub_distrib]

/-- This is the genuine coordinate derivative rule, with its essential hypotheses. -/
theorem coordDeriv_sub {f h : FourSpace → ℝ} {x : FourSpace}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (i : Fin 4) :
    coordDeriv (f - h) i x = coordDeriv f i x - coordDeriv h i x := by
  simp [coordDeriv, fderiv_sub hf hh]

/-- Coordinate regularity on the chart target supplies ordinary, not merely
within-set, differentiability because the chart target is open. -/
theorem covector_coefficient_differentiableAt (eta : RawCovector M)
    (h : CovectorContDiff 1 eta) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    DifferentiableAt ℝ (fun y => covectorInChart eta c y j) x := by
  exact differentiableAt_pi.mp
    (((h c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt_one) j

@[simp] theorem deltaStar_zero (g : RawCov2 M) : deltaStar g 0 = 0 := by
  have hz : deltaStarInChart g 0 = fun _ _ => (0 : Mat4) := by
    funext c x i j
    simp [deltaStarInChart, nablaCovectorInChart, coordDeriv]
  rw [deltaStar, hz, cov2FromCoordinates_zero]

/-- Subtraction for the actual Levi-Civita symmetrized gradient. The metric
is arbitrary: this law only differentiates its covector argument. -/
theorem deltaStar_sub (g : RawCov2 M) (eta theta : RawCovector M)
    (heta : CovectorContDiff 1 eta) (htheta : CovectorContDiff 1 theta) :
    deltaStar g (eta - theta) = deltaStar g eta - deltaStar g theta := by
  have hlocal (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
      (a b : Fin 4) :
      nablaCovectorInChart g (eta - theta) c x a b =
        nablaCovectorInChart g eta c x a b - nablaCovectorInChart g theta c x a b := by
    have hd := coordDeriv_sub
      (covector_coefficient_differentiableAt eta heta c x hx b)
      (covector_coefficient_differentiableAt theta htheta c x hx b) a
    simp only [nablaCovectorInChart, covectorInChart_sub, Pi.sub_apply]
    change coordDeriv ((fun y => covectorInChart eta c y b) -
      (fun y => covectorInChart theta c y b)) a x - _ = _
    rw [hd]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  unfold deltaStar
  rw [← cov2FromCoordinates_sub]
  funext p
  change cov2FromChartAt p p (deltaStarInChart g (eta - theta) p (chartAt FourSpace p p)) =
    cov2FromChartAt p p ((deltaStarInChart g eta - deltaStarInChart g theta) p
      (chartAt FourSpace p p))
  congr 1
  ext i j
  simp only [Pi.sub_apply, deltaStarInChart]
  rw [hlocal p _ (mem_chart_target FourSpace p) i j,
    hlocal p _ (mem_chart_target FourSpace p) j i]
  ring

/-- The exact unprojected tensor-defect identity for the frozen operators.
Regularity of the two Bianchi outputs is explicit, not presumed from the
unproved coordinate-compatibility results. -/
theorem gaugedLinearization_difference (lam : ℝ) (ghat z u : RawCov2 M)
    (hfixed : CovectorContDiff 1 (bianchi ghat u))
    (hcenter : CovectorContDiff 1 (bianchi z u)) :
    gaugedLinearization lam ghat z u - gaugedLinearization lam z z u =
      tensorDefect ghat z u := by
  unfold gaugedLinearization tensorDefect
  rw [deltaStar_sub z _ _ hfixed hcenter]
  abel

@[simp] theorem cov2VariationDerivative_zero (t : ℝ) :
    cov2VariationDerivative (fun _ => (0 : RawCov2 M)) t = 0 := by
  simp only [cov2VariationDerivative, cov2InChart_zero, deriv_const]
  exact cov2FromCoordinates_zero

/-- The metric-dependent variation term vanishes on an identically zero
covector without differentiability or positivity assumptions. -/
@[simp] theorem deltaStarMetricVariation_zero (z u : RawCov2 M) :
    deltaStarMetricVariation z u 0 = 0 := by
  simp [deltaStarMetricVariation]

/-- Cancels the dangerous metric-variation term once genuine Haar cancellation
has been established; it does not assume a product rule. -/
theorem dangerous_term_zero_of_cancellation (rho : CircleAction M)
    (ghat z u : RawCov2 M)
    (hc : covectorPiPerp rho (bianchi ghat (z - ghat)) = 0) :
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) = 0 := by
  rw [hc, deltaStarMetricVariation_zero]

@[simp] theorem cov2InChart_sub (u v : RawCov2 M) (c : M) (x : FourSpace) :
    cov2InChart (u - v) c x = cov2InChart u c x - cov2InChart v c x := by
  rfl

@[simp] theorem covectorFromCoordinates_sub (a b : M → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (a - b) = covectorFromCoordinates a - covectorFromCoordinates b := by
  ext p v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    sub_mul, Finset.sum_sub_distrib]

theorem cov2_coefficient_differentiableAt (u : RawCov2 M)
    (h : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => cov2InChart u c y i j) x := by
  exact differentiableAt_pi.mp (differentiableAt_pi.mp
    (((h c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt_one) i) j

/-- The actual Lie derivative is additive in its tensor argument. There is
no regularity premise on Y: its coordinate derivatives are fixed coefficients. -/
theorem lieTensor_sub (Y : RawVector M) (u v : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v) :
    lieTensor Y (u - v) = lieTensor Y u - lieTensor Y v := by
  have hlocal (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
      (i j : Fin 4) :
      lieTensorInChart Y (u - v) c x i j =
        lieTensorInChart Y u c x i j - lieTensorInChart Y v c x i j := by
    have hd (a : Fin 4) := coordDeriv_sub
      (cov2_coefficient_differentiableAt u hu c x hx i j)
      (cov2_coefficient_differentiableAt v hv c x hx i j) a
    simp only [lieTensorInChart, cov2InChart_sub, Matrix.sub_apply]
    change (∑ a, (vectorInChart Y c x a *
      coordDeriv ((fun y => cov2InChart u c y i j) -
        (fun y => cov2InChart v c y i j)) a x + _ + _)) = _
    simp only [hd, mul_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold lieTensor
  rw [← cov2FromCoordinates_sub]
  funext p
  change cov2FromChartAt p p (lieTensorInChart Y (u - v) p (chartAt FourSpace p p)) =
    cov2FromChartAt p p ((lieTensorInChart Y u - lieTensorInChart Y v) p
      (chartAt FourSpace p p))
  congr 1
  ext i j
  exact hlocal p _ (mem_chart_target FourSpace p) i j

theorem nablaTensorInChart_sub (g u v : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (a b d : Fin 4) :
    nablaTensorInChart g (u - v) c x a b d =
      nablaTensorInChart g u c x a b d - nablaTensorInChart g v c x a b d := by
  have hd := coordDeriv_sub
    (cov2_coefficient_differentiableAt u hu c x hx b d)
    (cov2_coefficient_differentiableAt v hv c x hx b d) a
  simp only [nablaTensorInChart, cov2InChart_sub, Matrix.sub_apply]
  change coordDeriv ((fun y => cov2InChart u c y b d) -
    (fun y => cov2InChart v c y b d)) a x - _ - _ = _
  rw [hd]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

@[simp] theorem metricTraceInChart_sub (g u v : RawCov2 M) (c : M) :
    metricTraceInChart g (u - v) c = metricTraceInChart g u c - metricTraceInChart g v c := by
  funext x
  simp [metricTraceInChart, mul_sub, Finset.sum_sub_distrib]

/-- A transparent sufficient hypothesis for the differentiability of each
metric trace. Smoothness of inversion is not silently assumed here. -/
theorem metricTraceInChart_differentiableAt (g u : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hinv : DifferentiableAt ℝ (inverseMetricInChart g c) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  unfold metricTraceInChart
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.fun_sum
  intro j _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hinv i) j).mul
    (cov2_coefficient_differentiableAt u hu c x hx i j)

/-- Bianchi subtraction follows from genuine differentiation of the tensor
coefficients and inverse metric. This is independent of naturality. -/
theorem bianchi_sub (g u v : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v)
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart g c) x) :
    bianchi g (u - v) = bianchi g u - bianchi g v := by
  have hlocal (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
      (j : Fin 4) :
      bianchiInChart g (u - v) c x j = bianchiInChart g u c x j - bianchiInChart g v c x j := by
    have hd := coordDeriv_sub
      (metricTraceInChart_differentiableAt g u hu c x hx (hinv c x hx))
      (metricTraceInChart_differentiableAt g v hv c x hx (hinv c x hx)) j
    simp only [bianchiInChart, metricTraceInChart_sub,
      nablaTensorInChart_sub g u v hu hv c x hx, hd, mul_sub, Finset.sum_sub_distrib]
    ring
  unfold bianchi
  rw [← covectorFromCoordinates_sub]
  funext p
  change covectorFromChartAt p p (bianchiInChart g (u - v) p (chartAt FourSpace p p)) =
    covectorFromChartAt p p ((bianchiInChart g u - bianchiInChart g v) p
      (chartAt FourSpace p p))
  congr 1
  ext j
  exact hlocal p _ (mem_chart_target FourSpace p) j

/-- The complete, unprojected actual-metric vector defect, including its
second Lie term. Input regularity of the reconstructed Lie tensors and
inverse metric is made explicit rather than inferred from missing chart
compatibility theorems. -/
theorem actualMetricVector_difference (ghat z g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hz : Cov2ContDiff 1 z)
    (hLg : Cov2ContDiff 1 (lieTensor Y g)) (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart ghat c) x) :
    vectorOperator ghat g Y - vectorOperator z z Y =
      actualMetricVectorDefect ghat z g Y := by
  unfold vectorOperator actualMetricVectorDefect killing
  rw [lieTensor_sub Y g z hg hz, bianchi_sub ghat _ _ hLg hLz hinv]
  abel

@[simp] theorem actionPullbackCovector_sub (rho : CircleAction M) (t : Circle)
    (eta theta : RawCovector M) :
    actionPullbackCovector rho t (eta - theta) =
      actionPullbackCovector rho t eta - actionPullbackCovector rho t theta := by
  rfl

/-- Linearity of the genuine scalar Haar integrals uses their explicit
integrability premises, rather than the integral's default outside its domain. -/
theorem covectorPi0_sub (rho : CircleAction M) (eta theta : RawCovector M)
    (heta : CovectorHaarIntegrable rho eta) (htheta : CovectorHaarIntegrable rho theta) :
    covectorPi0 rho (eta - theta) = covectorPi0 rho eta - covectorPi0 rho theta := by
  unfold covectorPi0
  rw [← covectorFromCoordinates_sub]
  funext p
  change covectorFromChartAt p p _ = covectorFromChartAt p p _
  congr 1
  ext i
  simp only [actionPullbackCovector_sub, covectorInChart_sub, Pi.sub_apply]
  exact MeasureTheory.integral_sub
    (heta p _ (mem_chart_target FourSpace p) i)
    (htheta p _ (mem_chart_target FourSpace p) i)

theorem covectorPiPerp_sub (rho : CircleAction M) (eta theta : RawCovector M)
    (heta : CovectorHaarIntegrable rho eta) (htheta : CovectorHaarIntegrable rho theta) :
    covectorPiPerp rho (eta - theta) = covectorPiPerp rho eta - covectorPiPerp rho theta := by
  unfold covectorPiPerp
  rw [covectorPi0_sub rho eta theta heta htheta]
  abel

/-- The center vector difference needs only integrability to pass subtraction
through the common projection. -/
theorem projected_center_vector_difference (rho : CircleAction M)
    (ghat z : RawCov2 M) (Y : RawVector M)
    (hfixed : CovectorHaarIntegrable rho (vectorOperator ghat z Y))
    (hcenter : CovectorHaarIntegrable rho (vectorOperator z z Y)) :
    projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y =
      covectorPiPerp rho (bianchi ghat (killing z Y) - bianchi z (killing z Y)) := by
  exact (covectorPiPerp_sub rho _ _ hfixed hcenter).symm

/-- K24's complete projected actual-metric vector defect under explicit
regularity and genuine Haar-integrability premises. -/
theorem projected_actual_vector_difference (rho : CircleAction M)
    (ghat z g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hz : Cov2ContDiff 1 z)
    (hLg : Cov2ContDiff 1 (lieTensor Y g)) (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart ghat c) x)
    (hfixed : CovectorHaarIntegrable rho (vectorOperator ghat g Y))
    (hcenter : CovectorHaarIntegrable rho (vectorOperator z z Y)) :
    projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
      projectedActualVectorDefect rho ghat z g Y := by
  unfold projectedVectorOperator projectedActualVectorDefect
  rw [← covectorPiPerp_sub rho _ _ hfixed hcenter,
    actualMetricVector_difference ghat z g Y hg hz hLg hLz hinv]

/-- A genuine invariant covector has constant orbit coefficients and hence
fiberwise Haar integrability. -/
theorem covectorHaarIntegrable_of_invariant (rho : CircleAction M) (eta : RawCovector M)
    (heta : IsInvariantCovector rho eta) : CovectorHaarIntegrable rho eta := by
  intro c x _ i
  unfold IsInvariantCovector at heta
  simp only [heta]
  exact MeasureTheory.integrable_const _

/-- The normalized scalar Haar integral fixes an invariant covector. Chart
reconstruction is justified by the actual inverse-chart differential theorem. -/
theorem covectorPi0_of_invariant [IsManifold I4 ∞ M]
    (rho : CircleAction M) (eta : RawCovector M) (heta : IsInvariantCovector rho eta) :
    covectorPi0 rho eta = eta := by
  unfold IsInvariantCovector at heta
  funext p
  change covectorFromChartAt p p (fun i =>
    ∫ t : Circle, covectorInChart (actionPullbackCovector rho t eta) p
      (chartAt FourSpace p p) i ∂circleHaar) = eta p
  simp only [heta, MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  exact covector_chart_recovery eta p p (mem_chart_source FourSpace p)

theorem covectorPiPerp_of_invariant [IsManifold I4 ∞ M]
    (rho : CircleAction M) (eta : RawCovector M) (heta : IsInvariantCovector rho eta) :
    covectorPiPerp rho eta = 0 := by
  rw [covectorPiPerp, covectorPi0_of_invariant rho eta heta, sub_self]

/-- Exact dangerous-term cancellation from invariance of the Bianchi output.
Establishing that invariance from invariant metrics still requires naturality. -/
theorem dangerous_term_zero_of_invariant [IsManifold I4 ∞ M]
    (rho : CircleAction M) (ghat z u : RawCov2 M)
    (hinv : IsInvariantCovector rho (bianchi ghat (z - ghat))) :
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) = 0 := by
  exact dangerous_term_zero_of_cancellation rho ghat z u
    (covectorPiPerp_of_invariant rho _ hinv)

end K24.Global.Research20261024


open K24.Global
universe uM

theorem solution
    {M : Type uM} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (rho : CircleAction M) (ghat z g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 1 g) (hz : Cov2ContDiff 1 z)
    (hLg : Cov2ContDiff 1 (lieTensor Y g))
    (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hinv : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      DifferentiableAt ℝ (inverseMetricInChart ghat c) x)
    (hfixed : CovectorHaarIntegrable rho (vectorOperator ghat g Y))
    (hcenter : CovectorHaarIntegrable rho (vectorOperator z z Y)) :
    projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
      projectedActualVectorDefect rho ghat z g Y := by
  exact Research20261024.projected_actual_vector_difference rho ghat z g Y
    hg hz hLg hLz hinv hfixed hcenter

#print axioms solution
