-- Prove2me | solution 1 for K24.Global.FlatTorus.projectedDefect_holder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:28:41.332395+00:00
-- url     : https://prove2.me/submissions/1258a537-d35f-41b5-9102-70df348c83ff

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus.SmoothProof

theorem chartAt_eq_localInverse (p : Torus) :
    (chartAt FourSpace p : Torus → FourSpace) =
      quotientMap_isLocalHomeomorph.localInverseAt (representative p) := by
  rfl

theorem chartAt_symm_eq_quotientMap (p : Torus) :
    ((chartAt FourSpace p).symm : FourSpace → Torus) = quotientMap := by
  change ((quotientMap_isLocalHomeomorph.localInverseAt (representative p)).symm :
    FourSpace → Torus) = quotientMap
  exact quotientMap_isLocalHomeomorph.localInverseAt_symm _

theorem quotientMap_add (x y : FourSpace) : quotientMap (x + y) = quotientMap x * quotientMap y := by
  funext i
  exact Circle.exp_add (x i) (y i)

theorem quotientMap_sub (x y : FourSpace) : quotientMap (x - y) = quotientMap x / quotientMap y := by
  funext i
  exact Circle.exp_sub (x i) (y i)

theorem chartAt_quotient_eventually_affine (p : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace p).source) :
    (fun z => chartAt FourSpace p (quotientMap z)) =ᶠ[𝓝 x]
      (fun z => z - x + chartAt FourSpace p (quotientMap x)) := by
  let e := chartAt FourSpace p
  let y := e (quotientMap x)
  have hy : y ∈ e.target := e.map_source hx
  have hqy : quotientMap y = quotientMap x := by
    exact (congrFun (chartAt_symm_eq_quotientMap p) y).symm.trans (e.left_inv hx)
  have hcont : ContinuousAt (fun z : FourSpace => z - x + y) x :=
    (continuousAt_id.sub continuousAt_const).add continuousAt_const
  have hn : ∀ᶠ z in 𝓝 x, z - x + y ∈ e.target :=
    hcont (by simpa using e.open_target.mem_nhds hy)
  filter_upwards [hn] with z hz
  have hqz : quotientMap (z - x + y) = quotientMap z := by
    rw [quotientMap_add, quotientMap_sub, hqy]
    simp
  change e (quotientMap z) = z - x + y
  calc
    e (quotientMap z) = e (quotientMap (z - x + y)) := congrArg e hqz.symm
    _ = e (e.symm (z - x + y)) :=
      congrArg e (congrFun (chartAt_symm_eq_quotientMap p) (z - x + y)).symm
    _ = z - x + y := e.right_inv hz

theorem contDiffAt_chartAt_quotient (p : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace p).source) :
    ContDiffAt ℝ ∞ (fun z => chartAt FourSpace p (quotientMap z)) x := by
  exact ((contDiffAt_id.sub contDiffAt_const).add contDiffAt_const).congr_of_eventuallyEq
    (chartAt_quotient_eventually_affine p x hx)

theorem original_torus_isManifold : IsManifold I4 ∞ Torus := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change ∃ p : Torus, chartAt FourSpace p = e at he
  change ∃ p : Torus, chartAt FourSpace p = e' at he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  intro x hx
  change ContDiffWithinAt ℝ ∞
    (fun z => chartAt FourSpace q ((chartAt FourSpace p).symm z)) _ x
  rw [chartAt_symm_eq_quotientMap]
  apply (contDiffAt_chartAt_quotient q x _).contDiffWithinAt
  have h := hx.1.2
  change (chartAt FourSpace p).symm x ∈ (chartAt FourSpace q).source at h
  rwa [chartAt_symm_eq_quotientMap] at h

attribute [local instance] original_torus_isManifold

theorem contMDiff_quotientMap : ContMDiff I4 I4 ∞ quotientMap := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨quotientMap_isLocalHomeomorph.continuous.continuousAt, ?_⟩
  simpa only [mfld_simps, Function.comp_def] using
    (contDiffAt_chartAt_quotient (quotientMap x) x (mem_chart_source _ _)).contDiffWithinAt (s := Set.univ)

/-- A smooth real lift of the relative circle coordinate near its base point. -/
def relativeAngle (t0 t : Circle) : ℝ := (Complex.log ((t / t0 : Circle) : ℂ)).im

theorem exp_relativeAngle (t0 t : Circle) : Circle.exp (relativeAngle t0 t) = t / t0 := by
  simp only [relativeAngle, Complex.log_im, Circle.exp_arg]

theorem contMDiffAt_relativeAngle (t0 : Circle) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (relativeAngle t0) t0 := by
  have hlog : ContDiffAt ℝ ∞ Complex.log (1 : ℂ) :=
    (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  have hdiv : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun t : Circle => t / t0) :=
    contMDiff_id.div contMDiff_const
  have : Fact (Module.finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun t : Circle => (t : ℂ)) :=
    contMDiff_coe_sphere (E := ℂ) (n := 1)
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun t : Circle => ((t / t0 : Circle) : ℂ)) :=
    hc.comp hdiv
  have hlog' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ Complex.log ((t0 / t0 : Circle) : ℂ) := by
    simpa using hlog.contMDiffAt
  have h := hlog'.comp t0 (hcoe t0)
  unfold relativeAngle
  simpa only [Function.comp_def, Complex.imCLM_apply] using Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp t0 h

theorem quotientMap_chartAt (p q : Torus) (hq : q ∈ (chartAt FourSpace p).source) :
    quotientMap (chartAt FourSpace p q) = q :=
  (congrFun (chartAt_symm_eq_quotientMap p) (chartAt FourSpace p q)).symm.trans
    ((chartAt FourSpace p).left_inv hq)

theorem quotientMap_shift_second (a : ℝ) (x : FourSpace) :
    quotientMap (x + a • basisVector 1) = translate (Circle.exp a) (quotientMap x) := by
  funext i
  by_cases hi : i = 1
  · subst i
    simp [quotientMap, translate, basisVector, Circle.exp_add, mul_comm]
  · simp [quotientMap, translate, basisVector, hi]

theorem contMDiff_translate :
    ContMDiff ((𝓡 1).prod I4) I4 ∞ (fun q : Circle × Torus => translate q.1 q.2) := by
  intro q0
  let t0 := q0.1
  let p0 := q0.2
  let lift : Circle × Torus → FourSpace := fun q =>
    chartAt FourSpace p0 q.2 +
      (relativeAngle t0 q.1 + Complex.arg (t0 : ℂ)) • basisVector 1
  have hc : ContMDiffAt I4 I4 ∞ (chartAt FourSpace p0) p0 :=
    contMDiffOn_chart.contMDiffAt ((chartAt FourSpace p0).open_source.mem_nhds (mem_chart_source _ _))
  have hlift : ContMDiffAt ((𝓡 1).prod I4) I4 ∞ lift q0 :=
    (hc.comp q0 contMDiffAt_snd).add
      (((contMDiffAt_relativeAngle t0).comp q0 contMDiffAt_fst).add
        contMDiffAt_const |>.smul contMDiffAt_const)
  have h := (contMDiff_quotientMap (lift q0)).comp q0 hlift
  apply h.congr_of_eventuallyEq
  have hn : ∀ᶠ q : Circle × Torus in 𝓝 q0, q.2 ∈ (chartAt FourSpace p0).source :=
    continuous_snd.continuousAt ((chartAt FourSpace p0).open_source.mem_nhds (mem_chart_source _ _))
  filter_upwards [hn] with q hq
  change translate q.1 q.2 = quotientMap (lift q)
  dsimp [lift]
  rw [quotientMap_shift_second, quotientMap_chartAt p0 q.2 hq,
    Circle.exp_add, exp_relativeAngle, Circle.exp_arg, div_mul_cancel]

/-- The original marked action, with the original quotient charted structure. -/
def smoothTranslationAction : CircleAction Torus where
  act := translate
  one_act := translate_one
  mul_act := translate_mul
  smooth := contMDiff_translate

theorem hasMFDerivAt_quotientMap (x : FourSpace) :
    HasMFDerivAt I4 I4 quotientMap x (ContinuousLinearMap.id ℝ FourSpace) := by
  refine ⟨quotientMap_isLocalHomeomorph.continuous.continuousAt, ?_⟩
  have h := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x).add_const
    (chartAt FourSpace (quotientMap x) (quotientMap x))).congr_of_eventuallyEq
    (chartAt_quotient_eventually_affine (quotientMap x) x (mem_chart_source _ _))
  convert h.hasFDerivWithinAt (s := Set.univ) using 1 <;>
    first | rfl | simp

theorem coverDifferential_eq_id (x : FourSpace) :
    coverDifferential x = ContinuousLinearMap.id ℝ FourSpace :=
  (hasMFDerivAt_quotientMap x).mfderiv

theorem hasMFDerivAt_chartAt (p q : Torus) (hq : q ∈ (chartAt FourSpace p).source) :
    HasMFDerivAt I4 I4 (chartAt FourSpace p) q (ContinuousLinearMap.id ℝ FourSpace) := by
  refine ⟨(chartAt FourSpace p).continuousAt hq, ?_⟩
  let x := chartAt FourSpace q q
  have hQx : quotientMap x = q := quotientMap_chartAt q q (mem_chart_source _ _)
  have hx : quotientMap x ∈ (chartAt FourSpace p).source := by rwa [hQx]
  have h := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x).add_const
    (chartAt FourSpace p (quotientMap x))).congr_of_eventuallyEq
    (chartAt_quotient_eventually_affine p x hx)
  simpa only [mfld_simps, Function.comp_def, chartAt_symm_eq_quotientMap] using
    h.hasFDerivWithinAt (s := Set.univ)

theorem mfderiv_chartAt_eq_id (p q : Torus) (hq : q ∈ (chartAt FourSpace p).source) :
    mfderiv I4 I4 (chartAt FourSpace p) q = ContinuousLinearMap.id ℝ FourSpace :=
  (hasMFDerivAt_chartAt p q hq).mfderiv

theorem hasMFDerivAt_translate (t : Circle) (p : Torus) :
    HasMFDerivAt I4 I4 (translate t) p (ContinuousLinearMap.id ℝ FourSpace) := by
  let a := Complex.arg (t : ℂ)
  let F : FourSpace → FourSpace := fun x => x + a • basisVector 1
  have hF : HasMFDerivAt I4 I4 F (chartAt FourSpace p p)
      (ContinuousLinearMap.id ℝ FourSpace) :=
    ((hasFDerivAt_id (𝕜 := ℝ) _).add_const (a • basisVector 1)).hasMFDerivAt
  have h := (hasMFDerivAt_quotientMap (F (chartAt FourSpace p p))).comp p
    (hF.comp p (hasMFDerivAt_chartAt p p (mem_chart_source _ _)))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace p).open_source.mem_nhds (mem_chart_source _ _)] with q hq
  change translate t q = quotientMap (chartAt FourSpace p q + a • basisVector 1)
  rw [quotientMap_shift_second, quotientMap_chartAt p q hq]
  simp [a]

theorem mfderiv_translate_eq_id (t : Circle) (p : Torus) :
    mfderiv I4 I4 (translate t) p = ContinuousLinearMap.id ℝ FourSpace :=
  (hasMFDerivAt_translate t p).mfderiv

@[simp] theorem frame_eq_basisVector (p : Torus) (i : Fin 4) :
    frame p i = basisVector i := by
  unfold frame
  rw [coverDifferential_eq_id]
  rfl

@[simp] theorem coframe_eq_coordProj (p : Torus) (i : Fin 4) :
    coframe p i = coordProj i := by
  unfold coframe
  rw [coverDifferential_eq_id]
  simp only [ContinuousLinearMap.inverse_id]
  rfl

@[simp] theorem flatMetric_apply (p : Torus) (v w : FourSpace) :
    flatMetric p v w = ∑ i : Fin 4, v i * w i := by
  simp only [flatMetric, coframe_eq_coordProj, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

theorem flatMetric_invariant : IsInvariantCov2 smoothTranslationAction flatMetric := by
  intro t
  funext p
  ext v w
  change flatMetric (translate t p) (mfderiv I4 I4 (translate t) p v)
    (mfderiv I4 I4 (translate t) p w) = flatMetric p v w
  rw [mfderiv_translate_eq_id, flatMetric_apply, flatMetric_apply]
  rfl

theorem coverCov2_perturbation (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4) :
    coverCov2 (perturbation alpha n) x i j =
      if i = 0 ∧ j = 0 then liftedOscillation alpha n (x 0) else 0 := by
  unfold coverCov2 pullbackCov2
  rw [show mfderiv I4 I4 quotientMap x = ContinuousLinearMap.id ℝ FourSpace from
    coverDifferential_eq_id x]
  simp only [bilinearPullback_apply,
    perturbation, coframe_eq_coordProj, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change oscillatingScalar alpha n (quotientMap x) *
    ((basisVector i) 0 * (basisVector j) 0) = _
  have hs : oscillatingScalar alpha n (quotientMap x) = liftedOscillation alpha n (x 0) := by
    simp only [oscillatingScalar, quotientMap, liftedOscillation, ← Circle.exp_natCast_mul,
      Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  rw [hs]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [basisVector, hi, hj]

end K24.Global.FlatTorus.SmoothProof

/- Frozen geometric prefix copied verbatim from k24-torus-smooth/GeometricSupport.lean;
SHA256 0b06d2f711ce1eceacddc1ba66ce1326be223ce48beee1e5e8037e1d30dda73a. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus.VectorDefectProof
open SmoothProof
attribute [local instance] original_torus_isManifold

@[simp] theorem cov2InChart_eq_coverCov2 (u : RawCov2 Torus) (c : Torus) (x : FourSpace) :
    cov2InChart u c x = coverCov2 u x := by
  change (fun i j => u ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))) = _
  rw [chartAt_symm_eq_quotientMap]
  rfl

@[simp] theorem coverCov2_eq (u : RawCov2 Torus) (x : FourSpace) (i j : Fin 4) :
    coverCov2 u x i j = u (quotientMap x) (basisVector i) (basisVector j) := by
  change u (quotientMap x) (coverDifferential x (basisVector i))
    (coverDifferential x (basisVector j)) = _
  rw [coverDifferential_eq_id]
  rfl

@[simp] theorem cov2InChart_add (u v : RawCov2 Torus) (c : Torus) (x : FourSpace) :
    cov2InChart (u + v) c x = cov2InChart u c x + cov2InChart v c x := by
  rfl

@[simp] theorem cov2FromCoordinates_add (a b : Torus → FourSpace → Mat4) :
    cov2FromCoordinates (fun c x => a c x + b c x) =
      cov2FromCoordinates a + cov2FromCoordinates b := by
  funext p
  ext v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear,
    Finset.sum_add_distrib, add_mul, mul_add]

@[simp] theorem vectorInChart_testVector (c : Torus) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    vectorInChart testVector c x = Real.cos (x 1) • basisVector 0 := by
  change (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x))
    (testVector ((chartAt FourSpace c).symm x)) = _
  rw [mfderiv_chartAt_eq_id c _ ((chartAt FourSpace c).symm.map_source hx)]
  change testVector ((chartAt FourSpace c).symm x) = _
  rw [chartAt_symm_eq_quotientMap]
  simp [testVector, quotientMap, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

@[simp] theorem cov2InChart_flatMetric (c : Torus) (x : FourSpace) (i j : Fin 4) :
    cov2InChart flatMetric c x i j = if i = j then 1 else 0 := by
  rw [cov2InChart_eq_coverCov2, coverCov2_eq, flatMetric_apply]
  simp [basisVector, eq_comm]

@[simp] theorem cov2InChart_perturbation (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) (i j : Fin 4) :
    cov2InChart (perturbation alpha n) c x i j =
      (if i = 0 ∧ j = 0 then 1 else 0) * liftedOscillation alpha n (x 0) := by
  rw [cov2InChart_eq_coverCov2, coverCov2_perturbation]
  split_ifs <;> simp

theorem hasFDerivAt_coord (i : Fin 4) (x : FourSpace) :
    HasFDerivAt (fun x : FourSpace => x i) (coordProj i) x :=
  (coordProj i).hasFDerivAt

@[simp] theorem coordProj_basis (i j : Fin 4) :
    coordProj i (basisVector j) = if i = j then 1 else 0 := by
  simp [coordProj, basisVector]

@[simp] theorem coordDeriv_cos (i k : Fin 4) (x : FourSpace) :
    coordDeriv (fun y : FourSpace => Real.cos (y i)) k x =
      -Real.sin (x i) * (if i = k then 1 else 0) := by
  unfold coordDeriv
  rw [((hasFDerivAt_coord i x).cos).fderiv]
  simp

@[simp] theorem coordDeriv_liftedOscillation (alpha : ℝ) (n : ℕ)
    (i : Fin 4) (x : FourSpace) :
    coordDeriv (fun y : FourSpace => liftedOscillation alpha n (y 0)) i x =
      amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * x 0) *
        (if 0 = i then 1 else 0) := by
  unfold coordDeriv liftedOscillation
  rw [((((hasFDerivAt_coord 0 x).const_mul (n : ℝ)).sin).const_mul
    (amplitude alpha n)).fderiv]
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem coordDeriv_vectorInChart (c : Torus) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i p : Fin 4) :
    coordDeriv (fun y => vectorInChart testVector c y p) i x =
      -Real.sin (x 1) * (if 1 = i then 1 else 0) * (basisVector 0) p := by
  have he : (fun y => vectorInChart testVector c y p) =ᶠ[𝓝 x]
      (fun y : FourSpace => Real.cos (y 1) * (basisVector 0) p) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    rw [vectorInChart_testVector c y hy]
    rfl
  unfold coordDeriv
  rw [he.fderiv_eq]
  rw [(((hasFDerivAt_coord 1 x).cos).mul_const ((basisVector 0) p)).fderiv]
  simp [mul_comm]


def flatLieMatrix (p : Torus) : Mat4 := fun i j =>
  -((p 1 : Circle) : ℂ).im *
    ((basisVector 1) i * (basisVector 0) j + (basisVector 1) j * (basisVector 0) i)

def perturbLieMatrix (alpha : ℝ) (n : ℕ) (p : Torus) : Mat4 := fun i j =>
  ((p 1 : Circle) : ℂ).re * amplitude alpha n * (n : ℝ) * ((p 0 ^ n : Circle) : ℂ).re *
      (basisVector 0) i * (basisVector 0) j +
    oscillatingScalar alpha n p * flatLieMatrix p i j

theorem lieTensorInChart_flatMetric (c : Torus) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    lieTensorInChart testVector flatMetric c x = flatLieMatrix (quotientMap x) := by
  funext i j
  unfold lieTensorInChart
  simp only [cov2InChart_flatMetric, coordDeriv_vectorInChart c x hx]
  have hz (i j p : Fin 4) :
      coordDeriv (fun _ : FourSpace => if i = j then (1 : ℝ) else 0) p x = 0 := by
    simp [coordDeriv]
  simp only [hz, mul_zero, zero_add]
  fin_cases i <;> fin_cases j <;>
    simp [flatLieMatrix, quotientMap, Circle.coe_exp, Complex.exp_ofReal_mul_I_im,
      basisVector, Fin.sum_univ_succ]

theorem lieTensorInChart_perturbation (alpha : ℝ) (n : ℕ) (c : Torus) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    lieTensorInChart testVector (perturbation alpha n) c x =
      perturbLieMatrix alpha n (quotientMap x) := by
  have hd (i j p : Fin 4) :
      coordDeriv (fun y => cov2InChart (perturbation alpha n) c y i j) p x =
        (if i = 0 ∧ j = 0 then 1 else 0) *
        (amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * x 0) *
          (if 0 = p then 1 else 0)) := by
    simp only [cov2InChart_perturbation]
    by_cases h : i = 0 ∧ j = 0
    · simp only [if_pos h, one_mul]
      exact coordDeriv_liftedOscillation alpha n p x
    · simp [h, coordDeriv]
  funext i j
  unfold lieTensorInChart
  simp_rw [hd]
  simp only [cov2InChart_perturbation, coordDeriv_vectorInChart c x hx,
    vectorInChart_testVector c x hx]
  simp only [perturbLieMatrix, flatLieMatrix, oscillatingScalar, quotientMap,
    ← Circle.exp_natCast_mul, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, liftedOscillation]
  fin_cases i <;> fin_cases j <;>
    simp [basisVector] <;> ring

theorem cov2FromCoordinates_of_matrix (A : Torus → Mat4)
    (f : Torus → FourSpace → Mat4)
    (hf : ∀ c x, x ∈ (chartAt FourSpace c).target → f c x = A (quotientMap x)) :
    cov2FromCoordinates f = fun p => matrixToBilinear (A p) := by
  funext p
  unfold cov2FromCoordinates cov2FromChartAt
  rw [mfderiv_chartAt_eq_id p p (mem_chart_source _ _),
    hf p _ ((chartAt FourSpace p).map_source (mem_chart_source _ _)),
    quotientMap_chartAt p p (mem_chart_source _ _)]
  ext v w
  rfl

theorem lieTensor_flatMetric :
    lieTensor testVector flatMetric = fun p => matrixToBilinear (flatLieMatrix p) :=
  cov2FromCoordinates_of_matrix _ _ lieTensorInChart_flatMetric

theorem lieTensor_perturbation (alpha : ℝ) (n : ℕ) :
    lieTensor testVector (perturbation alpha n) =
      fun p => matrixToBilinear (perturbLieMatrix alpha n p) :=
  cov2FromCoordinates_of_matrix _ _ (lieTensorInChart_perturbation alpha n)


theorem coordDeriv_add (f g : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    coordDeriv (fun y => f y + g y) i x = coordDeriv f i x + coordDeriv g i x := by
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (basisVector i))
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

theorem lieTensor_add (Y : RawVector Torus) (u v : RawCov2 Torus)
    (hu : ∀ c i j, Differentiable ℝ (fun x => cov2InChart u c x i j))
    (hv : ∀ c i j, Differentiable ℝ (fun x => cov2InChart v c x i j)) :
    lieTensor Y (u + v) = lieTensor Y u + lieTensor Y v := by
  unfold lieTensor
  rw [← cov2FromCoordinates_add]
  congr 1
  funext c x i j
  simp only [lieTensorInChart, cov2InChart_add, Matrix.add_apply]
  simp_rw [coordDeriv_add _ _ _ (hu c i j x) (hv c i j x)]
  simp only [mul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem differentiable_cov2InChart_flatMetric (c : Torus) (i j : Fin 4) :
    Differentiable ℝ (fun x => cov2InChart flatMetric c x i j) := by
  simp only [cov2InChart_flatMetric]
  exact differentiable_const _

theorem differentiable_cov2InChart_perturbation (alpha : ℝ) (n : ℕ)
    (c : Torus) (i j : Fin 4) :
    Differentiable ℝ (fun x => cov2InChart (perturbation alpha n) c x i j) := by
  simp only [cov2InChart_perturbation, liftedOscillation]
  fun_prop

@[simp] theorem matrixToBilinear_basis (A : Mat4) (i j : Fin 4) :
    matrixToBilinear A (basisVector i) (basisVector j) = A i j := by
  simp [matrixToBilinear, coordProj_basis]

theorem cov2InChart_matrix_section (A : Torus → Mat4) (c : Torus) (x : FourSpace)
    (i j : Fin 4) :
    cov2InChart (fun p => matrixToBilinear (A p)) c x i j = A (quotientMap x) i j := by
  rw [cov2InChart_eq_coverCov2, coverCov2_eq]
  change matrixToBilinear (A (quotientMap x)) (basisVector i) (basisVector j) = _
  exact matrixToBilinear_basis _ i j

theorem differentiable_cov2InChart_lie_flatMetric (c : Torus) (i j : Fin 4) :
    Differentiable ℝ (fun x => cov2InChart (lieTensor testVector flatMetric) c x i j) := by
  rw [lieTensor_flatMetric]
  simp only [cov2InChart_matrix_section, flatLieMatrix, quotientMap, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im]
  fun_prop

theorem differentiable_cov2InChart_lie_perturbation (alpha : ℝ) (n : ℕ)
    (c : Torus) (i j : Fin 4) :
    Differentiable ℝ
      (fun x => cov2InChart (lieTensor testVector (perturbation alpha n)) c x i j) := by
  rw [lieTensor_perturbation]
  simp only [cov2InChart_matrix_section, perturbLieMatrix, flatLieMatrix, oscillatingScalar,
    quotientMap, ← Circle.exp_natCast_mul, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
  fun_prop

@[simp] theorem inverseMetricInChart_flatMetric (c : Torus) (x : FourSpace) :
    inverseMetricInChart flatMetric c x = 1 := by
  have h : cov2InChart flatMetric c x = 1 := by
    ext i j
    simp only [cov2InChart_flatMetric, Matrix.one_apply]
  simp [inverseMetricInChart, h]

@[simp] theorem metricTraceInChart_add (g u v : RawCov2 Torus) (c : Torus) :
    metricTraceInChart g (u + v) c =
      fun x => metricTraceInChart g u c x + metricTraceInChart g v c x := by
  funext x
  simp [metricTraceInChart, mul_add, Finset.sum_add_distrib]

theorem differentiable_trace_flatMetric (u : RawCov2 Torus)
    (hu : ∀ c i j, Differentiable ℝ (fun x => cov2InChart u c x i j)) (c : Torus) :
    Differentiable ℝ (metricTraceInChart flatMetric u c) := by
  unfold metricTraceInChart
  simp only [inverseMetricInChart_flatMetric]
  exact Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ =>
    (hu c i j).const_mul _

@[simp] theorem covectorFromCoordinates_add (a b : Torus → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (fun c x => a c x + b c x) =
      covectorFromCoordinates a + covectorFromCoordinates b := by
  funext p
  ext v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    Finset.sum_add_distrib, add_mul]

theorem bianchi_add (u v : RawCov2 Torus)
    (hu : ∀ c i j, Differentiable ℝ (fun x => cov2InChart u c x i j))
    (hv : ∀ c i j, Differentiable ℝ (fun x => cov2InChart v c x i j)) :
    bianchi flatMetric (u + v) = bianchi flatMetric u + bianchi flatMetric v := by
  unfold bianchi
  rw [← covectorFromCoordinates_add]
  congr 1
  funext c x j
  have hn (a b d : Fin 4) :
      nablaTensorInChart flatMetric (u + v) c x a b d =
        nablaTensorInChart flatMetric u c x a b d +
        nablaTensorInChart flatMetric v c x a b d := by
    simp only [nablaTensorInChart, cov2InChart_add, Matrix.add_apply,
      coordDeriv_add _ _ _ (hu c b d x) (hv c b d x), mul_add,
      Finset.sum_add_distrib]
    ring
  simp only [bianchiInChart, hn, metricTraceInChart_add,
    coordDeriv_add _ _ _ (differentiable_trace_flatMetric u hu c x)
      (differentiable_trace_flatMetric v hv c x),
    mul_add, Finset.sum_add_distrib, Pi.add_apply]
  ring

theorem actualVectorDifference_eq_projectedDefect (rho : CircleAction Torus)
    (alpha : ℝ) (n : ℕ) :
    actualVectorDifference rho alpha n = projectedDefect rho alpha n := by
  unfold actualVectorDifference projectedDefect unprojectedDefect vectorOperator nearbyMetric
  rw [lieTensor_add testVector flatMetric (perturbation alpha n)
    differentiable_cov2InChart_flatMetric (differentiable_cov2InChart_perturbation alpha n)]
  rw [bianchi_add (lieTensor testVector flatMetric) (lieTensor testVector (perturbation alpha n))
    differentiable_cov2InChart_lie_flatMetric (differentiable_cov2InChart_lie_perturbation alpha n)]
  rw [add_sub_cancel_left]

end K24.Global.FlatTorus.VectorDefectProof

namespace K24.Global.FlatTorus.DefectFormulaProof
open SmoothProof VectorDefectProof
attribute [local instance] original_torus_isManifold

/-- The only diagonal coefficient of the actual Lie derivative on the cover. -/
def lie00 (alpha : ℝ) (n : ℕ) (x : FourSpace) : ℝ :=
  Real.cos (x 1) * amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * x 0)

/-- The two equal off-diagonal coefficients of the actual Lie derivative. -/
def lie01 (alpha : ℝ) (n : ℕ) (x : FourSpace) : ℝ :=
  -Real.sin (x 1) * amplitude alpha n * Real.sin ((n : ℝ) * x 0)

theorem cov2InChart_lie_perturbation (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) (i j : Fin 4) :
    cov2InChart (lieTensor testVector (perturbation alpha n)) c x i j =
      if i = 0 ∧ j = 0 then lie00 alpha n x
      else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then lie01 alpha n x else 0 := by
  rw [lieTensor_perturbation, cov2InChart_matrix_section]
  simp only [perturbLieMatrix, flatLieMatrix, oscillatingScalar, quotientMap,
    ← Circle.exp_natCast_mul, Circle.coe_exp, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re]
  fin_cases i <;> fin_cases j <;> simp [basisVector, lie00, lie01] <;> ring

@[simp] theorem christoffelInChart_flatMetric (c : Torus) (x : FourSpace)
    (k i j : Fin 4) :
    christoffelInChart flatMetric c x k i j = 0 := by
  simp [christoffelInChart, cov2InChart_flatMetric, coordDeriv]

@[simp] theorem nablaTensorInChart_flatMetric (u : RawCov2 Torus) (c : Torus)
    (x : FourSpace) (a b d : Fin 4) :
    nablaTensorInChart flatMetric u c x a b d =
      coordDeriv (fun y => cov2InChart u c y b d) a x := by
  simp [nablaTensorInChart]

theorem metricTraceInChart_lie_perturbation (alpha : ℝ) (n : ℕ) (c : Torus) :
    metricTraceInChart flatMetric (lieTensor testVector (perturbation alpha n)) c =
      lie00 alpha n := by
  funext x
  simp [metricTraceInChart, cov2InChart_lie_perturbation, Fin.sum_univ_succ]

theorem coordDeriv_lie00 (alpha : ℝ) (n : ℕ) (a : Fin 4) (x : FourSpace) :
    coordDeriv (lie00 alpha n) a x =
      -Real.sin (x 1) * amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * x 0) *
        (if 1 = a then 1 else 0) -
      Real.cos (x 1) * amplitude alpha n * (n : ℝ) ^ 2 * Real.sin ((n : ℝ) * x 0) *
        (if 0 = a then 1 else 0) := by
  have h := (((((hasFDerivAt_coord 1 x).cos).mul_const (amplitude alpha n)).mul_const (n : ℝ)).mul
    (((hasFDerivAt_coord 0 x).const_mul (n : ℝ)).cos)).fderiv
  exact (congrArg (fun L : FourSpace →L[ℝ] ℝ => L (basisVector a)) h).trans (by
    simp only [add_apply, smul_apply,
      smul_eq_mul, coordProj_basis]
    split_ifs <;> ring)

theorem coordDeriv_lie01 (alpha : ℝ) (n : ℕ) (a : Fin 4) (x : FourSpace) :
    coordDeriv (lie01 alpha n) a x =
      -Real.cos (x 1) * amplitude alpha n * Real.sin ((n : ℝ) * x 0) *
        (if 1 = a then 1 else 0) -
      Real.sin (x 1) * amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * x 0) *
        (if 0 = a then 1 else 0) := by
  have h := (((((hasFDerivAt_coord 1 x).sin).neg).mul_const (amplitude alpha n)).mul
    (((hasFDerivAt_coord 0 x).const_mul (n : ℝ)).sin)).fderiv
  exact (congrArg (fun L : FourSpace →L[ℝ] ℝ => L (basisVector a)) h).trans (by
    simp only [add_apply, smul_apply,
      neg_apply, Pi.neg_apply, smul_eq_mul, coordProj_basis]
    split_ifs <;> ring)

theorem deriv_liftedOscillation (alpha : ℝ) (n : ℕ) :
    deriv (liftedOscillation alpha n) =
      fun r => amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * r) := by
  funext r
  exact ((((hasDerivAt_id r).const_mul (n : ℝ)).sin).const_mul
    (amplitude alpha n)).deriv.trans (by simp only [id_eq]; ring)

theorem deriv_deriv_liftedOscillation (alpha : ℝ) (n : ℕ) :
    deriv (deriv (liftedOscillation alpha n)) =
      fun r => -(amplitude alpha n * (n : ℝ) ^ 2 * Real.sin ((n : ℝ) * r)) := by
  rw [deriv_liftedOscillation]
  funext r
  exact ((((hasDerivAt_id r).const_mul (n : ℝ)).cos).const_mul
    (amplitude alpha n * (n : ℝ))).deriv.trans (by simp only [id_eq]; ring)

theorem expectedDefectCoefficients_explicit (alpha : ℝ) (n : ℕ) (x : FourSpace) (j : Fin 4) :
    expectedDefectCoefficients alpha n x j =
      if j = 0 then Real.cos (x 1) *
        (amplitude alpha n * Real.sin ((n : ℝ) * x 0) +
          (1 / 2 : ℝ) * (amplitude alpha n * (n : ℝ) ^ 2 * Real.sin ((n : ℝ) * x 0)))
      else if j = 1 then (1 / 2 : ℝ) * Real.sin (x 1) *
        (amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * x 0)) else 0 := by
  unfold expectedDefectCoefficients
  rw [deriv_deriv_liftedOscillation, deriv_liftedOscillation]
  simp [liftedOscillation]

@[simp] theorem coordDeriv_const (r : ℝ) (i : Fin 4) (x : FourSpace) :
    coordDeriv (fun _ : FourSpace => r) i x = 0 := by
  simp [coordDeriv]

theorem bianchiInChart_lie_perturbation (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) :
    bianchiInChart flatMetric (lieTensor testVector (perturbation alpha n)) c x =
      expectedDefectCoefficients alpha n x := by
  funext j
  simp only [bianchiInChart, inverseMetricInChart_flatMetric,
    nablaTensorInChart_flatMetric, metricTraceInChart_lie_perturbation]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  simp only [cov2InChart_lie_perturbation]
  fin_cases j <;>
    simp [Fin.sum_univ_succ, coordDeriv_lie00, coordDeriv_lie01,
      expectedDefectCoefficients_explicit] <;> ring


/-- Global coefficients of the actual defect in the frozen flat coframe. -/
def rawDefectCoefficients (alpha : ℝ) (n : ℕ) (p : Torus) : Fin 4 → ℝ := fun j =>
  if j = 0 then ((p 1 : Circle) : ℂ).re *
    (amplitude alpha n * ((p 0 ^ n : Circle) : ℂ).im +
      (1 / 2 : ℝ) * (amplitude alpha n * (n : ℝ) ^ 2 * ((p 0 ^ n : Circle) : ℂ).im))
  else if j = 1 then (1 / 2 : ℝ) * ((p 1 : Circle) : ℂ).im *
    (amplitude alpha n * (n : ℝ) * ((p 0 ^ n : Circle) : ℂ).re) else 0

theorem expectedDefectCoefficients_eq_raw (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    expectedDefectCoefficients alpha n x = rawDefectCoefficients alpha n (quotientMap x) := by
  funext j
  rw [expectedDefectCoefficients_explicit]
  simp only [rawDefectCoefficients, quotientMap, ← Circle.exp_natCast_mul, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]

theorem unprojectedDefect_eq_raw (alpha : ℝ) (n : ℕ) :
    unprojectedDefect alpha n =
      fun p => coefficientsToCovector (rawDefectCoefficients alpha n p) := by
  unfold unprojectedDefect bianchi
  funext p
  unfold covectorFromCoordinates covectorFromChartAt
  rw [mfderiv_chartAt_eq_id p p (mem_chart_source _ _),
    bianchiInChart_lie_perturbation, expectedDefectCoefficients_eq_raw,
    quotientMap_chartAt p p (mem_chart_source _ _)]
  ext v
  rfl

@[simp] theorem coverCovector_eq (u : RawCovector Torus) (x : FourSpace) (j : Fin 4) :
    coverCovector u x j = u (quotientMap x) (basisVector j) := by
  change u (quotientMap x) (coverDifferential x (basisVector j)) = _
  rw [coverDifferential_eq_id]
  rfl

@[simp] theorem coefficientsToCovector_basis (a : Fin 4 → ℝ) (j : Fin 4) :
    coefficientsToCovector a (basisVector j) = a j := by
  simp [coefficientsToCovector, coordProj_basis]

theorem coverCovector_unprojectedDefect (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    coverCovector (unprojectedDefect alpha n) x = expectedDefectCoefficients alpha n x := by
  funext j
  rw [unprojectedDefect_eq_raw, coverCovector_eq]
  change coefficientsToCovector (rawDefectCoefficients alpha n (quotientMap x))
    (basisVector j) = _
  rw [coefficientsToCovector_basis, expectedDefectCoefficients_eq_raw]

end K24.Global.FlatTorus.DefectFormulaProof
namespace K24.Global.FlatTorus.DefectHaarProof

open MeasureTheory SmoothProof DefectFormulaProof

theorem actionPullbackCovector_unprojectedDefect
    (rho : CircleAction Torus) (hrho : rho.act = translate)
    (alpha : ℝ) (n : ℕ) (t : Circle) (p : Torus) :
    actionPullbackCovector rho t (unprojectedDefect alpha n) p =
      coefficientsToCovector (rawDefectCoefficients alpha n (translate t p)) := by
  dsimp only [actionPullbackCovector, pullbackCovector]
  rw [hrho, mfderiv_translate_eq_id, unprojectedDefect_eq_raw]
  rfl

theorem covectorInChart_pullback_unprojectedDefect
    (rho : CircleAction Torus) (hrho : rho.act = translate)
    (alpha : ℝ) (n : ℕ) (t : Circle) (c : Torus) (x : FourSpace) (i : Fin 4) :
    covectorInChart (actionPullbackCovector rho t (unprojectedDefect alpha n)) c x i =
      rawDefectCoefficients alpha n (translate t (quotientMap x)) i := by
  dsimp only [covectorInChart]
  rw [chartAt_symm_eq_quotientMap]
  change actionPullbackCovector rho t (unprojectedDefect alpha n) (quotientMap x)
    (coverDifferential x (basisVector i)) = _
  rw [coverDifferential_eq_id, actionPullbackCovector_unprojectedDefect rho hrho]
  exact coefficientsToCovector_basis _ _

theorem rawDefectCoefficients_translate_continuous
    (alpha : ℝ) (n : ℕ) (p : Torus) (i : Fin 4) :
    Continuous (fun t : Circle => rawDefectCoefficients alpha n (translate t p) i) := by
  by_cases h0 : i = 0
  · simp only [rawDefectCoefficients, h0, ↓reduceIte, translate]
    norm_num
    fun_prop
  · by_cases h1 : i = 1
    · simp only [rawDefectCoefficients, h1, ↓reduceIte, translate]
      norm_num
      fun_prop
    · simp only [rawDefectCoefficients, h0, h1, ↓reduceIte]
      exact continuous_const

theorem rawDefectCoefficients_translate_neg
    (alpha : ℝ) (n : ℕ) (p : Torus) (i : Fin 4) (t : Circle) :
    rawDefectCoefficients alpha n (translate ((-1) * t) p) i =
      -rawDefectCoefficients alpha n (translate t p) i := by
  by_cases h0 : i = 0
  · simp [rawDefectCoefficients, h0, translate, Circle.coe_mul]
    ring
  · by_cases h1 : i = 1
    · simp [rawDefectCoefficients, h1, translate, Circle.coe_mul]
      ring
    · simp [rawDefectCoefficients, h0, h1]

theorem unprojectedDefect_haarIntegrable
    (rho : CircleAction Torus) (hrho : rho.act = translate) (alpha : ℝ) (n : ℕ) :
    CovectorHaarIntegrable rho (unprojectedDefect alpha n) := by
  intro c x _hx i
  simp_rw [covectorInChart_pullback_unprojectedDefect rho hrho]
  exact Continuous.integrable_of_hasCompactSupport
    (rawDefectCoefficients_translate_continuous alpha n (quotientMap x) i)
    (HasCompactSupport.of_compactSpace _)

theorem unprojectedDefect_integral_zero
    (rho : CircleAction Torus) (hrho : rho.act = translate) (alpha : ℝ) (n : ℕ)
    (c : Torus) (x : FourSpace) (i : Fin 4) :
    (∫ t : Circle, covectorInChart (actionPullbackCovector rho t
      (unprojectedDefect alpha n)) c x i ∂circleHaar) = 0 := by
  have : circleHaar.IsMulLeftInvariant := by
    unfold circleHaar
    infer_instance
  simp_rw [covectorInChart_pullback_unprojectedDefect rho hrho]
  exact MeasureTheory.integral_eq_zero_of_mul_left_eq_neg
    (g := (-1 : Circle)) (rawDefectCoefficients_translate_neg alpha n (quotientMap x) i)

theorem unprojectedDefect_average_zero
    (rho : CircleAction Torus) (hrho : rho.act = translate) (alpha : ℝ) (n : ℕ) :
    covectorPi0 rho (unprojectedDefect alpha n) = 0 := by
  funext p
  simp [covectorPi0, covectorFromCoordinates, covectorFromChartAt,
    unprojectedDefect_integral_zero rho hrho, coefficientsToCovector]

theorem projectedDefect_eq_unprojectedDefect
    (rho : CircleAction Torus) (hrho : rho.act = translate) (alpha : ℝ) (n : ℕ) :
    projectedDefect rho alpha n = unprojectedDefect alpha n := by
  simp [projectedDefect, covectorPiPerp, unprojectedDefect_average_zero rho hrho]

end K24.Global.FlatTorus.DefectHaarProof
end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise
namespace K24.Global.OscillationBounds
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem holder_zero_of_norm_bound {X : Type*} [PseudoEMetricSpace X]
    (f : X → V) (B : ℝ≥0) (hB : ∀ x, ‖f x‖₊ ≤ B) :
    HolderWith (2 * B) 0 f := by
  intro x y
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
  rw [edist_nndist]
  apply ENNReal.coe_le_coe.mpr
  apply (NNReal.coe_le_coe).mp
  rw [coe_nndist, dist_eq_norm]
  calc
    _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
    _ ≤ (B : ℝ) + B := add_le_add (hB x) (hB y)
    _ = _ := by simp [two_mul]

omit [NormedSpace ℝ V] in
theorem holder_of_norm_lipschitz {X : Type*} [PseudoEMetricSpace X]
    (f : X → V) (B L alpha : ℝ≥0) (ha : alpha ≤ 1)
    (hB : ∀ x, ‖f x‖₊ ≤ B) (hL : LipschitzWith L f) :
    HolderWith ((2 * B) ^ ((1 - alpha : ℝ≥0) : ℝ) * L ^ (alpha : ℝ)) alpha f := by
  have h := (holder_zero_of_norm_bound f B hB).interpolate
    (t₁ := 1 - alpha) (t₂ := alpha) hL.holderWith (tsub_add_cancel_of_le ha)
  simpa using h

theorem coordinateHolderENorm_le_of_derivative_bounds
    (f : E → V) (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (hf : ContDiff ℝ (k + 1) f) (B : ℕ → ℝ≥0)
    (hB : ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖₊ ≤ B j) :
    coordinateHolderENorm k alpha Set.univ f ≤
      (↑(∑ j ∈ Finset.range (k + 1), B j) : ℝ≥0∞) +
      (↑((2 * B k) ^ ((1 - alpha : ℝ≥0) : ℝ) * B (k + 1) ^ (alpha : ℝ)) : ℝ≥0∞) := by
  have hL : LipschitzWith (B (k + 1)) (iteratedFDeriv ℝ k f) := by
    apply lipschitzWith_of_nnnorm_fderiv_le
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k))
    intro x
    change ‖fderiv ℝ (iteratedFDeriv ℝ k f) x‖ ≤ (B (k + 1) : ℝ)
    rw [norm_fderiv_iteratedFDeriv]
    exact hB (k + 1) le_rfl x
  have hH := holder_of_norm_lipschitz (iteratedFDeriv ℝ k f) (B k)
    (B (k + 1)) alpha ha (hB k (Nat.le_succ k)) hL
  unfold coordinateHolderENorm
  apply add_le_add
  · simp only [ENNReal.ofNNReal_finsetSum]
    apply Finset.sum_le_sum
    intro j hj
    unfold derivativeENorm
    apply iSup_le
    intro x
    simp only [iteratedFDerivWithin_univ]
    exact_mod_cast hB j (by have := Finset.mem_range.mp hj; omega) x
  · simp only [iteratedFDerivWithin_univ]
    have hHs : HolderWith
        ((2 * B k) ^ ((1 - alpha : ℝ≥0) : ℝ) * B (k + 1) ^ (alpha : ℝ))
        alpha (fun x : (Set.univ : Set E) => iteratedFDeriv ℝ k f x) :=
      fun x y => hH x y
    exact hHs.eHolderNorm_le


theorem norm_iteratedFDeriv_sin_linear (l : E →L[ℝ] ℝ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => Real.sin (l x)) x‖ ≤ ‖l‖ ^ j := by
  rw [show (fun x => Real.sin (l x)) = Real.sin ∘ l from rfl,
    l.iteratedFDeriv_comp_right (Real.contDiff_sin : ContDiff ℝ j Real.sin) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j Real.sin (l x)‖ * ∏ _ : Fin j, ‖l‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * ‖l‖ ^ j := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      gcongr
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_sin_le_one j (l x)
    _ = _ := one_mul _

theorem norm_iteratedFDeriv_sin_linear_smul
    (l : E →L[ℝ] ℝ) (v : V) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => Real.sin (l x) • v) x‖ ≤ ‖v‖ * ‖l‖ ^ j := by
  have hf : ContDiff ℝ j (fun x => Real.sin (l x)) := Real.contDiff_sin.comp l.contDiff
  rw [iteratedFDeriv_smul_const_apply hf.contDiffAt]
  calc
    _ ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight v‖ *
        ‖iteratedFDeriv ℝ j (fun x => Real.sin (l x)) x‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ = ‖v‖ * ‖iteratedFDeriv ℝ j (fun x => Real.sin (l x)) x‖ := by
      simp [ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_sin_linear l j x) (norm_nonneg _)


theorem coordinateHolderENorm_sin_linear_smul
    (l : E →L[ℝ] ℝ) (v : V) (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    BigHolderOn k alpha Set.univ (fun x => Real.sin (l x) • v) := by
  have hf : ContDiff ℝ (k + 1) (fun x => Real.sin (l x) • v) :=
    (Real.contDiff_sin.comp l.contDiff).smul contDiff_const
  refine ⟨hf.of_le (by exact_mod_cast Nat.le_succ k) |>.contDiffOn, ?_⟩
  have h := coordinateHolderENorm_le_of_derivative_bounds _ k alpha ha hf
    (fun j => ‖v‖₊ * ‖l‖₊ ^ j) (by
      intro j hj x
      exact_mod_cast norm_iteratedFDeriv_sin_linear_smul l v j x)
  exact lt_of_le_of_lt h (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩)


end K24.Global.OscillationBounds
end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise
namespace K24.Global.DefectNormProof
open FlatTorus OscillationBounds FlatTorus.DefectFormulaProof
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem bigHolder_sine_sum (l m : E →L[ℝ] ℝ) (v w : V)
    (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    BigHolderOn k alpha Set.univ (fun x => Real.sin (l x) • v + Real.sin (m x) • w) := by
  have hf (i : ℕ∞ω) : ContDiff ℝ i (fun x => Real.sin (l x) • v) :=
    (Real.contDiff_sin.comp l.contDiff).smul contDiff_const
  have hg (i : ℕ∞ω) : ContDiff ℝ i (fun x => Real.sin (m x) • w) :=
    (Real.contDiff_sin.comp m.contDiff).smul contDiff_const
  refine ⟨((hf k).add (hg k)).contDiffOn, ?_⟩
  have hb := coordinateHolderENorm_le_of_derivative_bounds _ k alpha ha
    ((hf (k + 1)).add (hg (k + 1)))
    (fun j => ‖v‖₊ * ‖l‖₊ ^ j + ‖w‖₊ * ‖m‖₊ ^ j) (by
      intro j hj x
      apply (NNReal.coe_le_coe).mp
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
      rw [fun_iteratedFDeriv_add_apply ((hf j).contDiffAt) ((hg j).contDiffAt)]
      exact (norm_add_le _ _).trans (add_le_add
        (norm_iteratedFDeriv_sin_linear_smul l v j x)
        (norm_iteratedFDeriv_sin_linear_smul m w j x)))
  exact lt_of_le_of_lt hb (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩)

def wavePlus (alpha : ℝ) (n : ℕ) : Fin 4 → ℝ := fun j =>
  if j = 0 then amplitude alpha n * (1 + (n : ℝ)^2 / 2) / 2
  else if j = 1 then amplitude alpha n * n / 4 else 0

def waveMinus (alpha : ℝ) (n : ℕ) : Fin 4 → ℝ := fun j =>
  if j = 0 then amplitude alpha n * (1 + (n : ℝ)^2 / 2) / 2
  else if j = 1 then -(amplitude alpha n * n / 4) else 0

theorem expectedDefect_sine_decomposition (alpha : ℝ) (n : ℕ) :
    expectedDefectCoefficients alpha n = fun x =>
      Real.sin ((((n : ℝ) • coordProj 0) + coordProj 1) x) • wavePlus alpha n +
      Real.sin ((((n : ℝ) • coordProj 0) - coordProj 1) x) • waveMinus alpha n := by
  funext x j
  rw [expectedDefectCoefficients_explicit]
  simp only [add_apply, sub_apply, smul_apply,
    coordProj, PiLp.proj_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Real.sin_add, Real.sin_sub, wavePlus, waveMinus]
  split_ifs <;> ring

theorem expectedDefect_bigHolder (alpha : HolderExponent) (n k : ℕ) :
    BigHolderOn k alpha.value Set.univ (expectedDefectCoefficients alpha.value n) := by
  rw [expectedDefect_sine_decomposition]
  exact bigHolder_sine_sum _ _ _ _ k alpha.value alpha.lessThanOne.le

theorem actual_unprojectedDefect_finite (alpha : HolderExponent) (n k : ℕ) :
    covectorHolderENorm k alpha.value (unprojectedDefect alpha.value n) < ⊤ := by
  unfold covectorHolderENorm
  have he : coverCovector (unprojectedDefect alpha.value n) = expectedDefectCoefficients alpha.value n :=
    funext (coverCovector_unprojectedDefect alpha.value n)
  rw [he]
  exact (expectedDefect_bigHolder alpha n k).2


theorem expectedDefect_contDiff (alpha : ℝ) (n : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (expectedDefectCoefficients alpha n) := by
  rw [expectedDefect_sine_decomposition]
  exact ((Real.contDiff_sin.comp (((n : ℝ) • coordProj 0) + coordProj 1).contDiff).smul
    contDiff_const).add
    ((Real.contDiff_sin.comp (((n : ℝ) • coordProj 0) - coordProj 1).contDiff).smul contDiff_const)

theorem derivative_probe_expected (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    (iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha n) Set.univ x)
        (fun _ : Fin 1 => basisVector 0) 0 =
      amplitude alpha n * (n : ℝ) * (1 + (n : ℝ)^2 / 2) *
        Real.cos ((n : ℝ) * x 0) * Real.cos (x 1) := by
  let l := ((n : ℝ) • coordProj 0) + coordProj 1
  let m := ((n : ℝ) • coordProj 0) - coordProj 1
  have hd := (((l.hasFDerivAt (x := x)).sin).smul_const (wavePlus alpha n)).add
    (((m.hasFDerivAt (x := x)).sin).smul_const (waveMinus alpha n))
  rw [expectedDefect_sine_decomposition,
    iteratedFDerivWithin_one_apply (uniqueDiffWithinAt_univ), fderivWithin_univ]
  change (fderiv ℝ ((fun y => Real.sin (l y) • wavePlus alpha n) +
    fun y => Real.sin (m y) • waveMinus alpha n) x) (basisVector 0) 0 = _
  rw [hd.fderiv]
  simp only [l, m, add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordProj, PiLp.proj_apply,
    basisVector, wavePlus, waveMinus, Real.cos_add, Real.cos_sub]
  norm_num
  ring

theorem derivative_probe_norm_le
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => FourSpace) (Fin 4 → ℝ)) :
    |D (fun _ => basisVector 0) 0| ≤ ‖D‖ := by
  calc
    _ ≤ ‖D (fun _ => basisVector 0)‖ := norm_le_pi_norm _ 0
    _ ≤ ‖D‖ * ∏ _ : Fin 1, ‖basisVector 0‖ := D.le_opNorm _
    _ = _ := by simp [basisVector, PiLp.norm_single]


def comparisonPoint (n : ℕ) : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0

theorem comparisonPoint_distance (n : ℕ) :
    dist (0 : FourSpace) (comparisonPoint n) = Real.pi / (n : ℝ) := by
  rw [dist_zero_left, comparisonPoint, norm_smul]
  simp [basisVector, PiLp.norm_single,
    Real.norm_of_nonneg (div_nonneg Real.pi_pos.le (Nat.cast_nonneg n))]

theorem derivative_difference_lower (alpha : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (-alpha) ≤
      ‖iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha n) Set.univ 0 -
        iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha n) Set.univ (comparisonPoint n)‖ := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hphase : (n : ℝ) * (Real.pi / (n : ℝ)) = Real.pi := by field_simp
  have hdiff :
      (iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha n) Set.univ 0 -
        iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha n) Set.univ (comparisonPoint n))
        (fun _ : Fin 1 => basisVector 0) 0 = amplitude alpha n * n * (2 + (n : ℝ)^2) := by
    rw [sub_apply, Pi.sub_apply,
      derivative_probe_expected, derivative_probe_expected]
    simp [comparisonPoint, basisVector, hphase]
    ring
  have ha : 0 ≤ amplitude alpha n := Real.rpow_nonneg hn0.le _
  have hp : amplitude alpha n * (n : ℝ)^3 = (n : ℝ)^(-alpha) := by
    unfold amplitude
    change (n : ℝ)^(-(3+alpha)) * (n : ℝ)^3 = _
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    norm_num
  have he := derivative_probe_norm_le
    (iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha n) Set.univ 0 -
      iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha n) Set.univ (comparisonPoint n))
  rw [hdiff, abs_of_nonneg (by positivity)] at he
  rw [← hp]
  exact (by nlinarith [mul_nonneg ha hn0.le] :
    amplitude alpha n * (n : ℝ)^3 ≤ amplitude alpha n * n * (2 + (n : ℝ)^2)).trans he

theorem expectedDefect_holder_constant_lower (alpha : HolderExponent) (n : ℕ)
    (hn : 1 ≤ n) (C : ℝ≥0)
    (hC : HolderWith C alpha.value (fun x : (Set.univ : Set FourSpace) =>
      iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha.value n) Set.univ x)) :
    Real.pi ^ (-(alpha.value : ℝ)) ≤ (C : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpN : 0 < (n : ℝ) ^ (alpha.value : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hpPi : 0 < Real.pi ^ (alpha.value : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have hdist := hC.dist_le (⟨0, Set.mem_univ _⟩ : (Set.univ : Set FourSpace))
    (⟨comparisonPoint n, Set.mem_univ _⟩ : (Set.univ : Set FourSpace))
  rw [Subtype.dist_eq, comparisonPoint_distance] at hdist
  have hbound : (n : ℝ)^(-(alpha.value : ℝ)) ≤
      C * (Real.pi / (n : ℝ)) ^ (alpha.value : ℝ) := by
    apply (derivative_difference_lower alpha.value n hn).trans
    simpa only [dist_eq_norm] using hdist
  rw [Real.rpow_neg hn0.le, Real.div_rpow Real.pi_pos.le hn0.le] at hbound
  have hdiv : (1 : ℝ) / (n : ℝ) ^ (alpha.value : ℝ) ≤
      (C * Real.pi ^ (alpha.value : ℝ)) / (n : ℝ) ^ (alpha.value : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using hbound
  have hmul := (div_le_div_iff_of_pos_right hpN).mp hdiv
  rw [Real.rpow_neg Real.pi_pos.le, ← one_div]
  exact (div_le_iff₀ hpPi).mpr hmul

theorem expectedDefect_C1_norm_lower (alpha : HolderExponent) (n : ℕ) (hn : 1 ≤ n) :
    Real.pi ^ (-(alpha.value : ℝ)) ≤
      (coordinateHolderENorm 1 alpha.value Set.univ (expectedDefectCoefficients alpha.value n)).toReal := by
  have hh : ENNReal.ofReal (Real.pi ^ (-(alpha.value : ℝ))) ≤
      eHolderNorm alpha.value (fun x : (Set.univ : Set FourSpace) =>
        iteratedFDerivWithin ℝ 1 (expectedDefectCoefficients alpha.value n) Set.univ x) := by
    unfold eHolderNorm
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    exact ENNReal.ofReal_le_coe.mpr (expectedDefect_holder_constant_lower alpha n hn C hC)
  have hc : ENNReal.ofReal (Real.pi ^ (-(alpha.value : ℝ))) ≤
      coordinateHolderENorm 1 alpha.value Set.univ (expectedDefectCoefficients alpha.value n) :=
    hh.trans (le_add_left le_rfl)
  have hfin := (expectedDefect_bigHolder alpha n 1).2
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg Real.pi_pos.le _)] using
    ENNReal.toReal_mono hfin.ne hc


theorem actual_unprojectedDefect_C1_norm_lower (alpha : HolderExponent) (n : ℕ)
    (hn : 1 ≤ n) :
    Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
      covectorHolderNorm 1 alpha.value (unprojectedDefect alpha.value n) := by
  unfold covectorHolderNorm covectorHolderENorm
  have he : coverCovector (unprojectedDefect alpha.value n) = expectedDefectCoefficients alpha.value n :=
    funext (coverCovector_unprojectedDefect alpha.value n)
  rw [he]
  exact expectedDefect_C1_norm_lower alpha n hn

theorem projected_norm_bounds_of_identity (rho : CircleAction Torus)
    (alpha : HolderExponent)
    (heq : ∀ n : ℕ, projectedDefect rho alpha.value n = unprojectedDefect alpha.value n) :
    (∀ n : ℕ, covectorHolderENorm 1 alpha.value (projectedDefect rho alpha.value n) < ⊤) ∧
    (∀ n : ℕ, 2 ≤ n → Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
      covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n)) := by
  constructor
  · intro n
    rw [heq n]
    exact actual_unprojectedDefect_finite alpha n 1
  · intro n hn
    rw [heq n]
    exact actual_unprojectedDefect_C1_norm_lower alpha n (by omega)


theorem projectedDefect_holder_bounds_proof (rho : CircleAction Torus)
    (hrho : rho.act = translate) (alpha : HolderExponent) :
    (∀ n : ℕ, covectorHolderENorm 1 alpha.value (projectedDefect rho alpha.value n) < ⊤) ∧
    (∀ n : ℕ, 2 ≤ n → Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
      covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n)) := by
  exact projected_norm_bounds_of_identity rho alpha
    (fun n => FlatTorus.DefectHaarProof.projectedDefect_eq_unprojectedDefect rho hrho alpha.value n)

end K24.Global.DefectNormProof

namespace K24.Global.FlatTorus
theorem _root_.solution :
  ∀ (rho : CircleAction Torus), rho.act = translate → ∀ alpha : HolderExponent,
    (∀ n : ℕ, covectorHolderENorm 1 alpha.value (projectedDefect rho alpha.value n) < ⊤) ∧
    (∀ n : ℕ, 2 ≤ n → Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
      covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n)) := DefectNormProof.projectedDefect_holder_bounds_proof
end K24.Global.FlatTorus
