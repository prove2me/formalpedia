-- Prove2me | solution 1 for K24.Global.FlatTorus.smooth_translation_and_test_vector
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:13:56.431306+00:00
-- url     : https://prove2.me/submissions/0e05a890-c2a9-4605-af5a-71ca1cc15457

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology MeasureTheory
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

theorem actionPullbackVector_testVector (t : Circle) (p : Torus) :
    actionPullbackVector smoothTranslationAction t testVector p =
      ((t * p 1 : Circle) : ℂ).re • basisVector 0 := by
  change mfderiv I4 I4 (translate t⁻¹) (translate t p) (testVector (translate t p)) = _
  rw [mfderiv_translate_eq_id]
  change testVector (translate t p) = _
  simp [testVector, frame_eq_basisVector, translate]

theorem vectorInChart_pullback_testVector (t : Circle) (c : Torus) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    vectorInChart (actionPullbackVector smoothTranslationAction t testVector) c x i =
      ((t * ((chartAt FourSpace c).symm x) 1 : Circle) : ℂ).re * (basisVector 0) i := by
  dsimp only [vectorInChart]
  rw [mfderiv_chartAt_eq_id c _ ((chartAt FourSpace c).symm.map_source hx)]
  change (show FourSpace from actionPullbackVector smoothTranslationAction t testVector
    ((chartAt FourSpace c).symm x)) i = _
  rw [actionPullbackVector_testVector]
  rfl

theorem testVector_haarIntegrable : VectorHaarIntegrable smoothTranslationAction testVector := by
  intro c x hx i
  simp_rw [vectorInChart_pullback_testVector _ c x hx i]
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.of_compactSpace _)

theorem testVector_zeroAverage : IsNonzeroVector smoothTranslationAction testVector := by
  have : circleHaar.IsMulLeftInvariant := by
    unfold circleHaar
    infer_instance
  have hint (p : Torus) (i : Fin 4) :
      (∫ t : Circle, vectorInChart (actionPullbackVector smoothTranslationAction t testVector)
        p (chartAt FourSpace p p) i ∂circleHaar) = 0 := by
    have hx := (chartAt FourSpace p).map_source (mem_chart_source FourSpace p)
    simp_rw [vectorInChart_pullback_testVector _ p _ hx i]
    apply MeasureTheory.integral_eq_zero_of_mul_left_eq_neg (g := (-1 : Circle))
    intro t
    simp [Circle.coe_mul]
    ring
  unfold IsNonzeroVector vectorPi0
  funext p
  simp [hint]

/-- Exact geometric and Haar fields of the original torus sharpness statement. -/
theorem _root_.solution :
  IsManifold I4 ∞ Torus ∧
    ∃ rho : CircleAction Torus,
      rho.act = translate ∧ IsInvariantCov2 rho flatMetric ∧
      VectorHaarIntegrable rho testVector ∧ IsNonzeroVector rho testVector :=
  ⟨original_torus_isManifold, smoothTranslationAction, rfl, flatMetric_invariant,
    testVector_haarIntegrable, testVector_zeroAverage⟩

end K24.Global.FlatTorus.SmoothProof
