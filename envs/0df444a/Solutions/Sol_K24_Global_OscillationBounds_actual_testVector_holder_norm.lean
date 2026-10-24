-- Prove2me | solution 1 for K24.Global.OscillationBounds.actual_testVector_holder_norm
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:26:25.172766+00:00
-- url     : https://prove2.me/submissions/a41437a7-cec4-4286-9421-7676c7f48a34

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/- Copied unchanged from GeometricSupport.lean, SHA256 0b06d2f711ce1eceacddc1ba66ce1326be223ce48beee1e5e8037e1d30dda73a. -/

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
end

/- Analytic estimates for the actual perturbation. -/

set_option autoImplicit false
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

theorem power_scale_interpolation (N alpha : ℝ≥0) (hN : 1 ≤ N)
    (ha : alpha ≤ 1) (k : ℕ) :
    (2 * N ^ ((k : ℝ) - 3 - alpha)) ^ ((1 - alpha : ℝ≥0) : ℝ) *
        (N ^ ((k + 1 : ℕ) - 3 - (alpha : ℝ))) ^ (alpha : ℝ) ≤
      2 * N ^ ((k : ℝ) - 3) := by
  have hN0 : N ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hN)
  have h2 : (2 : ℝ≥0) ^ ((1 - alpha : ℝ≥0) : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ≥0) ^ (1 : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          (by rw [NNReal.coe_sub ha]; exact sub_le_self _ alpha.coe_nonneg)
      _ = _ := NNReal.rpow_one _
  rw [NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul,
    mul_assoc, ← NNReal.rpow_add hN0]
  rw [show ((k : ℝ) - 3 - alpha) * ((1 - alpha : ℝ≥0) : ℝ) +
      ((k + 1 : ℕ) - 3 - (alpha : ℝ)) * alpha = (k : ℝ) - 3 by
        rw [NNReal.coe_sub ha, Nat.cast_add, Nat.cast_one, NNReal.coe_one]; ring]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

theorem coordinateHolderENorm_le_power_scale
    (f : E → V) (k : ℕ) (alpha N : ℝ≥0) (ha : alpha ≤ 1) (hN : 1 ≤ N)
    (hf : ContDiff ℝ (k + 1) f)
    (hB : ∀ j ≤ k + 1, ∀ x,
      ‖iteratedFDeriv ℝ j f x‖₊ ≤ N ^ ((j : ℝ) - 3 - alpha)) :
    coordinateHolderENorm k alpha Set.univ f ≤
      (↑(((k + 3 : ℕ) : ℝ≥0) * N ^ ((k : ℝ) - 3)) : ℝ≥0∞) := by
  have h := coordinateHolderENorm_le_of_derivative_bounds f k alpha ha hf
    (fun j => N ^ ((j : ℝ) - 3 - alpha)) hB
  refine h.trans ?_
  rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
  have hs : ∑ j ∈ Finset.range (k + 1), N ^ ((j : ℝ) - 3 - alpha) ≤
      ((k + 1 : ℕ) : ℝ≥0) * N ^ ((k : ℝ) - 3) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (k + 1), N ^ ((k : ℝ) - 3) := by
        apply Finset.sum_le_sum
        intro j hj
        apply NNReal.rpow_le_rpow_of_exponent_le hN
        have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        linarith [alpha.coe_nonneg]
      _ = _ := by simp
  have hh := power_scale_interpolation N alpha hN ha k
  calc
    _ ≤ ((k + 1 : ℕ) : ℝ≥0) * N ^ ((k : ℝ) - 3) + 2 * N ^ ((k : ℝ) - 3) :=
      add_le_add hs hh
    _ = _ := by push_cast; ring


open FlatTorus

def oscillationMatrix (alpha : ℝ) (n : ℕ) (x : FourSpace) : Mat4 :=
  fun i j => if i = 0 ∧ j = 0 then liftedOscillation alpha n (x 0) else 0

def unitMatrix00 : Mat4 := fun i j => if i = 0 ∧ j = 0 then 1 else 0

theorem unitMatrix00_norm_le : ‖unitMatrix00‖ ≤ 1 := by
  rw [Matrix.norm_le_iff (by norm_num)]
  intro i j
  simp only [unitMatrix00]
  split_ifs <;> norm_num

theorem coordProj_norm_le (i : Fin 4) : ‖coordProj i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [coordProj, PiLp.proj_apply, one_mul] using PiLp.norm_apply_le x i

theorem oscillationMatrix_eq_sin_smul (alpha : ℝ) (n : ℕ) :
    oscillationMatrix alpha n = fun x =>
      Real.sin (((n : ℝ) • coordProj 0) x) • (amplitude alpha n • unitMatrix00) := by
  funext x i j
  simp only [oscillationMatrix, liftedOscillation, unitMatrix00,
    smul_apply, coordProj, PiLp.proj_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem oscillationMatrix_contDiff (alpha : ℝ) (n : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (oscillationMatrix alpha n) := by
  rw [oscillationMatrix_eq_sin_smul]
  exact (Real.contDiff_sin.comp ((n : ℝ) • coordProj 0).contDiff).smul contDiff_const

theorem oscillationMatrix_derivative_bound (alpha : ℝ) (n j : ℕ) (x : FourSpace) :
    ‖iteratedFDeriv ℝ j (oscillationMatrix alpha n) x‖ ≤
      amplitude alpha n * (n : ℝ) ^ j := by
  rw [oscillationMatrix_eq_sin_smul]
  have ha : 0 ≤ amplitude alpha n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hn : ‖((n : ℝ) • coordProj 0)‖ ≤ (n : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
    simpa using mul_le_mul_of_nonneg_left (coordProj_norm_le 0) (Nat.cast_nonneg n)
  have hv : ‖amplitude alpha n • unitMatrix00‖ ≤ amplitude alpha n := by
    rw [norm_smul, Real.norm_of_nonneg ha]
    simpa using mul_le_mul_of_nonneg_left unitMatrix00_norm_le ha
  exact (norm_iteratedFDeriv_sin_linear_smul _ _ j x).trans (by
    gcongr)

theorem oscillationMatrix_bigHolder (alpha : HolderExponent) (n k : ℕ) :
    BigHolderOn k alpha.value Set.univ (oscillationMatrix alpha.value n) := by
  rw [oscillationMatrix_eq_sin_smul]
  exact coordinateHolderENorm_sin_linear_smul _ _ k alpha.value alpha.lessThanOne.le


theorem oscillationMatrix_coordinate_bound (alpha : HolderExponent) (n : ℕ)
    (hn : 1 ≤ n) (k : ℕ) :
    coordinateHolderENorm k alpha.value Set.univ (oscillationMatrix alpha.value n) ≤
      (↑(((k + 3 : ℕ) : ℝ≥0) * (n : ℝ≥0) ^ ((k : ℝ) - 3)) : ℝ≥0∞) := by
  apply coordinateHolderENorm_le_power_scale _ k alpha.value (n : ℝ≥0)
    alpha.lessThanOne.le (by exact_mod_cast hn) (oscillationMatrix_contDiff _ _ _)
  intro j hj x
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hb := oscillationMatrix_derivative_bound alpha.value n j x
  have he : amplitude alpha.value n * (n : ℝ) ^ j =
      (n : ℝ) ^ ((j : ℝ) - 3 - alpha.value) := by
    unfold amplitude
    change (n : ℝ) ^ (-(3 + (alpha.value : ℝ))) * (n : ℝ) ^ j = _
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    congr 1
    ring
  rw [he] at hb
  exact_mod_cast hb

theorem oscillationMatrix_C3_bound_positive (alpha : HolderExponent) (n : ℕ)
    (hn : 1 ≤ n) :
    coordinateHolderENorm 3 alpha.value Set.univ (oscillationMatrix alpha.value n) ≤ 6 := by
  simpa using oscillationMatrix_coordinate_bound alpha n hn 3

theorem oscillationMatrix_C2_bound_positive (alpha : HolderExponent) (n : ℕ)
    (hn : 1 ≤ n) :
    coordinateHolderENorm 2 alpha.value Set.univ (oscillationMatrix alpha.value n) ≤
      (↑((5 : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ≥0∞) := by
  convert oscillationMatrix_coordinate_bound alpha n hn 2 using 1
  norm_num [NNReal.rpow_neg_one]


theorem oscillationMatrix_zero (alpha : ℝ) : oscillationMatrix alpha 0 = 0 := by
  funext x i j
  simp [oscillationMatrix, liftedOscillation]

theorem coordinateHolderENorm_zero (k : ℕ) (alpha : ℝ≥0) :
    coordinateHolderENorm (E := E) k alpha Set.univ (0 : E → V) = 0 := by
  simp [coordinateHolderENorm, derivativeENorm]
  exact eHolderNorm_const _ _ _

theorem oscillationMatrix_C3_bound (alpha : HolderExponent) (n : ℕ) :
    coordinateHolderENorm 3 alpha.value Set.univ (oscillationMatrix alpha.value n) ≤ 6 := by
  rcases n.eq_zero_or_pos with hn | hn
  · rw [hn, oscillationMatrix_zero, coordinateHolderENorm_zero]
    positivity
  · exact oscillationMatrix_C3_bound_positive alpha n hn

theorem oscillationMatrix_C2_tendsto (alpha : HolderExponent) :
    Tendsto (fun n : ℕ =>
      (coordinateHolderENorm 2 alpha.value Set.univ (oscillationMatrix alpha.value n)).toReal)
      atTop (𝓝 0) := by
  have hb : ∀ᶠ n : ℕ in atTop,
      (coordinateHolderENorm 2 alpha.value Set.univ (oscillationMatrix alpha.value n)).toReal ≤
        5 * (n : ℝ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top (oscillationMatrix_C2_bound_positive alpha n hn)
    simpa using h
  have ht : Tendsto (fun n : ℕ => 5 * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (5 : ℝ)
  exact squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) hb ht

theorem coverCov2_perturbation_eq_matrix (alpha : ℝ) (n : ℕ) :
    coverCov2 (perturbation alpha n) = oscillationMatrix alpha n := by
  funext x i j
  exact FlatTorus.SmoothProof.coverCov2_perturbation alpha n x i j

theorem actual_perturbation_holder_bounds_proof (alpha : HolderExponent) :
    (∀ n k : ℕ,
      ContDiff ℝ k (coverCov2 (perturbation alpha.value n)) ∧
      tensorHolderENorm k alpha.value (perturbation alpha.value n) < ⊤) ∧
    (∀ n : ℕ, tensorHolderNorm 3 alpha.value (perturbation alpha.value n) ≤ 6) ∧
    Tendsto (fun n : ℕ => tensorHolderNorm 2 alpha.value (perturbation alpha.value n))
      atTop (𝓝 0) := by
  constructor
  · intro n k
    rw [tensorHolderENorm, coverCov2_perturbation_eq_matrix]
    exact ⟨oscillationMatrix_contDiff _ _ _, (oscillationMatrix_bigHolder alpha n k).2⟩
  constructor
  · intro n
    unfold tensorHolderNorm tensorHolderENorm
    rw [coverCov2_perturbation_eq_matrix]
    have h := ENNReal.toReal_mono (by norm_num : (6 : ℝ≥0∞) ≠ ⊤)
      (oscillationMatrix_C3_bound alpha n)
    simpa using h
  · simpa only [tensorHolderNorm, tensorHolderENorm, coverCov2_perturbation_eq_matrix]
      using oscillationMatrix_C2_tendsto alpha


theorem actual_perturbation_C2_rate (alpha : HolderExponent) (n : ℕ) (hn : 1 ≤ n) :
    tensorHolderNorm 2 alpha.value (perturbation alpha.value n) ≤ 5 * (n : ℝ)⁻¹ := by
  unfold tensorHolderNorm tensorHolderENorm
  rw [coverCov2_perturbation_eq_matrix]
  simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (oscillationMatrix_C2_bound_positive alpha n hn)

theorem actual_perturbation_C3_enorm_bound (alpha : HolderExponent) (n : ℕ) :
    tensorHolderENorm 3 alpha.value (perturbation alpha.value n) ≤ 6 := by
  unfold tensorHolderENorm
  rw [coverCov2_perturbation_eq_matrix]
  exact oscillationMatrix_C3_bound alpha n

theorem actual_perturbation_zero_norm (alpha : HolderExponent) (k : ℕ) :
    tensorHolderENorm k alpha.value (perturbation alpha.value 0) = 0 := by
  unfold tensorHolderENorm
  rw [coverCov2_perturbation_eq_matrix, oscillationMatrix_zero, coordinateHolderENorm_zero]

end K24.Global.OscillationBounds

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise
namespace K24.Global.OscillationBounds
open FlatTorus
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_iteratedFDeriv_cos_linear (l : E →L[ℝ] ℝ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => Real.cos (l x)) x‖ ≤ ‖l‖ ^ j := by
  rw [show (fun x => Real.cos (l x)) = Real.cos ∘ l from rfl,
    l.iteratedFDeriv_comp_right (Real.contDiff_cos : ContDiff ℝ j Real.cos) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j Real.cos (l x)‖ * ∏ _ : Fin j, ‖l‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * ‖l‖ ^ j := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      gcongr
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_cos_le_one j (l x)
    _ = _ := one_mul _

theorem norm_iteratedFDeriv_cos_linear_smul
    (l : E →L[ℝ] ℝ) (v : V) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => Real.cos (l x) • v) x‖ ≤ ‖v‖ * ‖l‖ ^ j := by
  have hf : ContDiff ℝ j (fun x => Real.cos (l x)) := Real.contDiff_cos.comp l.contDiff
  rw [iteratedFDeriv_smul_const_apply hf.contDiffAt]
  calc
    _ ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight v‖ *
        ‖iteratedFDeriv ℝ j (fun x => Real.cos (l x)) x‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ = ‖v‖ * ‖iteratedFDeriv ℝ j (fun x => Real.cos (l x)) x‖ := by
      simp [ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_cos_linear l j x) (norm_nonneg _)

theorem coordinateHolderENorm_cos_linear_smul
    (l : E →L[ℝ] ℝ) (v : V) (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    BigHolderOn k alpha Set.univ (fun x => Real.cos (l x) • v) := by
  have hf : ContDiff ℝ (k + 1) (fun x => Real.cos (l x) • v) :=
    (Real.contDiff_cos.comp l.contDiff).smul contDiff_const
  refine ⟨hf.of_le (by exact_mod_cast Nat.le_succ k) |>.contDiffOn, ?_⟩
  have h := coordinateHolderENorm_le_of_derivative_bounds _ k alpha ha hf
    (fun j => ‖v‖₊ * ‖l‖₊ ^ j) (by
      intro j hj x
      exact_mod_cast norm_iteratedFDeriv_cos_linear_smul l v j x)
  exact lt_of_le_of_lt h (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩)

theorem pointwise_le_coordinateHolderENorm (f : E → V) (k : ℕ)
    (alpha : ℝ≥0) (x : E) :
    (‖f x‖₊ : ℝ≥0∞) ≤ coordinateHolderENorm k alpha Set.univ f := by
  have hpt : (‖f x‖₊ : ℝ≥0∞) ≤ derivativeENorm 0 Set.univ f := by
    unfold derivativeENorm
    apply le_iSup_of_le (⟨x, Set.mem_univ x⟩ : (Set.univ : Set E))
    have he : ‖iteratedFDerivWithin ℝ 0 f Set.univ x‖₊ = ‖f x‖₊ :=
      NNReal.eq (norm_iteratedFDerivWithin_zero (𝕜 := ℝ))
    rw [he]
  have hs : derivativeENorm 0 Set.univ f ≤
      ∑ j ∈ Finset.range (k + 1), derivativeENorm j Set.univ f :=
    Finset.single_le_sum (f := fun j => derivativeENorm j Set.univ f)
      (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.succ_pos k))
  exact hpt.trans (hs.trans (le_add_right le_rfl))

theorem coverVector_testVector_formula (x : FourSpace) :
    coverVector testVector x = Real.cos (x 1) • basisVector 0 := by
  unfold coverVector testVector frame
  rw [FlatTorus.SmoothProof.coverDifferential_eq_id,
    FlatTorus.SmoothProof.coverDifferential_eq_id]
  rw [ContinuousLinearMap.inverse_id]
  change (((quotientMap x 1 : Circle) : ℂ).re • basisVector 0) = _
  congr 1
  simp only [quotientMap, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

theorem actual_testVector_holder_norm_proof (alpha : HolderExponent) :
    (∀ k : ℕ, ContDiff ℝ k (coverVector testVector) ∧
      vectorHolderENorm k alpha.value testVector < ⊤) ∧
    (∀ k : ℕ, 1 ≤ vectorHolderNorm k alpha.value testVector) := by
  have he : coverVector testVector = fun x => Real.cos ((coordProj 1) x) • basisVector 0 := by
    funext x
    exact coverVector_testVector_formula x
  have hfin : ∀ k : ℕ, vectorHolderENorm k alpha.value testVector < ⊤ := by
    intro k
    unfold vectorHolderENorm
    rw [he]
    exact (coordinateHolderENorm_cos_linear_smul _ _ k alpha.value alpha.lessThanOne.le).2
  constructor
  · intro k
    refine ⟨?_, hfin k⟩
    rw [he]
    exact (Real.contDiff_cos.comp (coordProj 1).contDiff).smul contDiff_const
  · intro k
    have hl := pointwise_le_coordinateHolderENorm (coverVector testVector) k alpha.value 0
    have hv : ‖coverVector testVector 0‖₊ = 1 := by
      rw [coverVector_testVector_formula]
      simp [basisVector, PiLp.nnnorm_single]
    rw [hv, ENNReal.coe_one] at hl
    have h := ENNReal.toReal_mono (hfin k).ne hl
    simpa only [vectorHolderNorm, vectorHolderENorm, ENNReal.toReal_one] using h

end K24.Global.OscillationBounds

namespace K24.Global.OscillationBounds
open FlatTorus
theorem _root_.solution :
  ∀ alpha : HolderExponent,
    (∀ k : ℕ, ContDiff ℝ k (coverVector testVector) ∧
      vectorHolderENorm k alpha.value testVector < ⊤) ∧
    (∀ k : ℕ, 1 ≤ vectorHolderNorm k alpha.value testVector) := actual_testVector_holder_norm_proof
end K24.Global.OscillationBounds
