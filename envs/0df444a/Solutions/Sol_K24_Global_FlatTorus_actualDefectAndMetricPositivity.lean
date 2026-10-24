-- Prove2me | solution 1 for K24.Global.FlatTorus.actualDefectAndMetricPositivity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:38:25.727898+00:00
-- url     : https://prove2.me/submissions/5509a6d4-a031-41fa-9e2d-31fb2db1a70c

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff

namespace K24.Global.FlatTorus

private theorem quotientMap_add (x y : FourSpace) :
    quotientMap (x + y) = quotientMap x * quotientMap y := by
  funext i
  exact Circle.exp_add (x i) (y i)

private theorem quotientMap_sub (x y : FourSpace) :
    quotientMap (x - y) = quotientMap x / quotientMap y := by
  funext i
  exact Circle.exp_sub (x i) (y i)

private theorem quotientMap_translate_of_eq {x y : FourSpace} (h : quotientMap x = quotientMap y)
    (z : FourSpace) : quotientMap (z - x + y) = quotientMap z := by
  rw [quotientMap_add, quotientMap_sub, h, div_mul_cancel]

private theorem localInverse_quotientMap_eventually_translation (a x : FourSpace)
    (hx : quotientMap x ∈ (quotientMap_isLocalHomeomorph.localInverseAt a).source) :
    (fun y => quotientMap_isLocalHomeomorph.localInverseAt a (quotientMap y)) =ᶠ[𝓝 x]
      (fun y => y - x + quotientMap_isLocalHomeomorph.localInverseAt a (quotientMap x)) := by
  let e := quotientMap_isLocalHomeomorph.localInverseAt a
  have hx' : e (quotientMap x) ∈ e.target := e.map_source hx
  have hcont : ContinuousAt (fun y : FourSpace => y - x + e (quotientMap x)) x := by
    fun_prop
  have hmem : ∀ᶠ y in 𝓝 x, y - x + e (quotientMap x) ∈ e.target := by
    apply hcont.eventually
    simpa using e.open_target.mem_nhds hx'
  have hsource : ∀ᶠ y in 𝓝 x, quotientMap y ∈ e.source :=
    quotientMap_isLocalHomeomorph.continuous.continuousAt.eventually (e.open_source.mem_nhds hx)
  filter_upwards [hmem, hsource] with y hy hqy
  apply quotientMap_isLocalHomeomorph.injOn_localInverseAt_target
    (e.map_source hqy) hy
  rw [quotientMap_isLocalHomeomorph.apply_localInverseAt_of_mem hqy]
  exact (quotientMap_translate_of_eq
    (quotientMap_isLocalHomeomorph.apply_localInverseAt_of_mem hx).symm y).symm

private theorem contDiffAt_localInverse_quotientMap (a x : FourSpace)
    (hx : quotientMap x ∈ (quotientMap_isLocalHomeomorph.localInverseAt a).source) :
    ContDiffAt ℝ ∞ (fun y => quotientMap_isLocalHomeomorph.localInverseAt a (quotientMap y)) x := by
  apply ContDiffAt.congr_of_eventuallyEq (f := fun y => y - x +
    quotientMap_isLocalHomeomorph.localInverseAt a (quotientMap x))
  · fun_prop
  · exact localInverse_quotientMap_eventually_translation a x hx

private theorem chartAt_eq_localInverse (p : Torus) :
    chartAt FourSpace p = quotientMap_isLocalHomeomorph.localInverseAt (representative p) := by
  change (quotientMap_isLocalHomeomorph.localInverseAt (representative p)).trans
    (OpenPartialHomeomorph.refl FourSpace) = _
  exact OpenPartialHomeomorph.trans_refl _

end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff

namespace K24.Global.FlatTorus

private theorem atlas_eq_range_chartAt :
    atlas FourSpace Torus = Set.range (chartAt FourSpace : Torus → OpenPartialHomeomorph Torus FourSpace) :=
  rfl

private theorem inverse_transition_contDiff (a b : FourSpace) :
    ContDiffOn ℝ ∞
      ((quotientMap_isLocalHomeomorph.localInverseAt a).symm.trans
        (quotientMap_isLocalHomeomorph.localInverseAt b))
      ((quotientMap_isLocalHomeomorph.localInverseAt a).symm.trans
        (quotientMap_isLocalHomeomorph.localInverseAt b)).source := by
  intro x hx
  have hq : quotientMap x ∈ (quotientMap_isLocalHomeomorph.localInverseAt b).source := by
    simpa only [OpenPartialHomeomorph.symm_symm, Set.mem_preimage,
      IsLocalHomeomorph.localInverseAt_symm] using hx.2
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_def,
    IsLocalHomeomorph.localInverseAt_symm] using
    (contDiffAt_localInverse_quotientMap b x hq).contDiffWithinAt

private theorem torus_isManifold : IsManifold I4 ∞ Torus := by
  apply isManifold_of_contDiffOn I4 ∞ Torus
  intro e e' he he'
  rw [atlas_eq_range_chartAt] at he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  simpa only [I4, chartAt_eq_localInverse, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
    Set.preimage_id, Set.range_id, Set.inter_univ] using
    inverse_transition_contDiff (representative p) (representative q)

private theorem writtenInExtChartAt_quotientMap (x : FourSpace) :
    writtenInExtChartAt I4 I4 x quotientMap =
      fun y => quotientMap_isLocalHomeomorph.localInverseAt (representative (quotientMap x))
        (quotientMap y) := by
  simp only [writtenInExtChartAt, I4, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id,
    extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, chartAt_eq_localInverse]
  rfl

private theorem quotientMap_contMDiff : ContMDiff I4 I4 ∞ quotientMap := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨quotientMap_isLocalHomeomorph.continuous.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ∞ (writtenInExtChartAt I4 I4 x quotientMap)
    (range I4) (extChartAt I4 x x)
  rw [writtenInExtChartAt_quotientMap]
  have hx : quotientMap x ∈
      (quotientMap_isLocalHomeomorph.localInverseAt (representative (quotientMap x))).source := by
    rw [← chartAt_eq_localInverse]
    exact mem_chart_source FourSpace (quotientMap x)
  simpa only [I4, ext_chart_model_space_apply] using
    (contDiffAt_localInverse_quotientMap _ x hx).contDiffWithinAt

private theorem quotientMap_hasMFDerivAt (x : FourSpace) :
    HasMFDerivAt I4 I4 quotientMap x (ContinuousLinearMap.id ℝ FourSpace) := by
  refine ⟨quotientMap_isLocalHomeomorph.continuous.continuousAt, ?_⟩
  rw [writtenInExtChartAt_quotientMap]
  have hx : quotientMap x ∈
      (quotientMap_isLocalHomeomorph.localInverseAt (representative (quotientMap x))).source := by
    rw [← chartAt_eq_localInverse]
    exact mem_chart_source FourSpace (quotientMap x)
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x).add_const
    (quotientMap_isLocalHomeomorph.localInverseAt (representative (quotientMap x)) (quotientMap x))
  have he := hd.congr_of_eventuallyEq (localInverse_quotientMap_eventually_translation _ x hx)
  simpa only [I4, ext_chart_model_space_apply] using he.hasFDerivWithinAt

private theorem coverDifferential_eq_id (x : FourSpace) :
    coverDifferential x = ContinuousLinearMap.id ℝ FourSpace :=
  (quotientMap_hasMFDerivAt x).mfderiv

end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff

namespace K24.Global.FlatTorus

private theorem extChartAt_symm_eq_quotientMap (p : Torus) :
    ⇑(extChartAt I4 p).symm = quotientMap := by
  simp only [extChartAt_coe_symm, I4, modelWithCornersSelf_coe_symm,
    Function.comp_id, chartAt_eq_localInverse, IsLocalHomeomorph.localInverseAt_symm]

private theorem extChartAt_self_eq_representative (p : Torus) :
    extChartAt I4 p p = representative p := by
  change (chartAt FourSpace p) p = _
  rw [chartAt_eq_localInverse]
  nth_rw 2 [← quotientMap_representative p]
  exact quotientMap_isLocalHomeomorph.localInverseAt_apply_self

private theorem localInverse_contMDiffAt (a : FourSpace) (p : Torus)
    (hp : p ∈ (quotientMap_isLocalHomeomorph.localInverseAt a).source) :
    ContMDiffAt I4 I4 ∞ (quotientMap_isLocalHomeomorph.localInverseAt a) p := by
  rw [contMDiffAt_iff]
  refine ⟨(quotientMap_isLocalHomeomorph.localInverseAt a).continuousAt hp, ?_⟩
  rw [extChartAt_self_eq_representative]
  have hq : quotientMap (representative p) ∈
      (quotientMap_isLocalHomeomorph.localInverseAt a).source := by
    simpa only [quotientMap_representative] using hp
  simpa only [I4, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, extChartAt_symm_eq_quotientMap, Function.comp_def, id_eq] using
    (contDiffAt_localInverse_quotientMap a (representative p) hq).contDiffWithinAt

private theorem localInverse_contMDiffOn (a : FourSpace) :
    ContMDiffOn I4 I4 ∞ (quotientMap_isLocalHomeomorph.localInverseAt a)
      (quotientMap_isLocalHomeomorph.localInverseAt a).source := by
  intro p hp
  exact (localInverse_contMDiffAt a p hp).contMDiffWithinAt

private theorem quotientMap_localDiffeomorph (x : FourSpace) :
    ∃ e : OpenPartialHomeomorph FourSpace Torus,
      x ∈ e.source ∧ (⇑e = quotientMap) ∧
      ContMDiffOn I4 I4 ∞ e e.source ∧ ContMDiffOn I4 I4 ∞ e.symm e.target := by
  refine ⟨(quotientMap_isLocalHomeomorph.localInverseAt x).symm, ?_,
    quotientMap_isLocalHomeomorph.localInverseAt_symm x, ?_, ?_⟩
  · exact quotientMap_isLocalHomeomorph.self_mem_localInverseAt_target
  · rw [quotientMap_isLocalHomeomorph.localInverseAt_symm]
    exact quotientMap_contMDiff.contMDiffOn
  · simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target] using
      localInverse_contMDiffOn x

end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus

private theorem coverDifferential_isInvertible (x : FourSpace) :
    (coverDifferential x).IsInvertible := by
  rw [coverDifferential_eq_id]
  exact ⟨ContinuousLinearEquiv.refl ℝ FourSpace, rfl⟩

private theorem frame_eq_basisVector (p : Torus) (i : Fin 4) :
    frame p i = basisVector i := by
  rw [frame, coverDifferential_eq_id]
  rfl

private theorem coframe_eq_coordProj (p : Torus) (i : Fin 4) :
    coframe p i = coordProj i := by
  rw [coframe, coverDifferential_eq_id, ContinuousLinearMap.inverse_id]
  rfl

private theorem frame_coverDifferential (x : FourSpace) (i : Fin 4) :
    frame (quotientMap x) i = coverDifferential x (basisVector i) := by
  rw [frame_eq_basisVector, coverDifferential_eq_id]
  rfl

private theorem coframe_coverDifferential (x v : FourSpace) (i : Fin 4) :
    coframe (quotientMap x) i (coverDifferential x v) = v i := by
  rw [coframe_eq_coordProj, coverDifferential_eq_id]
  rfl

private theorem coframe_frame (p : Torus) (i j : Fin 4) :
    coframe p i (frame p j) = if i = j then 1 else 0 := by
  rw [coframe_eq_coordProj, frame_eq_basisVector]
  change (basisVector j) i = _
  simp [basisVector, PiLp.single_apply]

private theorem flatMetric_apply (p : Torus) (v w : FourSpace) :
    flatMetric p v w = ∑ i : Fin 4, v i * w i := by
  simp only [flatMetric, ContinuousLinearMap.sum_apply, coframe_eq_coordProj,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rfl

private theorem flatMetric_isMetric : IsMetric flatMetric := by
  constructor
  · intro p v w
    change FourSpace at v w
    rw [flatMetric_apply, flatMetric_apply]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro p v hv
    change FourSpace at v
    rw [flatMetric_apply]
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
      by_contra! h
      apply hv
      change v = (0 : FourSpace)
      ext i
      exact h i
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (v j))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

private theorem coverCov2_apply (u : RawCov2 Torus) (x : FourSpace) (i j : Fin 4) :
    coverCov2 u x i j = u (quotientMap x) (basisVector i) (basisVector j) := by
  change u (quotientMap x) (coverDifferential x (basisVector i))
    (coverDifferential x (basisVector j)) = _
  rw [coverDifferential_eq_id]
  rfl

private theorem coverCov2_flatMetric (x : FourSpace) : coverCov2 flatMetric x = 1 := by
  ext i j
  rw [coverCov2_apply]
  simp [flatMetric_apply, basisVector, PiLp.single_apply, Matrix.one_apply, eq_comm]

private theorem oscillatingScalar_quotientMap_frame (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    oscillatingScalar alpha n (quotientMap x) = liftedOscillation alpha n (x 0) := by
  simp only [oscillatingScalar, quotientMap, liftedOscillation]
  rw [← Circle.exp_nsmul]
  simp only [Circle.coe_exp, nsmul_eq_mul, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, zero_add, add_zero]

private theorem coverCov2_perturbation (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4) :
    coverCov2 (perturbation alpha n) x i j =
      if i = 0 ∧ j = 0 then liftedOscillation alpha n (x 0) else 0 := by
  rw [coverCov2_apply]
  change oscillatingScalar alpha n (quotientMap x) *
    (coframe (quotientMap x) 0 (basisVector i) *
      coframe (quotientMap x) 0 (basisVector j)) = _
  rw [coframe_eq_coordProj, oscillatingScalar_quotientMap_frame]
  change liftedOscillation alpha n (x 0) * ((basisVector i) 0 * (basisVector j) 0) = _
  simp only [basisVector, PiLp.single_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, eq_comm]

private theorem coverVector_testVector (x : FourSpace) :
    coverVector testVector x = Real.cos (x 1) • basisVector 0 := by
  rw [coverVector, coverDifferential_eq_id, ContinuousLinearMap.inverse_id]
  change testVector (quotientMap x) = _
  rw [testVector, frame_eq_basisVector]
  congr 1
  simp only [quotientMap, Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
    zero_sub, add_zero, sub_zero]

end K24.Global.FlatTorus

namespace K24.Global.FlatTorus

private theorem hasDerivAt_liftedOscillation (alpha : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (liftedOscillation alpha n)
      (amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * r)) r := by
  change HasDerivAt (fun y => amplitude alpha n * Real.sin ((n : ℝ) * y)) _ r
  simpa [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
    (((Real.hasDerivAt_sin ((n : ℝ) * r)).comp r
      ((hasDerivAt_id r).const_mul (n : ℝ))).const_mul (amplitude alpha n))

private theorem deriv_liftedOscillation (alpha : ℝ) (n : ℕ) :
    deriv (liftedOscillation alpha n) =
      fun r => amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * r) := by
  funext r
  exact (hasDerivAt_liftedOscillation alpha n r).deriv

private theorem deriv_twice_liftedOscillation (alpha : ℝ) (n : ℕ) :
    deriv (deriv (liftedOscillation alpha n)) =
      fun r => -(amplitude alpha n * (n : ℝ)^2) * Real.sin ((n : ℝ) * r) := by
  rw [deriv_liftedOscillation]
  funext r
  convert (((Real.hasDerivAt_cos ((n : ℝ) * r)).comp r
    ((hasDerivAt_id r).const_mul (n : ℝ))).const_mul
      (amplitude alpha n * (n : ℝ))).deriv using 1 <;> simp [Function.comp_def] <;> ring


end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus

local instance : IsManifold I4 ∞ Torus := torus_isManifold

private theorem chartAt_symm_eq_quotientMap (p : Torus) :
    ⇑(chartAt FourSpace p).symm = quotientMap := by
  rw [chartAt_eq_localInverse]
  exact quotientMap_isLocalHomeomorph.localInverseAt_symm _

private theorem chartAt_mfderiv_eq_id (c p : Torus) (hp : p ∈ (chartAt FourSpace c).source) :
    mfderiv I4 I4 (chartAt FourSpace c) p = ContinuousLinearMap.id ℝ FourSpace := by
  have h := (mdifferentiable_chart (I := I4) c).symm_comp_deriv hp
  rw [chartAt_symm_eq_quotientMap] at h
  change (coverDifferential _).comp (mfderiv I4 I4 (chartAt FourSpace c) p) = _ at h
  change (coverDifferential _).comp (mfderiv I4 I4 (chartAt FourSpace c) p) =
    ContinuousLinearMap.id ℝ FourSpace at h
  rw [coverDifferential_eq_id, ContinuousLinearMap.id_comp] at h
  exact h

private theorem cov2InChart_eq_coverCov2 (u : RawCov2 Torus) (c : Torus) :
    cov2InChart u c = coverCov2 u := by
  funext x i j
  unfold cov2InChart
  change u ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 ((chartAt FourSpace c).symm : FourSpace → Torus) x (basisVector i))
    (mfderiv I4 I4 ((chartAt FourSpace c).symm : FourSpace → Torus) x (basisVector j)) = _
  rw [chartAt_symm_eq_quotientMap]
  rfl

private theorem covectorInChart_eq_coverCovector (u : RawCovector Torus) (c : Torus) :
    covectorInChart u c = coverCovector u := by
  funext x i
  unfold covectorInChart
  change u ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 ((chartAt FourSpace c).symm : FourSpace → Torus) x (basisVector i)) = _
  rw [chartAt_symm_eq_quotientMap]
  rfl

private theorem coverCovector_apply (u : RawCovector Torus) (x : FourSpace) (i : Fin 4) :
    coverCovector u x i = u (quotientMap x) (basisVector i) := by
  change u (quotientMap x) (coverDifferential x (basisVector i)) = _
  rw [coverDifferential_eq_id]
  rfl

private theorem vectorInChart_eq_coverVector (Y : RawVector Torus) (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) :
    vectorInChart Y c x = coverVector Y x := by
  unfold vectorInChart
  change mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
    (Y ((chartAt FourSpace c).symm x)) = _
  rw [chartAt_symm_eq_quotientMap, chartAt_mfderiv_eq_id c _ hx]
  rw [coverVector, coverDifferential_eq_id, ContinuousLinearMap.inverse_id]
  rfl

private theorem vectorInChart_eventually_eq (Y : RawVector Torus) (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) :
    vectorInChart Y c =ᶠ[𝓝 x] coverVector Y := by
  have hn : ∀ᶠ y in 𝓝 x, quotientMap y ∈ (chartAt FourSpace c).source :=
    (quotientMap_isLocalHomeomorph.continuous.continuousAt).eventually
      ((chartAt FourSpace c).open_source.mem_nhds hx)
  filter_upwards [hn] with y hy using vectorInChart_eq_coverVector Y c y hy

private theorem coverCov2_fromCoordinates (a : Torus → FourSpace → Mat4) (x : FourSpace)
    (i j : Fin 4) :
    coverCov2 (cov2FromCoordinates a) x i j =
      a (quotientMap x) (representative (quotientMap x)) i j := by
  rw [coverCov2_apply]
  simp only [cov2FromCoordinates, cov2FromChartAt,
    chartAt_mfderiv_eq_id _ _ (mem_chart_source FourSpace _),
    show chartAt FourSpace (quotientMap x) (quotientMap x) =
      representative (quotientMap x) from extChartAt_self_eq_representative _]
  change matrixToBilinear (a (quotientMap x) (representative (quotientMap x)))
    (basisVector i) (basisVector j) = _
  simp [matrixToBilinear, coordProj, basisVector, PiLp.single_apply,
    bilinearPullback_apply, eq_comm]

private theorem coverCovector_fromCoordinates (a : Torus → FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) :
    coverCovector (covectorFromCoordinates a) x i =
      a (quotientMap x) (representative (quotientMap x)) i := by
  rw [coverCovector_apply]
  simp only [covectorFromCoordinates, covectorFromChartAt,
    chartAt_mfderiv_eq_id _ _ (mem_chart_source FourSpace _),
    show chartAt FourSpace (quotientMap x) (quotientMap x) =
      representative (quotientMap x) from extChartAt_self_eq_representative _]
  change coefficientsToCovector (a (quotientMap x) (representative (quotientMap x)))
    (basisVector i) = _
  simp [coefficientsToCovector, coordProj, basisVector, PiLp.single_apply, eq_comm]

end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus

private theorem coordDeriv_coord_comp (f : ℝ → ℝ) (f' : ℝ) (k i : Fin 4) (x : FourSpace)
    (hf : HasDerivAt f f' (x k)) :
    coordDeriv (fun y : FourSpace => f (y k)) i x = f' * (basisVector i) k := by
  have h := hf.comp_hasFDerivAt x (coordProj k).hasFDerivAt
  change fderiv ℝ (f ∘ coordProj k) x (basisVector i) = _
  rw [h.fderiv]
  rfl

private theorem coordDeriv_product_coords (f g : ℝ → ℝ) (f' g' : ℝ)
    (k l i : Fin 4) (x : FourSpace)
    (hf : HasDerivAt f f' (x k)) (hg : HasDerivAt g g' (x l)) :
    coordDeriv (fun y : FourSpace => f (y k) * g (y l)) i x =
      f' * (basisVector i) k * g (x l) + f (x k) * g' * (basisVector i) l := by
  have h := (hf.comp_hasFDerivAt x (coordProj k).hasFDerivAt).mul
    (hg.comp_hasFDerivAt x (coordProj l).hasFDerivAt)
  change fderiv ℝ (f ∘ coordProj k * g ∘ coordProj l) x
    (basisVector i) = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change f (x k) * (g' * (basisVector i) l) + g (x l) * (f' * (basisVector i) k) = _
  ring

private theorem hasDerivAt_deriv_lifted (alpha : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (deriv (liftedOscillation alpha n))
      (deriv (deriv (liftedOscillation alpha n)) r) r := by
  rw [deriv_twice_liftedOscillation, deriv_liftedOscillation]
  convert (((Real.hasDerivAt_cos ((n : ℝ) * r)).comp r
    ((hasDerivAt_id r).const_mul (n : ℝ))).const_mul
      (amplitude alpha n * (n : ℝ))) using 1 <;> (try dsimp only [Function.comp_def]) <;> first | rfl | ring

private theorem cos_eq_of_exp_eq {r s : ℝ} (h : Circle.exp r = Circle.exp s) :
    Real.cos r = Real.cos s := by
  have hh := congrArg (fun z : Circle => (z : ℂ).re) h
  simpa [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin] using hh

private theorem sin_eq_of_exp_eq {r s : ℝ} (h : Circle.exp r = Circle.exp s) :
    Real.sin r = Real.sin s := by
  have hh := congrArg (fun z : Circle => (z : ℂ).im) h
  simpa [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin] using hh

private theorem cos_quotientMap_eq {x y : FourSpace} (h : quotientMap x = quotientMap y)
    (i : Fin 4) : Real.cos (x i) = Real.cos (y i) :=
  cos_eq_of_exp_eq (congrFun h i)

private theorem sin_quotientMap_eq {x y : FourSpace} (h : quotientMap x = quotientMap y)
    (i : Fin 4) : Real.sin (x i) = Real.sin (y i) :=
  sin_eq_of_exp_eq (congrFun h i)

private theorem exp_nat_quotientMap_eq {x y : FourSpace} (h : quotientMap x = quotientMap y)
    (n : ℕ) (i : Fin 4) : Circle.exp ((n : ℝ) * x i) = Circle.exp ((n : ℝ) * y i) := by
  simpa only [quotientMap, ← nsmul_eq_mul, Circle.exp_nsmul] using
    congrArg (fun p : Torus => p i ^ n) h

private theorem lifted_quotientMap_eq {x y : FourSpace} (h : quotientMap x = quotientMap y)
    (alpha : ℝ) (n : ℕ) :
    liftedOscillation alpha n (x 0) = liftedOscillation alpha n (y 0) := by
  unfold liftedOscillation
  rw [sin_eq_of_exp_eq (exp_nat_quotientMap_eq h n 0)]

private theorem deriv_lifted_quotientMap_eq {x y : FourSpace} (h : quotientMap x = quotientMap y)
    (alpha : ℝ) (n : ℕ) :
    deriv (liftedOscillation alpha n) (x 0) = deriv (liftedOscillation alpha n) (y 0) := by
  rw [deriv_liftedOscillation]
  dsimp only
  rw [cos_eq_of_exp_eq (exp_nat_quotientMap_eq h n 0)]

private theorem deriv_twice_lifted_quotientMap_eq {x y : FourSpace}
    (h : quotientMap x = quotientMap y) (alpha : ℝ) (n : ℕ) :
    deriv (deriv (liftedOscillation alpha n)) (x 0) =
      deriv (deriv (liftedOscillation alpha n)) (y 0) := by
  rw [deriv_twice_liftedOscillation]
  dsimp only
  rw [sin_eq_of_exp_eq (exp_nat_quotientMap_eq h n 0)]

end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus

private def lieCoefficients (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then Real.cos (x 1) * deriv (liftedOscillation alpha n) (x 0)
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
    -Real.sin (x 1) * liftedOscillation alpha n (x 0)
  else 0

private theorem coordDeriv_perturbation (alpha : ℝ) (n : ℕ) (c : Torus) (x : FourSpace)
    (a i j : Fin 4) :
    coordDeriv (fun y => cov2InChart (perturbation alpha n) c y i j) a x =
      if i = 0 ∧ j = 0 then deriv (liftedOscillation alpha n) (x 0) *
        (basisVector a) 0 else 0 := by
  simp_rw [cov2InChart_eq_coverCov2, coverCov2_perturbation]
  by_cases h : i = 0 ∧ j = 0
  · simp only [h, ↓reduceIte]
    exact coordDeriv_coord_comp _ _ _ _ _
      (hasDerivAt_liftedOscillation alpha n (x 0) |>.differentiableAt.hasDerivAt)
  · simp [h, coordDeriv]

private theorem vectorInChart_testVector (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) (p : Fin 4) :
    vectorInChart testVector c x p =
      if p = 0 then Real.cos (x 1) else 0 := by
  rw [vectorInChart_eq_coverVector _ _ _ hx, coverVector_testVector]
  simp [basisVector, PiLp.single_apply]

private theorem coordDeriv_vectorInChart_testVector (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) (a p : Fin 4) :
    coordDeriv (fun y => vectorInChart testVector c y p) a x =
      if p = 0 then -Real.sin (x 1) * (basisVector a) 1 else 0 := by
  have h : (fun y => vectorInChart testVector c y p) =ᶠ[𝓝 x]
      (fun y : FourSpace => if p = 0 then Real.cos (y 1) else 0) := by
    filter_upwards [vectorInChart_eventually_eq testVector c x hx] with y hy
    rw [hy, coverVector_testVector]
    simp [basisVector, PiLp.single_apply]
  unfold coordDeriv
  rw [h.fderiv_eq]
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    exact coordDeriv_coord_comp _ _ _ _ _ (Real.hasDerivAt_cos (x 1))
  · simp [hp]

private theorem lieTensorInChart_test_perturbation (alpha : ℝ) (n : ℕ) (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) (i j : Fin 4) :
    lieTensorInChart testVector (perturbation alpha n) c x i j =
      lieCoefficients alpha n x i j := by
  unfold lieTensorInChart
  simp_rw [vectorInChart_testVector c x hx, coordDeriv_perturbation,
    coordDeriv_vectorInChart_testVector c x hx, cov2InChart_eq_coverCov2,
    coverCov2_perturbation]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, lieCoefficients, basisVector, PiLp.single_apply]

private theorem lieCoefficients_quotientMap_eq {x y : FourSpace}
    (h : quotientMap x = quotientMap y) (alpha : ℝ) (n : ℕ) :
    lieCoefficients alpha n x = lieCoefficients alpha n y := by
  funext i j
  simp only [lieCoefficients, cos_quotientMap_eq h, sin_quotientMap_eq h,
    lifted_quotientMap_eq h, deriv_lifted_quotientMap_eq h]

private theorem coverCov2_lieTensor_test_perturbation (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    coverCov2 (lieTensor testVector (perturbation alpha n)) x =
      lieCoefficients alpha n x := by
  funext i j
  rw [lieTensor, coverCov2_fromCoordinates]
  rw [lieTensorInChart_test_perturbation]
  · rw [lieCoefficients_quotientMap_eq (quotientMap_representative (quotientMap x))]
  · rw [quotientMap_representative]
    exact mem_chart_source FourSpace _

end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus

private theorem inverseMetricInChart_flat (c : Torus) (x : FourSpace) :
    inverseMetricInChart flatMetric c x = 1 := by
  simp [inverseMetricInChart, cov2InChart_eq_coverCov2, coverCov2_flatMetric]

private theorem christoffelInChart_flat (c : Torus) (x : FourSpace) (k i j : Fin 4) :
    christoffelInChart flatMetric c x k i j = 0 := by
  simp [christoffelInChart, cov2InChart_eq_coverCov2, coverCov2_flatMetric, coordDeriv]

private theorem metricTraceInChart_flat (u : RawCov2 Torus) (c : Torus) (x : FourSpace) :
    metricTraceInChart flatMetric u c x = ∑ a : Fin 4, coverCov2 u x a a := by
  simp [metricTraceInChart, inverseMetricInChart_flat, Matrix.one_apply,
    cov2InChart_eq_coverCov2]

private theorem bianchiInChart_flat (u : RawCov2 Torus) (c : Torus) (x : FourSpace) (j : Fin 4) :
    bianchiInChart flatMetric u c x j =
      -(∑ a : Fin 4, coordDeriv (fun y => coverCov2 u y a j) a x) +
        (1 / 2 : ℝ) * coordDeriv (fun y => ∑ a : Fin 4, coverCov2 u y a a) j x := by
  have ht : metricTraceInChart flatMetric u c =
      (fun y => ∑ a : Fin 4, coverCov2 u y a a) :=
    funext (metricTraceInChart_flat u c)
  simp [bianchiInChart, ht, nablaTensorInChart, inverseMetricInChart_flat,
    christoffelInChart_flat, metricTraceInChart_flat, cov2InChart_eq_coverCov2,
    Matrix.one_apply]

private theorem coordDeriv_lieCoefficients (alpha : ℝ) (n : ℕ) (x : FourSpace) (a i j : Fin 4) :
    coordDeriv (fun y => lieCoefficients alpha n y i j) a x =
      if i = 0 ∧ j = 0 then
        -Real.sin (x 1) * (basisVector a) 1 * deriv (liftedOscillation alpha n) (x 0) +
          Real.cos (x 1) * deriv (deriv (liftedOscillation alpha n)) (x 0) * (basisVector a) 0
      else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
        -Real.cos (x 1) * (basisVector a) 1 * liftedOscillation alpha n (x 0) +
          -Real.sin (x 1) * deriv (liftedOscillation alpha n) (x 0) * (basisVector a) 0
      else 0 := by
  unfold lieCoefficients
  split_ifs with h h'
  · exact coordDeriv_product_coords _ _ _ _ _ _ _ _
      (Real.hasDerivAt_cos (x 1)) (hasDerivAt_deriv_lifted alpha n (x 0))
  · exact coordDeriv_product_coords _ _ _ _ _ _ _ _
      ((Real.hasDerivAt_sin (x 1)).neg)
      (hasDerivAt_liftedOscillation alpha n (x 0) |>.differentiableAt.hasDerivAt)
  · simp [coordDeriv]

private theorem trace_lieCoefficients (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    (∑ a : Fin 4, lieCoefficients alpha n x a a) =
      Real.cos (x 1) * deriv (liftedOscillation alpha n) (x 0) := by
  simp [Fin.sum_univ_four, lieCoefficients]

private theorem bianchiInChart_lie_test_perturbation (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) :
    bianchiInChart flatMetric (lieTensor testVector (perturbation alpha n)) c x =
      expectedDefectCoefficients alpha n x := by
  funext j
  rw [bianchiInChart_flat]
  simp_rw [coverCov2_lieTensor_test_perturbation, coordDeriv_lieCoefficients,
    trace_lieCoefficients]
  rw [coordDeriv_product_coords _ _ _ _ _ _ _ _
    (Real.hasDerivAt_cos (x 1)) (hasDerivAt_deriv_lifted alpha n (x 0))]
  fin_cases j <;>
    simp [Fin.sum_univ_four, expectedDefectCoefficients, basisVector, PiLp.single_apply] <;> ring

private theorem expectedDefectCoefficients_quotientMap_eq {x y : FourSpace}
    (h : quotientMap x = quotientMap y) (alpha : ℝ) (n : ℕ) :
    expectedDefectCoefficients alpha n x = expectedDefectCoefficients alpha n y := by
  funext j
  simp only [expectedDefectCoefficients, cos_quotientMap_eq h, sin_quotientMap_eq h,
    lifted_quotientMap_eq h, deriv_lifted_quotientMap_eq h,
    deriv_twice_lifted_quotientMap_eq h]

private theorem coverCovector_unprojectedDefect (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    coverCovector (unprojectedDefect alpha n) x = expectedDefectCoefficients alpha n x := by
  funext j
  rw [unprojectedDefect, bianchi, coverCovector_fromCoordinates,
    bianchiInChart_lie_test_perturbation]
  rw [expectedDefectCoefficients_quotientMap_eq (quotientMap_representative (quotientMap x))]

end K24.Global.FlatTorus


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus

private theorem oscillatingScalar_gt_neg_one (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n)
    (p : Torus) : -1 < oscillatingScalar alpha.value n p := by
  have hn' : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have ha : 0 ≤ amplitude alpha.value n := Real.rpow_nonneg (by positivity) _
  have hb : amplitude alpha.value n < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hn' (by have := alpha.value.coe_nonneg; linarith)
  have hc := mul_le_mul_of_nonneg_left
    (Real.neg_one_le_sin ((n : ℝ) * (representative p) 0)) ha
  have he := oscillatingScalar_quotientMap_frame (alpha.value : ℝ) n (representative p)
  rw [quotientMap_representative] at he
  rw [he, liftedOscillation]
  linarith

private theorem nearbyMetric_apply (alpha : ℝ) (n : ℕ) (p : Torus) (v w : FourSpace) :
    nearbyMetric alpha n p v w = (∑ i : Fin 4, v i * w i) +
      oscillatingScalar alpha n p * (v 0 * w 0) := by
  change flatMetric p v w + perturbation alpha n p v w = _
  rw [flatMetric_apply]
  simp only [perturbation, coframe_eq_coordProj]
  rfl

private theorem nearbyMetric_isMetric (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n) :
    IsMetric (nearbyMetric alpha.value n) := by
  constructor
  · intro p v w
    change FourSpace at v w
    rw [nearbyMetric_apply, nearbyMetric_apply]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    · ring
  · intro p v hv
    change FourSpace at v
    rw [nearbyMetric_apply]
    have hs : 0 < 1 + oscillatingScalar alpha.value n p := by
      have := oscillatingScalar_gt_neg_one alpha n hn p
      linarith
    have hsum : (∑ i : Fin 4, v i * v i) +
        oscillatingScalar alpha.value n p * (v 0 * v 0) =
        ∑ i : Fin 4, (if i = 0 then 1 + oscillatingScalar alpha.value n p else 1) *
          (v i * v i) := by
      simp [Fin.sum_univ_four]
      ring
    rw [hsum]
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
      by_contra! h
      apply hv
      change v = (0 : FourSpace)
      ext i
      exact h i
    have hw (j : Fin 4) : 0 < (if j = 0 then 1 + oscillatingScalar alpha.value n p else 1) := by
      split_ifs <;> positivity
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le (mul_self_nonneg (v j)))
      ⟨i, Finset.mem_univ i, mul_pos (hw i) (mul_self_pos.mpr hi)⟩

end K24.Global.FlatTorus

open K24.Global K24.Global.FlatTorus

theorem solution :
  (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4),
    coverCov2 (lieTensor testVector (perturbation alpha n)) x i j =
      if i = 0 ∧ j = 0 then
        Real.cos (x 1) * deriv (liftedOscillation alpha n) (x 0)
      else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
        -Real.sin (x 1) * liftedOscillation alpha n (x 0)
      else 0) ∧
  (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace),
    coverCovector (unprojectedDefect alpha n) x = expectedDefectCoefficients alpha n x) ∧
  (∀ (alpha : HolderExponent) (n : ℕ), 2 ≤ n → IsMetric (nearbyMetric alpha.value n)) := by
  refine ⟨?_, coverCovector_unprojectedDefect, nearbyMetric_isMetric⟩
  intro alpha n x i j
  exact congrFun (congrFun (coverCov2_lieTensor_test_perturbation alpha n x) i) j
