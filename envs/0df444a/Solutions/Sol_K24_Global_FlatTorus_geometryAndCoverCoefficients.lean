-- Prove2me | solution 1 for K24.Global.FlatTorus.geometryAndCoverCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:22:38.001312+00:00
-- url     : https://prove2.me/submissions/3b1c743e-b818-4af8-adb9-db50f9ee8ef5

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

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

open K24.Global K24.Global.FlatTorus

theorem solution :
  IsManifold I4 ∞ Torus ∧
  ContMDiff I4 I4 ∞ quotientMap ∧
  (∀ x : FourSpace, ∃ e : OpenPartialHomeomorph FourSpace Torus,
    x ∈ e.source ∧ (⇑e = quotientMap) ∧
    ContMDiffOn I4 I4 ∞ e e.source ∧ ContMDiffOn I4 I4 ∞ e.symm e.target) ∧
  (∀ x : FourSpace,
    HasMFDerivAt I4 I4 quotientMap x (ContinuousLinearMap.id ℝ FourSpace) ∧
    coverDifferential x = ContinuousLinearMap.id ℝ FourSpace ∧
    (coverDifferential x).IsInvertible) ∧
  (∀ (x : FourSpace) (i : Fin 4),
    frame (quotientMap x) i = coverDifferential x (basisVector i)) ∧
  (∀ (x v : FourSpace) (i : Fin 4),
    coframe (quotientMap x) i (coverDifferential x v) = v i) ∧
  (∀ (p : Torus) (i j : Fin 4),
    coframe p i (frame p j) = if i = j then 1 else 0) ∧
  IsMetric flatMetric ∧
  (∀ x : FourSpace, coverCov2 flatMetric x = 1) ∧
  (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4),
    coverCov2 (perturbation alpha n) x i j =
      if i = 0 ∧ j = 0 then liftedOscillation alpha n (x 0) else 0) ∧
  (∀ x : FourSpace, coverVector testVector x = Real.cos (x 1) • basisVector 0) := by
  refine ⟨torus_isManifold, quotientMap_contMDiff, quotientMap_localDiffeomorph,
    ?_, frame_coverDifferential, coframe_coverDifferential, coframe_frame,
    flatMetric_isMetric, coverCov2_flatMetric, coverCov2_perturbation,
    coverVector_testVector⟩
  intro x
  exact ⟨quotientMap_hasMFDerivAt x, coverDifferential_eq_id x,
    coverDifferential_isInvertible x⟩
