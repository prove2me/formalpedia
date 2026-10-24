-- Prove2me | solution 1 for K24.Global.FlatTorus.actual_geometric_sharpness_calculation
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:00:08.751739+00:00
-- url     : https://prove2.me/submissions/03de6f16-ddf1-40db-b2c2-781236ef68c8

import Definitions.Def_K24GlobalStatement

/-!
A self-contained proof of the actual flat-torus Lie/Bianchi defect coefficients
and their two-point quotient from K24 §5.1. The frozen quotient atlas is proved
smooth, its real differential is computed, and the actual global operators
are reconstructed before identifying the claimed trigonometric formula.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus.CoefficientSharpness

theorem liftedOscillation_deriv (alpha : ℝ) (n : ℕ) (r : ℝ) :
    deriv (liftedOscillation alpha n) r =
      amplitude alpha n * Real.cos ((n : ℝ) * r) * (n : ℝ) := by
  change deriv (fun s => amplitude alpha n * Real.sin ((n : ℝ) * s)) r = _
  have h := (((hasDerivAt_id r).const_mul (n : ℝ)).sin).const_mul (amplitude alpha n)
  simpa only [liftedOscillation, id_eq, mul_one, mul_assoc] using h.deriv

theorem liftedOscillation_deriv_two (alpha : ℝ) (n : ℕ) (r : ℝ) :
    deriv (deriv (liftedOscillation alpha n)) r =
      -(amplitude alpha n) * (n : ℝ)^2 * Real.sin ((n : ℝ) * r) := by
  have hf : deriv (liftedOscillation alpha n) = fun s =>
      amplitude alpha n * Real.cos ((n : ℝ) * s) * (n : ℝ) := by
    funext s
    exact liftedOscillation_deriv alpha n s
  rw [hf]
  have h := ((((hasDerivAt_id r).const_mul (n : ℝ)).cos).const_mul
    (amplitude alpha n)).mul_const (n : ℝ)
  convert h.deriv using 1 <;> simp only [id_eq, mul_one]; ring

theorem expectedDefect_zero_formula (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    expectedDefectCoefficients alpha n x 0 =
      amplitude alpha n * (1 + (n : ℝ)^2 / 2) * Real.cos (x 1) *
        Real.sin ((n : ℝ) * x 0) := by
  simp only [expectedDefectCoefficients, ↓reduceIte, liftedOscillation,
    liftedOscillation_deriv_two]
  ring

theorem expectedDefect_zero_coordDeriv (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x =
      amplitude alpha n * (n : ℝ) * (1 + (n : ℝ)^2 / 2) *
        Real.cos (x 1) * Real.cos ((n : ℝ) * x 0) := by
  have h0 : HasFDerivAt (fun z : FourSpace => z 0) (coordProj 0) x :=
    (coordProj 0).hasFDerivAt
  have h1 : HasFDerivAt (fun z : FourSpace => z 1) (coordProj 1) x :=
    (coordProj 1).hasFDerivAt
  have hs := (h0.const_mul (n : ℝ)).sin
  have hc := h1.cos
  have h := (hc.const_mul (amplitude alpha n * (1 + (n : ℝ)^2 / 2))).mul hs
  have hf : (fun z => expectedDefectCoefficients alpha n z 0) =
      fun z : FourSpace =>
        (amplitude alpha n * (1 + (n : ℝ)^2 / 2) * Real.cos (z 1)) *
          Real.sin ((n : ℝ) * z 0) := by
    funext z
    exact expectedDefect_zero_formula alpha n z
  simp only [Pi.mul_def] at h
  rw [coordDeriv, hf, h.fderiv]
  simp [coordProj, basisVector]
  ring

theorem distance_test_points (n : ℕ) (hn : 0 < n) :
    dist (0 : FourSpace) ((Real.pi / (n : ℝ)) • basisVector 0) = Real.pi / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp [dist_zero_left, norm_smul, basisVector, abs_of_pos Real.pi_pos]

theorem expectedDefect_derivative_difference (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
    let d : FourSpace → ℝ := fun x =>
      coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x
    |d 0 - d y| = amplitude alpha n * (n : ℝ) * (2 + (n : ℝ)^2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only
  rw [expectedDefect_zero_coordDeriv, expectedDefect_zero_coordDeriv]
  have hmul : (n : ℝ) * (Real.pi / (n : ℝ)) = Real.pi := by
    field_simp
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  simp only [basisVector, PiLp.zero_apply, mul_zero, Real.cos_zero,
    mul_one, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply,
    ↓reduceIte, h10, hmul, Real.cos_pi, mul_neg_one, sub_neg_eq_add]
  have ha : 0 ≤ amplitude alpha n := Real.rpow_nonneg (by positivity) _
  rw [abs_of_nonneg (by positivity)]
  ring

theorem amplitude_rpow_cancellation (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    amplitude alpha n * (n : ℝ) * (2 + (n : ℝ)^2) /
        Real.rpow (Real.pi / (n : ℝ)) alpha =
      (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-alpha) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 := ne_of_gt hnR
  have hna : Real.rpow (n : ℝ) alpha ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnR _)
  have hpa : Real.rpow Real.pi alpha ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have ha : amplitude alpha n = ((n : ℝ)^3 * Real.rpow (n : ℝ) alpha)⁻¹ := by
    unfold amplitude
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hnR.le, Real.rpow_add hnR]
    norm_num
  rw [ha]
  simp only [Real.rpow_eq_pow] at *
  rw [Real.div_rpow Real.pi_pos.le hnR.le, Real.rpow_neg Real.pi_pos.le]
  field_simp [hn0, hna, hpa]
  ring

theorem expectedDefect_two_point_quotient (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
    let d : FourSpace → ℝ := fun x =>
      coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x
    |d 0 - d y| / Real.rpow (dist (0 : FourSpace) y) alpha =
      (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-alpha) := by
  dsimp only
  rw [expectedDefect_derivative_difference alpha n hn, distance_test_points n hn]
  exact amplitude_rpow_cancellation alpha n hn

end K24.Global.FlatTorus.CoefficientSharpness

/-!
# Smoothness of the frozen quotient torus atlas

The atlas transitions are locally translations. The proof uses only the
quotient's group law and local inverse identities, with no assumed manifold
instance and no import of an admitted target theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus.Geometry20261024

theorem torus_chart_symm (c : Torus) :
    ((chartAt FourSpace c).symm : FourSpace → Torus) = quotientMap := by
  change (((quotientMap_isLocalHomeomorph.localInverseAt (representative c)).trans
    (chartAt FourSpace (representative c))).symm : FourSpace → Torus) = quotientMap
  simp

theorem quotientMap_shift_of_eq (x v y : FourSpace)
    (h : quotientMap v = quotientMap x) :
    quotientMap (y - x + v) = quotientMap y := by
  funext i
  have hi : Circle.exp (v i) = Circle.exp (x i) := congrFun h i
  simp only [quotientMap, sub_eq_add_neg, PiLp.add_apply, PiLp.neg_apply,
    Circle.exp_add, Circle.exp_neg]
  rw [hi]
  group

/-- A local inverse branch of the quotient composed with the quotient is
locally a translation, hence smooth, at every point where the branch applies. -/
theorem chart_quotient_contDiffAt (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) :
    ContDiffAt ℝ ∞ (fun y : FourSpace => chartAt FourSpace c (quotientMap y)) x := by
  let e := chartAt FourSpace c
  let v := e (quotientMap x)
  let T : FourSpace → FourSpace := fun y => y - x + v
  have hv : v ∈ e.target := e.map_source hx
  have hqv : quotientMap v = quotientMap x := by
    have h := e.left_inv hx
    change (chartAt FourSpace c).symm v = quotientMap x at h
    rw [torus_chart_symm c] at h
    exact h
  have hT : ContDiff ℝ ∞ T := (contDiff_id.sub contDiff_const).add contDiff_const
  have hnear : ∀ᶠ y in 𝓝 x, T y ∈ e.target := by
    apply hT.continuous.continuousAt.preimage_mem_nhds
    apply e.open_target.mem_nhds
    simpa [T] using hv
  have heq : (fun y : FourSpace => e (quotientMap y)) =ᶠ[𝓝 x] T := by
    filter_upwards [hnear] with y hy
    have hshift := quotientMap_shift_of_eq x v y hqv
    calc
      e (quotientMap y) = e (quotientMap (T y)) := by rw [show quotientMap (T y) = quotientMap y from hshift]
      _ = T y := by
        rw [← torus_chart_symm c]
        exact e.right_inv hy
  exact hT.contDiffAt.congr_of_eventuallyEq heq

/-- The frozen atlas on the actual compact four-torus is smoothly compatible. -/
theorem torus_atlas_smooth : IsManifold I4 ∞ Torus := by
  apply isManifold_of_contDiffOn I4 ∞ Torus
  intro e e' he he'
  change ∃ c : Torus, chartAt FourSpace c = e at he
  change ∃ c' : Torus, chartAt FourSpace c' = e' at he'
  obtain ⟨c, rfl⟩ := he
  obtain ⟨c', rfl⟩ := he'
  simp only [I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id, Set.preimage_id, Set.inter_univ]
  intro x hx
  have hx' : quotientMap x ∈ (chartAt FourSpace c').source := by
    have hxx := hx.2
    change (chartAt FourSpace c).symm x ∈ (chartAt FourSpace c').source at hxx
    erw [torus_chart_symm c] at hxx
    exact hxx
  change ContDiffWithinAt ℝ ∞
    (fun y => (chartAt FourSpace c') ((chartAt FourSpace c).symm y)) _ x
  erw [torus_chart_symm c]
  exact (chart_quotient_contDiffAt c' x hx').contDiffWithinAt


/-- Smoothness of the actual universal-cover map in the frozen atlas. -/
theorem quotientMap_smooth : ContMDiff I4 I4 ∞ quotientMap := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨quotientMap_isLocalHomeomorph.continuous.continuousAt, ?_⟩
  have h := chart_quotient_contDiffAt (quotientMap x) x (mem_chart_source FourSpace (quotientMap x))
  simpa [extChartAt, I4, Function.comp_def, ContDiffAt] using h

local instance torusManifold : IsManifold I4 ∞ Torus := torus_atlas_smooth

theorem torus_chart_self (p : Torus) : chartAt FourSpace p p = representative p := by
  change ((quotientMap_isLocalHomeomorph.localInverseAt (representative p)).trans
    (chartAt FourSpace (representative p))) p = representative p
  have h := quotientMap_isLocalHomeomorph.localInverseAt_apply_self (x := representative p)
  rw [quotientMap_representative] at h
  simpa using h

theorem coverDifferential_representative (p : Torus) :
    coverDifferential (representative p) = ContinuousLinearMap.id ℝ FourSpace := by
  have h := mfderivWithin_range_extChartAt_symm (I := I4) (x := p)
  have hr : Set.range (I4 : FourSpace → FourSpace) = Set.univ := Set.range_id
  rw [hr, mfderivWithin_univ] at h
  change mfderiv I4 I4 ((chartAt FourSpace p).symm : FourSpace → Torus)
    (chartAt FourSpace p p) = ContinuousLinearMap.id ℝ FourSpace at h
  erw [torus_chart_symm p, torus_chart_self p] at h
  exact h


theorem quotientMap_shift_representative (x y : FourSpace) :
    quotientMap (y - x + representative (quotientMap x)) = quotientMap y := by
  funext i
  have h : Circle.exp (representative (quotientMap x) i) = Circle.exp (x i) :=
    congrFun (quotientMap_representative (quotientMap x)) i
  simp only [quotientMap, sub_eq_add_neg, PiLp.add_apply, PiLp.neg_apply,
    Circle.exp_add, Circle.exp_neg]
  rw [h]
  group

theorem coverDifferential_eq_id (x : FourSpace) :
    coverDifferential x = ContinuousLinearMap.id ℝ FourSpace := by
  let p := quotientMap x
  let T : FourSpace → FourSpace := fun y => y - x + representative p
  have hT : HasFDerivAt T (ContinuousLinearMap.id ℝ FourSpace) x :=
    ((hasFDerivAt_id x).sub_const x).add_const (representative p)
  have hq : MDifferentiableAt I4 I4 quotientMap (representative p) := by
    have h := mdifferentiableAt_atlas_symm (I := I4) (chart_mem_atlas FourSpace p)
      ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p))
    erw [torus_chart_symm p, torus_chart_self p] at h
    exact h
  have hcomp := mfderiv_comp x (g := quotientMap) (f := T)
    (by simpa [T] using hq) hT.differentiableAt.mdifferentiableAt
  have heq : quotientMap ∘ T = quotientMap := by
    funext y
    exact quotientMap_shift_representative x y
  rw [heq, mfderiv_eq_fderiv, hT.fderiv] at hcomp
  change coverDifferential x = (coverDifferential (T x)).comp
    (ContinuousLinearMap.id ℝ FourSpace) at hcomp
  have hTx : T x = representative p := by simp [T]
  erw [hTx, ContinuousLinearMap.comp_id] at hcomp
  exact hcomp.trans (coverDifferential_representative p)

theorem flat_frame_lift (x : FourSpace) (i : Fin 4) :
    (coframe (quotientMap x) i).comp (coverDifferential x) = coordProj i := by
  ext v
  simp [coframe, coverDifferential_eq_id, ContinuousLinearMap.inverse_id]



theorem coframe_eq_coordProj (p : Torus) (i : Fin 4) :
    coframe p i = coordProj i := by
  simp [coframe, coverDifferential_eq_id, ContinuousLinearMap.inverse_id]
  rfl

theorem frame_eq_basisVector (p : Torus) (i : Fin 4) :
    frame p i = basisVector i := by
  simp [frame, coverDifferential_eq_id]
  rfl

theorem coverCov2_eq (u : RawCov2 Torus) (x : FourSpace) (i j : Fin 4) :
    coverCov2 u x i j = u (quotientMap x) (basisVector i) (basisVector j) := by
  change u (quotientMap x) (coverDifferential x (basisVector i))
    (coverDifferential x (basisVector j)) = _
  rw [coverDifferential_eq_id]
  rfl

theorem coverCovector_eq (u : RawCovector Torus) (x : FourSpace) (i : Fin 4) :
    coverCovector u x i = u (quotientMap x) (basisVector i) := by
  change u (quotientMap x) (coverDifferential x (basisVector i)) = _
  rw [coverDifferential_eq_id]
  rfl

theorem coverVector_eq (Y : RawVector Torus) (x : FourSpace) :
    coverVector Y x = Y (quotientMap x) := by
  simp [coverVector, coverDifferential_eq_id, ContinuousLinearMap.inverse_id]
  rfl

@[simp] theorem coordProj_apply (i : Fin 4) (v : FourSpace) : coordProj i v = v i := rfl

theorem flatMetric_lift (x : FourSpace) : coverCov2 flatMetric x = (1 : Mat4) := by
  ext i j
  simp only [coverCov2_eq, flatMetric, coframe_eq_coordProj,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  change (∑ k : Fin 4, (basisVector i) k * (basisVector j) k) = _
  simp [basisVector, PiLp.single_apply, Matrix.one_apply, eq_comm]

theorem oscillatingScalar_lift (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    oscillatingScalar alpha n (quotientMap x) = liftedOscillation alpha n (x 0) := by
  simp only [oscillatingScalar, quotientMap, liftedOscillation]
  rw [← Circle.exp_natCast_mul, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

theorem perturbation_lift (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4) :
    coverCov2 (perturbation alpha n) x i j =
      if i = 0 ∧ j = 0 then amplitude alpha n * Real.sin ((n : ℝ) * x 0) else 0 := by
  rw [coverCov2_eq]
  simp only [perturbation, coframe_eq_coordProj]
  change oscillatingScalar alpha n (quotientMap x) *
    ((basisVector i) 0 * (basisVector j) 0) = _
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [basisVector, PiLp.single_apply, oscillatingScalar_lift, liftedOscillation,
      hi, hj, eq_comm]

theorem testVector_lift (x : FourSpace) :
    coverVector testVector x = Real.cos (x 1) • basisVector 0 := by
  simp [coverVector_eq, testVector, frame_eq_basisVector, quotientMap, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re]

/-- The differential of any canonical chart is identity on its source. -/
theorem chartDifferential_eq_id (c p : Torus) (hp : p ∈ (chartAt FourSpace c).source) :
    mfderiv I4 I4 (chartAt FourSpace c) p = ContinuousLinearMap.id ℝ FourSpace := by
  have h := (mdifferentiable_chart (I := I4) c).symm_comp_deriv hp
  erw [torus_chart_symm c] at h
  change (coverDifferential (chartAt FourSpace c p)).comp
    (mfderiv I4 I4 (chartAt FourSpace c) p) = _ at h
  rw [coverDifferential_eq_id, ContinuousLinearMap.id_comp] at h
  exact h


end K24.Global.FlatTorus.Geometry20261024

namespace K24.Global.FlatTorus.Geometry20261024

theorem cov2InChart_cover (u : RawCov2 Torus) (c : Torus) (x : FourSpace) :
    cov2InChart u c x = coverCov2 u x := by
  unfold cov2InChart coverCov2 pullbackCov2
  dsimp only
  erw [torus_chart_symm c]
  rfl

end K24.Global.FlatTorus.Geometry20261024

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators
namespace K24.Global.FlatTorus.DefectCalculus
open CoefficientSharpness

theorem coordDeriv_oscillation (alpha : ℝ) (n : ℕ) (x : FourSpace) (i : Fin 4) :
    coordDeriv (fun z => liftedOscillation alpha n (z 0)) i x =
      if i = 0 then deriv (liftedOscillation alpha n) (x 0) else 0 := by
  have h0 : HasFDerivAt (fun z : FourSpace => z 0) (coordProj 0) x :=
    (coordProj 0).hasFDerivAt
  have h := ((h0.const_mul (n : ℝ)).sin).const_mul (amplitude alpha n)
  change fderiv ℝ (fun z : FourSpace => amplitude alpha n * Real.sin ((n : ℝ) * z 0)) x
    (basisVector i) = _
  rw [h.fderiv]
  fin_cases i <;> simp [coordProj, basisVector, liftedOscillation_deriv, mul_assoc]

theorem coordDeriv_cosine (x : FourSpace) (i : Fin 4) :
    coordDeriv (fun z => Real.cos (z 1)) i x =
      if i = 1 then -Real.sin (x 1) else 0 := by
  have h1 : HasFDerivAt (fun z : FourSpace => z 1) (coordProj 1) x :=
    (coordProj 1).hasFDerivAt
  rw [coordDeriv, h1.cos.fderiv]
  fin_cases i <;> simp [coordProj, basisVector]

theorem coordDeriv_zero (x : FourSpace) (i : Fin 4) :
    coordDeriv (fun _ : FourSpace => (0 : ℝ)) i x = 0 := by
  simp [coordDeriv]

def lie00 (alpha : ℝ) (n : ℕ) (x : FourSpace) : ℝ :=
  Real.cos (x 1) * deriv (liftedOscillation alpha n) (x 0)

def lie01 (alpha : ℝ) (n : ℕ) (x : FourSpace) : ℝ :=
  -Real.sin (x 1) * liftedOscillation alpha n (x 0)

def lieCoefficients (alpha : ℝ) (n : ℕ) (x : FourSpace) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then lie00 alpha n x
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then lie01 alpha n x
  else 0

theorem coordDeriv_lie00 (alpha : ℝ) (n : ℕ) (x : FourSpace) (i : Fin 4) :
    coordDeriv (lie00 alpha n) i x =
      if i = 0 then Real.cos (x 1) * deriv (deriv (liftedOscillation alpha n)) (x 0)
      else if i = 1 then -Real.sin (x 1) * deriv (liftedOscillation alpha n) (x 0)
      else 0 := by
  have h0 : HasFDerivAt (fun z : FourSpace => z 0) (coordProj 0) x :=
    (coordProj 0).hasFDerivAt
  have h1 : HasFDerivAt (fun z : FourSpace => z 1) (coordProj 1) x :=
    (coordProj 1).hasFDerivAt
  have h := h1.cos.mul ((((h0.const_mul (n : ℝ)).cos).const_mul
    (amplitude alpha n)).mul_const (n : ℝ))
  simp only [Pi.mul_def] at h
  have heq : lie00 alpha n = fun z : FourSpace =>
      Real.cos (z 1) * (amplitude alpha n * Real.cos ((n : ℝ) * z 0) * (n : ℝ)) := by
    funext z
    exact congrArg (fun a => Real.cos (z 1) * a) (liftedOscillation_deriv alpha n (z 0))
  rw [coordDeriv, heq, h.fderiv]
  fin_cases i <;>
    simp [coordProj, basisVector, liftedOscillation_deriv, liftedOscillation_deriv_two] <;> ring_nf
  all_goals simp

theorem coordDeriv_lie01 (alpha : ℝ) (n : ℕ) (x : FourSpace) (i : Fin 4) :
    coordDeriv (lie01 alpha n) i x =
      if i = 0 then -Real.sin (x 1) * deriv (liftedOscillation alpha n) (x 0)
      else if i = 1 then -Real.cos (x 1) * liftedOscillation alpha n (x 0)
      else 0 := by
  have h0 : HasFDerivAt (fun z : FourSpace => z 0) (coordProj 0) x :=
    (coordProj 0).hasFDerivAt
  have h1 : HasFDerivAt (fun z : FourSpace => z 1) (coordProj 1) x :=
    (coordProj 1).hasFDerivAt
  have h := h1.sin.neg.mul (((h0.const_mul (n : ℝ)).sin).const_mul (amplitude alpha n))
  simp only [Pi.mul_def, Pi.neg_apply] at h
  change fderiv ℝ (fun z : FourSpace => -Real.sin (z 1) *
    (amplitude alpha n * Real.sin ((n : ℝ) * z 0))) x (basisVector i) = _
  rw [h.fderiv]
  fin_cases i <;>
    simp [coordProj, basisVector, liftedOscillation, liftedOscillation_deriv] <;> ring_nf
  all_goals simp

theorem flat_bianchi_lieCoefficients (alpha : ℝ) (n : ℕ) (x : FourSpace) (j : Fin 4) :
    -(∑ a : Fin 4, coordDeriv (fun z => lieCoefficients alpha n z a j) a x) +
      (1 / 2 : ℝ) * coordDeriv (fun z => ∑ a : Fin 4, lieCoefficients alpha n z a a) j x =
      expectedDefectCoefficients alpha n x j := by
  fin_cases j <;>
    simp [Fin.sum_univ_succ, lieCoefficients, coordDeriv_lie00, coordDeriv_lie01,
      expectedDefectCoefficients, coordDeriv_zero] <;> ring

end K24.Global.FlatTorus.DefectCalculus

namespace K24.Global.FlatTorus.Defect20261024
open Geometry20261024 DefectCalculus CoefficientSharpness
local instance torusManifold : IsManifold I4 ∞ Torus := Geometry20261024.torus_atlas_smooth

theorem vectorInChart_testVector (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) :
    vectorInChart testVector c x = Real.cos (x 1) • basisVector 0 := by
  unfold vectorInChart
  dsimp only
  erw [Geometry20261024.torus_chart_symm c]
  rw [chartDifferential_eq_id c (quotientMap x) hx]
  change testVector (quotientMap x) = _
  exact (coverVector_eq testVector x).symm.trans (Geometry20261024.testVector_lift x)

theorem vectorInChart_testVector_eventually (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) :
    vectorInChart testVector c =ᶠ[𝓝 x] (fun y => Real.cos (y 1) • basisVector 0) := by
  have hnear : ∀ᶠ y in 𝓝 x, quotientMap y ∈ (chartAt FourSpace c).source :=
    quotientMap_isLocalHomeomorph.continuous.continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hx)
  filter_upwards [hnear] with y hy
  exact vectorInChart_testVector c y hy

theorem vectorInChart_testVector_coordDeriv (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) (i p : Fin 4) :
    coordDeriv (fun y => vectorInChart testVector c y p) i x =
      if p = 0 then (if i = 1 then -Real.sin (x 1) else 0) else 0 := by
  have h := vectorInChart_testVector_eventually c x hx
  have hp : (fun y => vectorInChart testVector c y p) =ᶠ[𝓝 x]
      (fun y => if p = 0 then Real.cos (y 1) else 0) := by
    filter_upwards [h] with y hy
    rw [hy]
    simp [basisVector, PiLp.single_apply, eq_comm]
  rw [coordDeriv, hp.fderiv_eq]
  by_cases hp0 : p = 0
  · simp only [hp0, ↓reduceIte]
    exact coordDeriv_cosine x i
  · simp [hp0]

theorem cov2InChart_perturbation (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) (i j : Fin 4) :
    cov2InChart (perturbation alpha n) c x i j =
      if i = 0 ∧ j = 0 then liftedOscillation alpha n (x 0) else 0 := by
  rw [Geometry20261024.cov2InChart_cover]
  exact Geometry20261024.perturbation_lift alpha n x i j

theorem cov2InChart_perturbation_coordDeriv (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) (i j p : Fin 4) :
    coordDeriv (fun y => cov2InChart (perturbation alpha n) c y i j) p x =
      if i = 0 ∧ j = 0 then
        (if p = 0 then deriv (liftedOscillation alpha n) (x 0) else 0) else 0 := by
  simp only [cov2InChart_perturbation]
  by_cases hij : i = 0 ∧ j = 0
  · simp only [hij, ↓reduceIte]
    exact coordDeriv_oscillation alpha n x p
  · simp [hij, coordDeriv_zero]

/-- The actual Lie expression in a chart whose source contains the cover point. -/
theorem lieTensorInChart_perturbation (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) (hx : quotientMap x ∈ (chartAt FourSpace c).source)
    (i j : Fin 4) :
    lieTensorInChart testVector (perturbation alpha n) c x i j =
      lieCoefficients alpha n x i j := by
  unfold lieTensorInChart
  simp only [vectorInChart_testVector c x hx,
    vectorInChart_testVector_coordDeriv c x hx,
    cov2InChart_perturbation, cov2InChart_perturbation_coordDeriv]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, lieCoefficients, lie00, lie01, basisVector, PiLp.single_apply,
      coordDeriv_oscillation, coordDeriv_zero]


theorem cos_eq_of_quotientMap_eq (x y : FourSpace)
    (h : quotientMap x = quotientMap y) (i : Fin 4) :
    Real.cos (x i) = Real.cos (y i) := by
  have hh := congrArg (fun z : Circle => (z : ℂ).re) (congrFun h i)
  simpa only [quotientMap, Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using hh

theorem sin_eq_of_quotientMap_eq (x y : FourSpace)
    (h : quotientMap x = quotientMap y) (i : Fin 4) :
    Real.sin (x i) = Real.sin (y i) := by
  have hh := congrArg (fun z : Circle => (z : ℂ).im) (congrFun h i)
  simpa only [quotientMap, Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using hh

theorem cos_nat_mul_eq_of_quotientMap_eq (x y : FourSpace)
    (h : quotientMap x = quotientMap y) (i : Fin 4) (n : ℕ) :
    Real.cos ((n : ℝ) * x i) = Real.cos ((n : ℝ) * y i) := by
  have hh := congrArg (fun z : Circle => ((z ^ n : Circle) : ℂ).re) (congrFun h i)
  simpa only [quotientMap, ← Circle.exp_natCast_mul, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re] using hh

theorem sin_nat_mul_eq_of_quotientMap_eq (x y : FourSpace)
    (h : quotientMap x = quotientMap y) (i : Fin 4) (n : ℕ) :
    Real.sin ((n : ℝ) * x i) = Real.sin ((n : ℝ) * y i) := by
  have hh := congrArg (fun z : Circle => ((z ^ n : Circle) : ℂ).im) (congrFun h i)
  simpa only [quotientMap, ← Circle.exp_natCast_mul, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im] using hh

theorem expectedDefectCoefficients_eq_of_quotientMap_eq
    (alpha : ℝ) (n : ℕ) (x y : FourSpace) (h : quotientMap x = quotientMap y) :
    expectedDefectCoefficients alpha n x = expectedDefectCoefficients alpha n y := by
  funext j
  simp only [expectedDefectCoefficients, liftedOscillation,
    CoefficientSharpness.liftedOscillation_deriv,
    CoefficientSharpness.liftedOscillation_deriv_two,
    cos_eq_of_quotientMap_eq x y h, sin_eq_of_quotientMap_eq x y h,
    cos_nat_mul_eq_of_quotientMap_eq x y h, sin_nat_mul_eq_of_quotientMap_eq x y h]


theorem lieCoefficients_eq_of_quotientMap_eq
    (alpha : ℝ) (n : ℕ) (x y : FourSpace) (h : quotientMap x = quotientMap y) :
    lieCoefficients alpha n x = lieCoefficients alpha n y := by
  funext i j
  simp only [lieCoefficients, lie00, lie01, liftedOscillation,
    CoefficientSharpness.liftedOscillation_deriv,
    cos_eq_of_quotientMap_eq x y h, sin_eq_of_quotientMap_eq x y h,
    cos_nat_mul_eq_of_quotientMap_eq x y h, sin_nat_mul_eq_of_quotientMap_eq x y h]

open Geometry20261024

theorem coverCov2_fromCoordinates (a : Torus → FourSpace → Mat4)
    (x : FourSpace) (i j : Fin 4) :
    coverCov2 (cov2FromCoordinates a) x i j =
      a (quotientMap x) (representative (quotientMap x)) i j := by
  rw [coverCov2_eq]
  unfold cov2FromCoordinates cov2FromChartAt
  rw [chartDifferential_eq_id _ _ (mem_chart_source FourSpace (quotientMap x)), Geometry20261024.torus_chart_self]
  change matrixToBilinear (a (quotientMap x) (representative (quotientMap x)))
    (basisVector i) (basisVector j) = _
  simp [matrixToBilinear, coordProj, basisVector, PiLp.single_apply, eq_comm]

theorem coverCovector_fromCoordinates (a : Torus → FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) :
    coverCovector (covectorFromCoordinates a) x i =
      a (quotientMap x) (representative (quotientMap x)) i := by
  rw [coverCovector_eq]
  unfold covectorFromCoordinates covectorFromChartAt
  rw [chartDifferential_eq_id _ _ (mem_chart_source FourSpace (quotientMap x)), Geometry20261024.torus_chart_self]
  change coefficientsToCovector (a (quotientMap x) (representative (quotientMap x)))
    (basisVector i) = _
  simp [coefficientsToCovector, coordProj, basisVector, PiLp.single_apply, eq_comm]

theorem inverseMetric_flat (c : Torus) (x : FourSpace) :
    inverseMetricInChart flatMetric c x = (1 : Mat4) := by
  simp [inverseMetricInChart, Geometry20261024.cov2InChart_cover, flatMetric_lift]

theorem christoffel_flat (c : Torus) (x : FourSpace) (k i j : Fin 4) :
    christoffelInChart flatMetric c x k i j = 0 := by
  simp [christoffelInChart, inverseMetric_flat, Geometry20261024.cov2InChart_cover, flatMetric_lift, coordDeriv]

theorem nablaTensor_flat (u : RawCov2 Torus) (c : Torus) (x : FourSpace) (a b j : Fin 4) :
    nablaTensorInChart flatMetric u c x a b j =
      coordDeriv (fun y => coverCov2 u y b j) a x := by
  simp [nablaTensorInChart, christoffel_flat, Geometry20261024.cov2InChart_cover]

theorem metricTrace_flat (u : RawCov2 Torus) (c : Torus) :
    metricTraceInChart flatMetric u c = fun x => ∑ a : Fin 4, coverCov2 u x a a := by
  funext x
  simp [metricTraceInChart, inverseMetric_flat, Geometry20261024.cov2InChart_cover, Matrix.one_apply]

theorem bianchiInChart_flat (u : RawCov2 Torus) (c : Torus) (x : FourSpace) (j : Fin 4) :
    bianchiInChart flatMetric u c x j =
      -(∑ a : Fin 4, coordDeriv (fun y => coverCov2 u y a j) a x) +
      (1 / 2 : ℝ) * coordDeriv (fun y => ∑ a : Fin 4, coverCov2 u y a a) j x := by
  rw [bianchiInChart, metricTrace_flat]
  simp [inverseMetric_flat, nablaTensor_flat, Matrix.one_apply]


/-- Pullback coefficients of the genuine globally reconstructed Lie derivative. -/
theorem lieTensor_perturbation_lift (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    coverCov2 (lieTensor testVector (perturbation alpha n)) x =
      lieCoefficients alpha n x := by
  funext i j
  rw [lieTensor, coverCov2_fromCoordinates]
  rw [lieTensorInChart_perturbation alpha n (quotientMap x)
    (representative (quotientMap x))
    (by rw [quotientMap_representative]; exact mem_chart_source FourSpace (quotientMap x))]
  exact congrFun (congrFun (lieCoefficients_eq_of_quotientMap_eq alpha n
    (representative (quotientMap x)) x (quotientMap_representative (quotientMap x))) i) j

/-- The actual flat Bianchi operator applied to the actual Lie derivative. -/
theorem bianchiInChart_lieTensor_perturbation (alpha : ℝ) (n : ℕ)
    (c : Torus) (x : FourSpace) (j : Fin 4) :
    bianchiInChart flatMetric (lieTensor testVector (perturbation alpha n)) c x j =
      expectedDefectCoefficients alpha n x j := by
  rw [bianchiInChart_flat]
  simp only [lieTensor_perturbation_lift]
  exact flat_bianchi_lieCoefficients alpha n x j

/-- The frozen geometric defect has the claimed coefficients on every lift. -/
theorem geometric_defect_coefficients (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    coverCovector (unprojectedDefect alpha n) x = expectedDefectCoefficients alpha n x := by
  funext j
  rw [unprojectedDefect, bianchi, coverCovector_fromCoordinates,
    bianchiInChart_lieTensor_perturbation]
  exact congrFun (expectedDefectCoefficients_eq_of_quotientMap_eq alpha n
    (representative (quotientMap x)) x (quotientMap_representative (quotientMap x))) j

/-- The two-point quotient now concerns the actual geometric defect. -/
theorem actual_defect_two_point_quotient (alpha : HolderExponent)
    (n : ℕ) (hn : 2 ≤ n) :
    let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
    let d : FourSpace → ℝ := fun x =>
      coordDeriv (fun z => coverCovector (unprojectedDefect alpha.value n) z 0) 0 x
    |d 0 - d y| / Real.rpow (dist (0 : FourSpace) y) alpha.value =
      (1 + 2 / (n : ℝ) ^ 2) * Real.rpow Real.pi (-(alpha.value : ℝ)) := by
  simp only [geometric_defect_coefficients]
  exact CoefficientSharpness.expectedDefect_two_point_quotient alpha.value n (by omega)




end K24.Global.FlatTorus.Defect20261024

open K24.Global K24.Global.FlatTorus

theorem solution :
    (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace),
      coverCovector (unprojectedDefect alpha n) x = expectedDefectCoefficients alpha n x) ∧
    (∀ (alpha : HolderExponent) (n : ℕ), 2 ≤ n →
      let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
      let d : FourSpace → ℝ := fun x =>
        coordDeriv (fun z => coverCovector (unprojectedDefect alpha.value n) z 0) 0 x
      |d 0 - d y| / Real.rpow (dist (0 : FourSpace) y) alpha.value =
        (1 + 2 / (n : ℝ) ^ 2) * Real.rpow Real.pi (-(alpha.value : ℝ))) := by
  exact ⟨Defect20261024.geometric_defect_coefficients,
    Defect20261024.actual_defect_two_point_quotient⟩

#print axioms K24.Global.FlatTorus.Geometry20261024.torus_atlas_smooth
#print axioms K24.Global.FlatTorus.Geometry20261024.coverDifferential_eq_id
#print axioms K24.Global.FlatTorus.Defect20261024.lieTensor_perturbation_lift
#print axioms K24.Global.FlatTorus.Defect20261024.geometric_defect_coefficients
#print axioms K24.Global.FlatTorus.Defect20261024.actual_defect_two_point_quotient
#print axioms solution
