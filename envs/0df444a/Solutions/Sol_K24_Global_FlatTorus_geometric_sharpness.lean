-- Prove2me | solution 1 for K24.Global.FlatTorus.geometric_sharpness
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:11:06.250046+00:00
-- url     : https://prove2.me/submissions/efc7b38a-2b8a-40bc-be25-32f724321d7a

import Definitions.Def_K24GlobalStatement

/-!
A self-contained proof of the complete frozen SharpnessStatement from K24 §5.1.
The proof constructs the actual smooth torus/action, computes the genuine
Lie/Bianchi defect and Haar projection, proves all actual full Holder norms
finite, establishes the exact oscillatory upper/lower estimates, and derives
the failure of every frequency-independent shifted estimate.
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


namespace K24.Global.FlatTorus.Geometry20261024

theorem covectorInChart_cover (u : RawCovector Torus) (c : Torus) (x : FourSpace) :
    covectorInChart u c x = coverCovector u x := by
  unfold covectorInChart coverCovector pullbackCovector
  dsimp only
  erw [torus_chart_symm c]
  rfl

end K24.Global.FlatTorus.Geometry20261024


namespace K24.Global.FlatTorus.CoefficientSharpness
theorem expectedDefect_two_point_lower_bound (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
    let d : FourSpace → ℝ := fun x =>
      coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x
    Real.rpow Real.pi (-alpha) ≤
      |d 0 - d y| / Real.rpow (dist (0 : FourSpace) y) alpha := by
  dsimp only
  rw [expectedDefect_two_point_quotient alpha n hn]
  have hpi : 0 ≤ Real.rpow Real.pi (-alpha) := Real.rpow_nonneg Real.pi_pos.le _
  nlinarith [div_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sq_nonneg (n : ℝ))]


end K24.Global.FlatTorus.CoefficientSharpness



/- Internal assembly: metric/Metric.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators NNReal ENNReal Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus.Metric20261024
open Geometry20261024

theorem flatMetric_apply (p : Torus) (v w : FourSpace) :
    flatMetric p v w = ∑ i : Fin 4, v i * w i := by
  simp only [flatMetric, coframe_eq_coordProj, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

theorem flatMetric_isMetric : IsMetric flatMetric := by
  constructor
  · change ∀ (p : Torus) (v w : FourSpace), flatMetric p v w = flatMetric p w v
    intro p v w
    simp only [flatMetric_apply, mul_comm]
  · change ∀ (p : Torus) (v : FourSpace), v ≠ 0 → 0 < flatMetric p v v
    intro p v hv
    rw [flatMetric_apply]
    have hh : (∑ i : Fin 4, v i * v i) = ‖v‖ ^ 2 := by
      simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq v).symm
    rw [hh]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)

theorem amplitude_lt_one (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n) :
    amplitude alpha.value n < 1 := by
  unfold amplitude
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast (show 1 < n by omega)
  · have ha : (0 : ℝ) < alpha.value := alpha.positive
    linarith

theorem one_add_oscillatingScalar_pos (alpha : HolderExponent) (n : ℕ)
    (hn : 2 ≤ n) (p : Torus) : 0 < 1 + oscillatingScalar alpha.value n p := by
  have ha := amplitude_lt_one alpha n hn
  have ha0 : 0 ≤ amplitude alpha.value n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hs := mul_le_mul_of_nonneg_left
    (Real.neg_one_le_sin ((n : ℝ) * representative p 0)) ha0
  have he := oscillatingScalar_lift (alpha.value : ℝ) n (representative p)
  rw [quotientMap_representative] at he
  rw [he]
  unfold liftedOscillation
  linarith

theorem nearbyMetric_apply (alpha : ℝ) (n : ℕ) (p : Torus)
    (v w : FourSpace) :
    nearbyMetric alpha n p v w =
      (∑ i : Fin 4, v i * w i) + oscillatingScalar alpha n p * (v 0 * w 0) := by
  change flatMetric p v w + oscillatingScalar alpha n p *
    ((coframe p 0) v * (coframe p 0) w) = _
  rw [flatMetric_apply, coframe_eq_coordProj]
  rfl

theorem nearbyMetric_isMetric (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n) :
    IsMetric (nearbyMetric alpha.value n) := by
  constructor
  · change ∀ (p : Torus) (v w : FourSpace), nearbyMetric alpha.value n p v w = nearbyMetric alpha.value n p w v
    intro p v w
    simp only [nearbyMetric_apply, mul_comm]
  · change ∀ (p : Torus) (v : FourSpace), v ≠ 0 → 0 < nearbyMetric alpha.value n p v v
    intro p v hv
    rw [nearbyMetric_apply]
    have h0 := one_add_oscillatingScalar_pos alpha n hn p
    have heq : (∑ i : Fin 4, v i * v i) +
        oscillatingScalar alpha.value n p * (v 0 * v 0) =
        ∑ i : Fin 4, (if i = 0 then 1 + oscillatingScalar alpha.value n p else 1) * (v i)^2 := by
      simp [Fin.sum_univ_succ]
      ring
    rw [heq]
    have hc : ∀ i : Fin 4, 0 < (if i = 0 then 1 + oscillatingScalar alpha.value n p else 1) := by
      intro i
      split_ifs <;> first | exact h0 | norm_num
    have hne : ∃ i : Fin 4, v i ≠ 0 := by
      by_contra! h
      apply hv
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hne
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hc j).le (sq_nonneg _)
    · exact ⟨i, Finset.mem_univ i, mul_pos (hc i) (sq_pos_of_ne_zero hi)⟩

theorem flatMetric_smooth : Cov2ContDiff ∞ flatMetric := by
  intro c
  change ContDiffOn ℝ ∞ (fun x => cov2InChart flatMetric c x) _
  simpa only [Geometry20261024.cov2InChart_cover, flatMetric_lift] using
    (contDiff_const.contDiffOn : ContDiffOn ℝ ∞ (fun _ : FourSpace => (1 : Mat4))
      (chartAt FourSpace c).target)

theorem perturbation_cover_smooth (alpha : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (coverCov2 (perturbation alpha n)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [perturbation_lift]
  by_cases hij : i = 0 ∧ j = 0
  · simp only [hij, ↓reduceIte]
    have h0 : ContDiff ℝ ∞ (fun x : FourSpace => x 0) := (coordProj 0).contDiff
    exact contDiff_const.mul ((contDiff_const.mul h0).sin)
  · simp only [hij, ↓reduceIte]
    exact contDiff_const

theorem perturbation_smooth (alpha : ℝ) (n : ℕ) :
    Cov2ContDiff ∞ (perturbation alpha n) := by
  intro c
  change ContDiffOn ℝ ∞ (fun x => cov2InChart (perturbation alpha n) c x) _
  simp only [Geometry20261024.cov2InChart_cover]
  exact (perturbation_cover_smooth alpha n).contDiffOn

theorem nearbyMetric_cover_smooth (alpha : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (coverCov2 (nearbyMetric alpha n)) := by
  have heq : coverCov2 (nearbyMetric alpha n) =
      fun x => (1 : Mat4) + coverCov2 (perturbation alpha n) x := by
    funext x i j
    change coverCov2 (flatMetric + perturbation alpha n) x i j = _
    simp only [coverCov2_eq, Pi.add_apply, Matrix.add_apply, ContinuousLinearMap.add_apply]
    have hf := congrFun (congrFun (flatMetric_lift x) i) j
    rw [coverCov2_eq] at hf
    rw [hf]
  rw [heq]
  exact contDiff_const.add (perturbation_cover_smooth alpha n)

theorem nearbyMetric_smooth (alpha : ℝ) (n : ℕ) :
    Cov2ContDiff ∞ (nearbyMetric alpha n) := by
  intro c
  change ContDiffOn ℝ ∞ (fun x => cov2InChart (nearbyMetric alpha n) c x) _
  simp only [Geometry20261024.cov2InChart_cover]
  exact (nearbyMetric_cover_smooth alpha n).contDiffOn

theorem testVector_smooth : VectorContDiff ∞ testVector := by
  intro c
  have h0 : ContDiff ℝ ∞ (fun x : FourSpace => x 1) := (coordProj 1).contDiff
  have h : ContDiff ℝ ∞ (fun x : FourSpace => Real.cos (x 1) • basisVector 0) :=
    h0.cos.smul contDiff_const
  apply h.contDiffOn.congr
  intro x hx
  apply Defect20261024.vectorInChart_testVector
  have hh := (chartAt FourSpace c).map_target hx
  erw [Geometry20261024.torus_chart_symm c] at hh
  exact hh

end K24.Global.FlatTorus.Metric20261024


/- Internal assembly: action/Action.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology ChartedSpace MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace K24.Global.FlatTorus.Action20261024
open Geometry20261024 Defect20261024
local instance torusManifold : IsManifold I4 ∞ Torus := torus_atlas_smooth
local instance haar_left : circleHaar.IsMulLeftInvariant := by unfold circleHaar; infer_instance

def localAngle (t₀ t : Circle) : ℝ := Complex.arg (t * t₀⁻¹ : Circle) + Complex.arg t₀

theorem exp_localAngle (t₀ t : Circle) : Circle.exp (localAngle t₀ t) = t := by
  unfold localAngle
  rw [Circle.exp_add, Circle.exp_arg, Circle.exp_arg]
  group

theorem localAngle_contMDiffAt (t₀ : Circle) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (localAngle t₀) t₀ := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun t : Circle => (t : ℂ)) :=
    contMDiff_coe_sphere
  have hm : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun t : Circle => t * t₀⁻¹) :=
    contMDiff_id.mul contMDiff_const
  have hl : ContDiffAt ℝ ∞ Complex.log (1 : ℂ) :=
    (Complex.contDiffAt_log (by simp : (1 : ℂ) ∈ Complex.slitPlane)).restrict_scalars ℝ
  have hlog : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun t : Circle => Complex.log (t * t₀⁻¹ : Circle)) t₀ := by
    have hl' : ContDiffAt ℝ ∞ Complex.log ((t₀ * t₀⁻¹ : Circle) : ℂ) := by simpa using hl
    have hh := hl'.contMDiffAt.comp t₀ ((hc.comp hm).contMDiffAt)
    simpa only [Function.comp_def, Circle.coe_mul, Circle.coe_inv] using hh
  have hi := Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp t₀ hlog
  convert hi.add (contMDiffAt_const (c := Complex.arg t₀)) using 1
  funext t
  simp [localAngle, Complex.log_im]

theorem translate_cover_angle (t : Circle) (r : ℝ) (hr : Circle.exp r = t)
    (x : FourSpace) : translate t (quotientMap x) = quotientMap (x + r • basisVector 1) := by
  funext i
  by_cases hi : i = 1
  · subst i
    simp [translate, quotientMap, basisVector, Circle.exp_add, hr, mul_comm]
  · simp [translate, quotientMap, basisVector, hi]

theorem translate_joint_smooth : ContMDiff ((𝓡 1).prod I4) I4 ∞
    (fun q : Circle × Torus => translate q.1 q.2) := by
  intro q
  let L : Circle × Torus → FourSpace := fun z =>
    chartAt FourSpace q.2 z.2 + localAngle q.1 z.1 • basisVector 1
  have hchart : ContMDiffAt I4 I4 ∞ (chartAt FourSpace q.2) q.2 :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q.2)
      (mem_chart_source FourSpace q.2)
  have hL : ContMDiffAt ((𝓡 1).prod I4) I4 ∞ L q :=
    (hchart.comp q contMDiffAt_snd).add
      (((localAngle_contMDiffAt q.1).comp q contMDiffAt_fst).smul contMDiffAt_const)
  have heq : (fun z : Circle × Torus => translate z.1 z.2) =ᶠ[𝓝 q]
      (fun z => quotientMap (L z)) := by
    have hn : ∀ᶠ z : Circle × Torus in 𝓝 q,
        z.2 ∈ (chartAt FourSpace q.2).source :=
      continuous_snd.continuousAt.preimage_mem_nhds
        ((chartAt FourSpace q.2).open_source.mem_nhds (mem_chart_source FourSpace q.2))
    filter_upwards [hn] with z hz
    have hinv : quotientMap (chartAt FourSpace q.2 z.2) = z.2 := by
      rw [← torus_chart_symm q.2]
      exact (chartAt FourSpace q.2).left_inv hz
    rw [← hinv]
    exact translate_cover_angle z.1 (localAngle q.1 z.1) (exp_localAngle q.1 z.1) _
  exact (quotientMap_smooth.contMDiffAt.comp q hL).congr_of_eventuallyEq heq

def translationAction : CircleAction Torus where
  act := translate
  one_act := translate_one
  mul_act := translate_mul
  smooth := translate_joint_smooth

theorem translate_smooth (t : Circle) : ContMDiff I4 I4 ∞ (translate t) := by
  exact translate_joint_smooth.comp (contMDiff_const.prodMk contMDiff_id)

theorem translate_differential (t : Circle) (p : Torus) :
    mfderiv I4 I4 (translate t) p = ContinuousLinearMap.id ℝ FourSpace := by
  obtain ⟨x, rfl⟩ := quotientMap_surjective p
  let T : FourSpace → FourSpace := fun y => y + Complex.arg t • basisVector 1
  have hT : HasFDerivAt T (ContinuousLinearMap.id ℝ FourSpace) x :=
    (hasFDerivAt_id x).add_const _
  have heq : translate t ∘ quotientMap = quotientMap ∘ T := by
    funext y
    exact translate_cover_angle t (Complex.arg t) (Circle.exp_arg t) y
  have h₁ := mfderiv_comp x ((translate_smooth t).mdifferentiable (by simp) _)
    (quotientMap_smooth.mdifferentiable (by simp) x)
  have h₂ := mfderiv_comp x (quotientMap_smooth.mdifferentiable (by simp) (T x))
    hT.differentiableAt.mdifferentiableAt
  rw [heq, h₂, mfderiv_eq_fderiv, hT.fderiv] at h₁
  change (coverDifferential (T x)).comp (ContinuousLinearMap.id ℝ FourSpace) =
    (mfderiv I4 I4 (translate t) (quotientMap x)).comp (coverDifferential x) at h₁
  rw [coverDifferential_eq_id, coverDifferential_eq_id,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_id] at h₁
  exact h₁.symm

theorem pullbackCovector_translate (t : Circle) (u : RawCovector Torus) (p : Torus) :
    actionPullbackCovector translationAction t u p = u (translate t p) := by
  change (u (translate t p)).comp (mfderiv I4 I4 (translate t) p) = _
  rw [translate_differential]
  rfl

theorem pullbackVector_translate (t : Circle) (Y : RawVector Torus) (p : Torus) :
    actionPullbackVector translationAction t Y p = Y (translate t p) := by
  change mfderiv I4 I4 (translate t⁻¹) (translate t p) (Y (translate t p)) = _
  rw [translate_differential]
  rfl

def defectCoefficients (alpha : ℝ) (n : ℕ) (p : Torus) (j : Fin 4) : ℝ :=
  if j = 0 then amplitude alpha n * (1 + (n : ℝ)^2 / 2) * (p 1 : ℂ).re *
    ((p 0 ^ n : Circle) : ℂ).im
  else if j = 1 then (1 / 2 : ℝ) * amplitude alpha n * (n : ℝ) * (p 1 : ℂ).im *
    ((p 0 ^ n : Circle) : ℂ).re
  else 0

theorem defectCoefficients_cover (alpha : ℝ) (n : ℕ) (x : FourSpace) (j : Fin 4) :
    defectCoefficients alpha n (quotientMap x) j = expectedDefectCoefficients alpha n x j := by
  have hre (i : Fin 4) : (quotientMap x i : ℂ).re = Real.cos (x i) := by
    simp only [quotientMap, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have him (i : Fin 4) : (quotientMap x i : ℂ).im = Real.sin (x i) := by
    simp only [quotientMap, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  have hnpow_re : ((quotientMap x 0 ^ n : Circle) : ℂ).re = Real.cos ((n : ℝ) * x 0) := by
    change ((Circle.exp (x 0) ^ n : Circle) : ℂ).re = _
    rw [← Circle.exp_natCast_mul, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have hnpow_im : ((quotientMap x 0 ^ n : Circle) : ℂ).im = Real.sin ((n : ℝ) * x 0) := by
    change ((Circle.exp (x 0) ^ n : Circle) : ℂ).im = _
    rw [← Circle.exp_natCast_mul, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  simp only [defectCoefficients, hnpow_re, hnpow_im, hre, him]
  fin_cases j <;>
    simp [expectedDefectCoefficients, liftedOscillation, CoefficientSharpness.liftedOscillation_deriv,
      CoefficientSharpness.liftedOscillation_deriv_two] <;> ring

theorem unprojectedDefect_basis (alpha : ℝ) (n : ℕ) (p : Torus) (j : Fin 4) :
    unprojectedDefect alpha n p (basisVector j) = defectCoefficients alpha n p j := by
  obtain ⟨x, rfl⟩ := quotientMap_surjective p
  rw [← coverCovector_eq, geometric_defect_coefficients, defectCoefficients_cover]

theorem covectorInChart_pullback_defect (alpha : ℝ) (n : ℕ) (c : Torus)
    (x : FourSpace) (t : Circle) (j : Fin 4) :
    covectorInChart (actionPullbackCovector translationAction t (unprojectedDefect alpha n)) c x j =
      defectCoefficients alpha n (translate t (quotientMap x)) j := by
  rw [Geometry20261024.covectorInChart_cover, coverCovector_eq, pullbackCovector_translate]
  exact unprojectedDefect_basis alpha n (translate t (quotientMap x)) j

theorem defectCoefficients_translate_continuous (alpha : ℝ) (n : ℕ) (p : Torus) (j : Fin 4) :
    Continuous (fun t : Circle => defectCoefficients alpha n (translate t p) j) := by
  unfold defectCoefficients translate
  split_ifs <;> fun_prop

theorem defectCoefficients_translate_neg (alpha : ℝ) (n : ℕ) (p : Torus)
    (t : Circle) (j : Fin 4) :
    defectCoefficients alpha n (translate ((-1) * t) p) j =
      -defectCoefficients alpha n (translate t p) j := by
  simp [defectCoefficients, translate]
  split_ifs <;> ring

theorem defectCoefficients_translate_integral_zero (alpha : ℝ) (n : ℕ) (p : Torus) (j : Fin 4) :
    (∫ t : Circle, defectCoefficients alpha n (translate t p) j ∂circleHaar) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := (-1 : Circle))
  intro t
  exact defectCoefficients_translate_neg alpha n p t j

theorem defect_haar_integrable (alpha : ℝ) (n : ℕ) :
    CovectorHaarIntegrable translationAction (unprojectedDefect alpha n) := by
  intro c x hx j
  simp only [covectorInChart_pullback_defect]
  exact (defectCoefficients_translate_continuous alpha n (quotientMap x) j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem defect_haar_average_zero (alpha : ℝ) (n : ℕ) :
    covectorPi0 translationAction (unprojectedDefect alpha n) = 0 := by
  unfold covectorPi0
  simp only [covectorInChart_pullback_defect, defectCoefficients_translate_integral_zero]
  funext p
  ext v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector]

theorem vectorInChart_pullback_testVector (c : Torus) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (t : Circle) (j : Fin 4) :
    vectorInChart (actionPullbackVector translationAction t testVector) c x j =
      if j = 0 then ((t * quotientMap x 1 : Circle) : ℂ).re else 0 := by
  have hp : quotientMap x ∈ (chartAt FourSpace c).source := by
    have hh := (chartAt FourSpace c).map_target hx
    rwa [torus_chart_symm c] at hh
  unfold vectorInChart
  dsimp only
  erw [torus_chart_symm c]
  rw [chartDifferential_eq_id c (quotientMap x) hp]
  change coordProj j (actionPullbackVector translationAction t testVector (quotientMap x)) = _
  rw [pullbackVector_translate]
  simp [testVector, frame_eq_basisVector, translate, coordProj, basisVector, PiLp.single_apply]

theorem testVector_translate_integral_zero (p : Torus) (j : Fin 4) :
    (∫ t : Circle, (if j = 0 then ((t * p 1 : Circle) : ℂ).re else 0) ∂circleHaar) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := (-1 : Circle))
  intro t
  simp
  split_ifs <;> ring

theorem testVector_haar_integrable : VectorHaarIntegrable translationAction testVector := by
  intro c x hx j
  simp only [vectorInChart_pullback_testVector c x hx]
  have hc : Continuous (fun t : Circle => if j = 0 then ((t * quotientMap x 1 : Circle) : ℂ).re else 0) := by
    split_ifs <;> fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem testVector_haar_average_zero : vectorPi0 translationAction testVector = 0 := by
  funext p
  have hx := (chartAt FourSpace p).map_source (mem_chart_source FourSpace p)
  simp only [vectorPi0, vectorInChart_pullback_testVector p (chartAt FourSpace p p) hx,
    testVector_translate_integral_zero, zero_smul, Finset.sum_const_zero, map_zero, Pi.zero_apply]

theorem flatMetric_invariant : IsInvariantCov2 translationAction flatMetric := by
  intro t
  funext p
  ext v w
  unfold actionPullbackCov2 pullbackCov2
  change bilinearPullback (flatMetric (translate t p)) (mfderiv I4 I4 (translate t) p) v w = _
  rw [translate_differential]
  change flatMetric (translate t p) v w = flatMetric p v w
  simp only [flatMetric, coframe_eq_coordProj]
  rfl

theorem projectedDefect_eq_unprojected (alpha : ℝ) (n : ℕ) :
    projectedDefect translationAction alpha n = unprojectedDefect alpha n := by
  simp [projectedDefect, covectorPiPerp, defect_haar_average_zero]

theorem translationAction_act : translationAction.act = translate := rfl

theorem testVector_nonzero_mode : IsNonzeroVector translationAction testVector :=
  testVector_haar_average_zero

end K24.Global.FlatTorus.Action20261024


/- Internal assembly: operator-difference/Difference.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators NNReal ENNReal Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus.Difference20261024
open Geometry20261024 Defect20261024 DefectCalculus

theorem coverCov2_injective : Function.Injective coverCov2 := by
  intro u v h
  funext p
  obtain ⟨x, rfl⟩ := quotientMap_surjective p
  have hi : (fun i j => u (quotientMap x) (basisVector i) (basisVector j)) =
      (fun i j => v (quotientMap x) (basisVector i) (basisVector j)) := by
    funext i j
    have hh := congrFun (congrFun (congrFun h x) i) j
    simpa only [coverCov2_eq] using hh
  calc
    u (quotientMap x) = matrixToBilinear (fun i j => u (quotientMap x) (basisVector i) (basisVector j)) :=
      (matrixToBilinear_recover (u (quotientMap x))).symm
    _ = matrixToBilinear (fun i j => v (quotientMap x) (basisVector i) (basisVector j)) := congrArg _ hi
    _ = v (quotientMap x) := matrixToBilinear_recover (v (quotientMap x))

theorem coverCovector_injective : Function.Injective coverCovector := by
  intro u v h
  funext p
  obtain ⟨x, rfl⟩ := quotientMap_surjective p
  have hi : (fun i => u (quotientMap x) (basisVector i)) = (fun i => v (quotientMap x) (basisVector i)) := by
    funext i
    have hh := congrFun (congrFun h x) i
    simpa only [coverCovector_eq] using hh
  calc
    u (quotientMap x) = coefficientsToCovector (fun i => u (quotientMap x) (basisVector i)) :=
      (coefficientsToCovector_recover (u (quotientMap x))).symm
    _ = coefficientsToCovector (fun i => v (quotientMap x) (basisVector i)) := congrArg _ hi
    _ = v (quotientMap x) := coefficientsToCovector_recover (v (quotientMap x))

theorem coverCov2_add (u v : RawCov2 Torus) :
    coverCov2 (u + v) = coverCov2 u + coverCov2 v := by
  funext x i j
  simp only [coverCov2_eq, Pi.add_apply, Matrix.add_apply, ContinuousLinearMap.add_apply]

theorem coverCovector_add (u v : RawCovector Torus) :
    coverCovector (u + v) = coverCovector u + coverCovector v := by
  funext x i
  simp only [coverCovector_eq, Pi.add_apply, Matrix.add_apply, ContinuousLinearMap.add_apply]

theorem lieTensorInChart_add_flat (Y : RawVector Torus) (u : RawCov2 Torus)
    (c : Torus) (x : FourSpace) (i j : Fin 4) :
    lieTensorInChart Y (flatMetric + u) c x i j =
      lieTensorInChart Y flatMetric c x i j + lieTensorInChart Y u c x i j := by
  unfold lieTensorInChart
  simp only [Geometry20261024.cov2InChart_cover, coverCov2_add, Pi.add_apply, Matrix.add_apply, flatMetric_lift]
  simp only [coordDeriv, fderiv_const_add, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    mul_zero, zero_add, mul_add, Finset.sum_add_distrib]
  ring

theorem lieTensor_add_flat (Y : RawVector Torus) (u : RawCov2 Torus) :
    lieTensor Y (flatMetric + u) = lieTensor Y flatMetric + lieTensor Y u := by
  apply coverCov2_injective
  funext x i j
  rw [coverCov2_add]
  simp only [Pi.add_apply, Matrix.add_apply, lieTensor, coverCov2_fromCoordinates, lieTensorInChart_add_flat]

theorem coordDeriv_add (f g : FourSpace → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Fin 4) (x : FourSpace) :
    coordDeriv (f + g) i x = coordDeriv f i x + coordDeriv g i x := by
  simp [coordDeriv, fderiv_add (hf x) (hg x)]

theorem bianchi_flat_add (u v : RawCov2 Torus)
    (hu : ∀ i j, Differentiable ℝ (fun x => coverCov2 u x i j))
    (hv : ∀ i j, Differentiable ℝ (fun x => coverCov2 v x i j)) :
    bianchi flatMetric (u + v) = bianchi flatMetric u + bianchi flatMetric v := by
  apply coverCovector_injective
  funext x j
  rw [coverCovector_add]
  simp only [Pi.add_apply, bianchi, coverCovector_fromCoordinates, bianchiInChart_flat,
    coverCov2_add, Matrix.add_apply]
  have hsU : Differentiable ℝ (fun y => ∑ a : Fin 4, coverCov2 u y a a) :=
    Differentiable.fun_sum (fun a _ => hu a a)
  have hsV : Differentiable ℝ (fun y => ∑ a : Fin 4, coverCov2 v y a a) :=
    Differentiable.fun_sum (fun a _ => hv a a)
  simp only [Finset.sum_add_distrib]
  simp_rw [show ∀ a : Fin 4, (fun y => coverCov2 u y a j + coverCov2 v y a j) =
    (fun y => coverCov2 u y a j) + (fun y => coverCov2 v y a j) from fun _ => rfl,
    coordDeriv_add _ _ (hu _ _) (hv _ _)]
  rw [show (fun y => (∑ a : Fin 4, coverCov2 u y a a) + ∑ a : Fin 4, coverCov2 v y a a) =
    (fun y => ∑ a : Fin 4, coverCov2 u y a a) + (fun y => ∑ a : Fin 4, coverCov2 v y a a) from rfl,
    coordDeriv_add _ _ hsU hsV]
  rw [Finset.sum_add_distrib]
  ring

def baselineLieCoefficients (x : FourSpace) (i j : Fin 4) : ℝ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then -Real.sin (x 1) else 0

theorem lieTensorInChart_flat (c : Torus) (x : FourSpace)
    (hx : quotientMap x ∈ (chartAt FourSpace c).source) (i j : Fin 4) :
    lieTensorInChart testVector flatMetric c x i j = baselineLieCoefficients x i j := by
  unfold lieTensorInChart
  simp only [Geometry20261024.cov2InChart_cover, flatMetric_lift,
    vectorInChart_testVector c x hx, vectorInChart_testVector_coordDeriv c x hx]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, baselineLieCoefficients, Matrix.one_apply,
      coordDeriv, basisVector, PiLp.single_apply]

theorem lieTensor_flat_lift (x : FourSpace) :
    coverCov2 (lieTensor testVector flatMetric) x = baselineLieCoefficients x := by
  funext i j
  rw [lieTensor, coverCov2_fromCoordinates,
    lieTensorInChart_flat (quotientMap x) (representative (quotientMap x))
      (by rw [quotientMap_representative]; exact mem_chart_source FourSpace (quotientMap x))]
  simp only [baselineLieCoefficients, sin_eq_of_quotientMap_eq
    (representative (quotientMap x)) x (quotientMap_representative (quotientMap x))]

theorem lieTensor_flat_coeff_differentiable (i j : Fin 4) :
    Differentiable ℝ (fun x => coverCov2 (lieTensor testVector flatMetric) x i j) := by
  simp only [lieTensor_flat_lift, baselineLieCoefficients]
  have h1 : Differentiable ℝ (fun x : FourSpace => x 1) := (coordProj 1).differentiable
  split_ifs
  · exact h1.sin.neg
  · exact differentiable_const _

theorem lieTensor_perturbation_coeff_differentiable (alpha : ℝ) (n : ℕ) (i j : Fin 4) :
    Differentiable ℝ (fun x => coverCov2 (lieTensor testVector (perturbation alpha n)) x i j) := by
  simp only [lieTensor_perturbation_lift, lieCoefficients, lie00, lie01,
    CoefficientSharpness.liftedOscillation_deriv, liftedOscillation]
  have h0 : Differentiable ℝ (fun x : FourSpace => x 0) := (coordProj 0).differentiable
  have h1 : Differentiable ℝ (fun x : FourSpace => x 1) := (coordProj 1).differentiable
  split_ifs <;> fun_prop

/-- Exact algebraic relation between the actual nearby-metric vector operators. -/
theorem actual_vector_operator_difference (alpha : ℝ) (n : ℕ) :
    vectorOperator flatMetric (nearbyMetric alpha n) testVector -
      vectorOperator flatMetric flatMetric testVector = unprojectedDefect alpha n := by
  unfold vectorOperator nearbyMetric
  rw [lieTensor_add_flat, bianchi_flat_add _ _ lieTensor_flat_coeff_differentiable
    (lieTensor_perturbation_coeff_differentiable alpha n)]
  exact add_sub_cancel_left _ _

/-- The projected identity uses the same genuine Haar projection on both sides. -/
theorem actualVectorDifference_eq_projectedDefect (rho : CircleAction Torus)
    (alpha : ℝ) (n : ℕ) :
    actualVectorDifference rho alpha n = projectedDefect rho alpha n := by
  unfold actualVectorDifference projectedDefect
  rw [actual_vector_operator_difference]

end K24.Global.FlatTorus.Difference20261024


/- Internal assembly: holder/ActualHolder.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal BigOperators
namespace K24.Global.FlatTorus.HolderBridge20261024

theorem coordDeriv_difference_le_derivative_distance
    (f : FourSpace → Fin 4 → ℝ) (hf : Differentiable ℝ f)
    (i j : Fin 4) (x y : FourSpace) :
    |coordDeriv (fun z => f z j) i x - coordDeriv (fun z => f z j) i y| ≤
      dist (iteratedFDerivWithin ℝ 1 f Set.univ x)
        (iteratedFDerivWithin ℝ 1 f Set.univ y) := by
  rw [dist_iteratedFDerivWithin_one f f uniqueDiffWithinAt_univ uniqueDiffWithinAt_univ,
    fderivWithin_univ, dist_eq_norm]
  simp only [coordDeriv, fderiv_apply (hf x) j, fderiv_apply (hf y) j,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have h := norm_le_pi_norm ((fderiv ℝ f x - fderiv ℝ f y) (basisVector i)) j
  have h' := (fderiv ℝ f x - fderiv ℝ f y).le_opNorm (basisVector i)
  have hb : ‖basisVector i‖ = 1 := by simp [basisVector]
  rw [hb, mul_one] at h'
  have heval : |(fderiv ℝ f x) (basisVector i) j - (fderiv ℝ f y) (basisVector i) j| ≤
      ‖(fderiv ℝ f x - fderiv ℝ f y) (basisVector i)‖ := by
    simpa only [sub_apply, Pi.sub_apply, Real.norm_eq_abs] using h
  exact heval.trans h'

theorem two_point_quotient_le_coordinateHolderNorm
    (alpha : ℝ≥0) (f : FourSpace → Fin 4 → ℝ) (hf : Differentiable ℝ f)
    (hfinite : coordinateHolderENorm 1 alpha Set.univ f < ⊤)
    (i j : Fin 4) (x y : FourSpace) (hxy : x ≠ y) :
    |coordDeriv (fun z => f z j) i x - coordDeriv (fun z => f z j) i y| /
        Real.rpow (dist x y) alpha ≤
      (coordinateHolderENorm 1 alpha Set.univ f).toReal := by
  let D := fun x : (Set.univ : Set FourSpace) => iteratedFDerivWithin ℝ 1 f Set.univ x
  have hle : eHolderNorm alpha D ≤ coordinateHolderENorm 1 alpha Set.univ f := by
    exact le_add_left le_rfl
  have hDf : eHolderNorm alpha D < ⊤ := lt_of_le_of_lt hle hfinite
  have hbound := (eHolderNorm_lt_top.mp hDf).holderWith.dist_le
    (⟨x, Set.mem_univ x⟩ : (Set.univ : Set FourSpace))
    (⟨y, Set.mem_univ y⟩ : (Set.univ : Set FourSpace))
  have hnum : |coordDeriv (fun z => f z j) i x - coordDeriv (fun z => f z j) i y| ≤
      (nnHolderNorm alpha D : ℝ) * Real.rpow (dist x y) alpha := by
    exact (coordDeriv_difference_le_derivative_distance f hf i j x y).trans hbound
  have hpos : 0 < Real.rpow (dist x y) (alpha : ℝ) :=
    Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  have hquot := (div_le_iff₀ hpos).mpr hnum
  apply hquot.trans
  exact ENNReal.toReal_mono hfinite.ne hle

end K24.Global.FlatTorus.HolderBridge20261024

namespace K24.Global.FlatTorus.HolderBridge20261024
open CoefficientSharpness

theorem expectedDefect_differentiable (alpha : ℝ) (n : ℕ) :
    Differentiable ℝ (expectedDefectCoefficients alpha n) := by
  apply differentiable_pi.mpr
  intro j
  simp only [expectedDefectCoefficients, liftedOscillation_deriv_two, liftedOscillation_deriv,
    liftedOscillation]
  have h0 : Differentiable ℝ (fun x : FourSpace => x 0) := (coordProj 0).differentiable
  have h1 : Differentiable ℝ (fun x : FourSpace => x 1) := (coordProj 1).differentiable
  by_cases hj0 : j = 0
  · simp only [hj0, ↓reduceIte]
    fun_prop
  · by_cases hj1 : j = 1 <;> simp [hj0, hj1] <;> fun_prop

theorem actual_defect_holder_lower_bound_of_coefficients
    (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n)
    (hcoeff : ∀ x : FourSpace,
      coverCovector (unprojectedDefect alpha.value n) x =
        expectedDefectCoefficients alpha.value n x)
    (hfinite : covectorHolderENorm 1 alpha.value (unprojectedDefect alpha.value n) < ⊤) :
    Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
      covectorHolderNorm 1 alpha.value (unprojectedDefect alpha.value n) := by
  have hfun : coverCovector (unprojectedDefect alpha.value n) =
      expectedDefectCoefficients alpha.value n := funext hcoeff
  unfold covectorHolderENorm at hfinite
  rw [hfun] at hfinite
  unfold covectorHolderNorm covectorHolderENorm
  rw [hfun]
  let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
  have hxy : (0 : FourSpace) ≠ y := by
    apply dist_pos.mp
    dsimp only [y]
    rw [distance_test_points n (by omega)]
    positivity
  have hbound := two_point_quotient_le_coordinateHolderNorm alpha.value
    (expectedDefectCoefficients alpha.value n) (expectedDefect_differentiable alpha.value n)
    hfinite 0 0 0 y hxy
  exact (expectedDefect_two_point_lower_bound (alpha.value : ℝ) n (by omega)).trans hbound

theorem actual_defect_holder_ENorm_lower_bound_of_coefficients
    (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n)
    (hcoeff : ∀ x : FourSpace,
      coverCovector (unprojectedDefect alpha.value n) x =
        expectedDefectCoefficients alpha.value n x) :
    ENNReal.ofReal (Real.rpow Real.pi (-(alpha.value : ℝ))) ≤
      covectorHolderENorm 1 alpha.value (unprojectedDefect alpha.value n) := by
  by_cases hfinite : covectorHolderENorm 1 alpha.value (unprojectedDefect alpha.value n) < ⊤
  · apply (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).mpr
    exact actual_defect_holder_lower_bound_of_coefficients alpha n hn hcoeff hfinite
  · have htop : covectorHolderENorm 1 alpha.value (unprojectedDefect alpha.value n) = ⊤ :=
      top_unique (not_lt.mp hfinite)
    rw [htop]
    exact le_top

end K24.Global.FlatTorus.HolderBridge20261024

namespace K24.Global.FlatTorus.Defect20261024

theorem actual_defect_holder_ENorm_lower_bound
    (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal (Real.rpow Real.pi (-(alpha.value : ℝ))) ≤
      covectorHolderENorm 1 alpha.value (unprojectedDefect alpha.value n) := by
  exact HolderBridge20261024.actual_defect_holder_ENorm_lower_bound_of_coefficients
    alpha n hn (geometric_defect_coefficients alpha.value n)

theorem actual_defect_holder_lower_bound
    (alpha : HolderExponent) (n : ℕ) (hn : 2 ≤ n)
    (hfinite : covectorHolderENorm 1 alpha.value (unprojectedDefect alpha.value n) < ⊤) :
    Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
      covectorHolderNorm 1 alpha.value (unprojectedDefect alpha.value n) := by
  exact HolderBridge20261024.actual_defect_holder_lower_bound_of_coefficients
    alpha n hn (geometric_defect_coefficients alpha.value n) hfinite

end K24.Global.FlatTorus.Defect20261024


/- Internal assembly: reduction/Base.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators NNReal ENNReal Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus.SharpnessReduction20261024
open Geometry20261024

theorem testVector_holder_ENorm_lower_bound (alpha : ℝ≥0) :
    (1 : ℝ≥0∞) ≤ vectorHolderENorm 3 alpha testVector := by
  have hnorm : ‖iteratedFDerivWithin ℝ 0 (coverVector testVector) Set.univ 0‖ = 1 := by
    simp [norm_iteratedFDerivWithin_zero, testVector_lift, basisVector]
  have hnn : ‖iteratedFDerivWithin ℝ 0 (coverVector testVector) Set.univ 0‖₊ = 1 :=
    NNReal.eq hnorm
  have hpoint : (1 : ℝ≥0∞) ≤ derivativeENorm 0 Set.univ (coverVector testVector) := by
    have h := le_iSup (fun x : (Set.univ : Set FourSpace) =>
      (‖iteratedFDerivWithin ℝ 0 (coverVector testVector) Set.univ x‖₊ : ℝ≥0∞))
      (⟨0, Set.mem_univ 0⟩ : (Set.univ : Set FourSpace))
    simpa only [hnn, ENNReal.coe_one, derivativeENorm] using h
  have hsum : derivativeENorm 0 Set.univ (coverVector testVector) ≤
      ∑ j ∈ Finset.range (3 + 1), derivativeENorm j Set.univ (coverVector testVector) :=
    Finset.single_le_sum (f := fun j => derivativeENorm j Set.univ (coverVector testVector))
      (fun _ _ => bot_le) (by norm_num)
  exact (hpoint.trans hsum).trans (le_add_right le_rfl)

theorem testVector_holderNorm_pos (alpha : ℝ≥0)
    (hfinite : vectorHolderENorm 3 alpha testVector < ⊤) :
    0 < vectorHolderNorm 3 alpha testVector := by
  have h := ENNReal.toReal_mono hfinite.ne (testVector_holder_ENorm_lower_bound alpha)
  have : (1 : ℝ) ≤ vectorHolderNorm 3 alpha testVector := by
    simpa [vectorHolderNorm] using h
  linarith

/-- A fixed positive lower bound cannot be dominated by a sequence tending to zero. -/
theorem shifted_bound_impossible (a b : ℕ → ℝ) (v c : ℝ)
    (hc : 0 < c) (ha : ∀ n, 2 ≤ n → c ≤ a n)
    (hb : Tendsto b atTop (𝓝 0)) :
    ¬ (∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n → a n ≤ K * b n * v) := by
  rintro ⟨K, hK, hbound⟩
  have ht : Tendsto (fun n => K * b n * v) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul hb).mul tendsto_const_nhds using 1 <;> simp
  have he : ∀ᶠ n : ℕ in atTop, c ≤ K * b n * v := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (ha n hn).trans (hbound n hn)
  exact (not_le_of_gt hc) (ge_of_tendsto ht he)

end K24.Global.FlatTorus.SharpnessReduction20261024

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal BigOperators
namespace K24.Global.FlatTorus.HolderEstimates20261024

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem holderWith_zero_of_norm_le (f : E → V) (B : ℝ≥0)
    (hB : ∀ x, ‖f x‖ ≤ B) : HolderWith (2 * B) 0 f := by
  intro x y
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist]
  apply ENNReal.ofReal_le_iff_le_toReal (by finiteness) |>.mpr
  simpa only [ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_ofNat] using
    (dist_le_norm_add_norm (f x) (f y)).trans (by linarith [hB x, hB y])

/-- Global boundedness and a derivative bound interpolate at the sharp real exponent. -/
theorem holderWith_of_norm_fderiv_bounds (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (f : E → V) (hf : Differentiable ℝ f) (B L : ℝ≥0)
    (hB : ∀ x, ‖f x‖ ≤ B) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) :
    HolderWith ((2 * B) ^ (1 - (alpha : ℝ)) * L ^ (alpha : ℝ)) alpha f := by
  have hzero := holderWith_zero_of_norm_le f B hB
  have hlip : LipschitzWith L f :=
    lipschitzWith_of_nnnorm_fderiv_le hf (fun x => hL x)
  have hone : HolderWith L 1 f := holderWith_one.mpr hlip
  have hsum : (1 - alpha) + alpha = (1 : ℝ≥0) := tsub_add_cancel_of_le ha
  have h := hzero.interpolate hone (t₁ := 1 - alpha) (t₂ := alpha) hsum
  simpa only [zero_mul, one_mul, zero_add, NNReal.coe_sub ha, NNReal.coe_one] using h

/-- A genuine full coordinate Hölder bound, with actual multilinear Fréchet derivatives. -/
theorem coordinateHolderENorm_le_of_derivative_bounds (k : ℕ)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (f : E → V)
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ≥0)
    (hB : ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    coordinateHolderENorm k alpha Set.univ f ≤
      (∑ j ∈ Finset.range (k + 1), (B j : ℝ≥0∞)) +
        (((2 * B k) ^ (1 - (alpha : ℝ)) * B (k + 1) ^ (alpha : ℝ) : ℝ≥0) : ℝ≥0∞) := by
  have hD : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)
  have hL : ∀ x, ‖fderiv ℝ (iteratedFDeriv ℝ k f) x‖ ≤ B (k + 1) := by
    intro x
    rw [norm_fderiv_iteratedFDeriv]
    exact hB (k + 1) le_rfl x
  have hholder := holderWith_of_norm_fderiv_bounds alpha ha
    (iteratedFDeriv ℝ k f) hD (B k) (B (k + 1)) (hB k (by omega)) hL
  have hrestrict : HolderWith ((2 * B k) ^ (1 - (alpha : ℝ)) * B (k + 1) ^ (alpha : ℝ)) alpha
      (fun x : (Set.univ : Set E) => iteratedFDerivWithin ℝ k f Set.univ x) := by
    intro x y
    simpa only [iteratedFDerivWithin_univ, Subtype.edist_eq] using hholder x y
  apply add_le_add ?_ hrestrict.eHolderNorm_le
  apply Finset.sum_le_sum
  intro j hj
  unfold derivativeENorm
  apply iSup_le
  intro x
  rw [iteratedFDerivWithin_univ]
  exact_mod_cast hB j (by have := Finset.mem_range.mp hj; omega) x

/-- Pointwise finite bounds through order `k+1` imply finite full `C^{k,alpha}` norm. -/
theorem coordinateHolderENorm_lt_top_of_derivative_bounds (k : ℕ)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (f : E → V)
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ≥0)
    (hB : ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    coordinateHolderENorm k alpha Set.univ f < ⊤ := by
  apply lt_of_le_of_lt (coordinateHolderENorm_le_of_derivative_bounds k alpha ha f hf B hB)
  simp only [ENNReal.add_lt_top, ENNReal.sum_lt_top, ENNReal.coe_lt_top, implies_true, and_self]

end K24.Global.FlatTorus.HolderEstimates20261024


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise
namespace K24.Global.FlatTorus.HolderEstimates20261024

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_iteratedFDeriv_sin_clm (L : E →L[ℝ] ℝ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => Real.sin (L y)) x‖ ≤ ‖L‖ ^ j := by
  change ‖iteratedFDeriv ℝ j (Real.sin ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (n := j) Real.contDiff_sin x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j Real.sin (L x)‖ * ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * ∏ _ : Fin j, ‖L‖ := by
      gcongr
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_sin_le_one j (L x)
    _ = ‖L‖ ^ j := by simp

theorem norm_iteratedFDeriv_cos_clm (L : E →L[ℝ] ℝ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => Real.cos (L y)) x‖ ≤ ‖L‖ ^ j := by
  change ‖iteratedFDeriv ℝ j (Real.cos ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (n := j) Real.contDiff_cos x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j Real.cos (L x)‖ * ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * ∏ _ : Fin j, ‖L‖ := by
      gcongr
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_cos_le_one j (L x)
    _ = ‖L‖ ^ j := by simp

theorem norm_iteratedFDeriv_sin_smul (L : E →L[ℝ] ℝ) (A : ℝ) (v : V)
    (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => (A * Real.sin (L y)) • v) x‖ ≤
      |A| * ‖L‖ ^ j * ‖v‖ := by
  let S : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight (A • v)
  have hf : ContDiff ℝ j (fun y => Real.sin (L y)) := Real.contDiff_sin.comp L.contDiff
  have heq : (fun y => (A * Real.sin (L y)) • v) = S ∘ (fun y => Real.sin (L y)) := by
    funext y
    change (A * Real.sin (L y)) • v = Real.sin (L y) • (A • v)
    rw [smul_smul, mul_comm]
  rw [heq]
  calc
    _ ≤ ‖S‖ * ‖iteratedFDeriv ℝ j (fun y => Real.sin (L y)) x‖ :=
      S.norm_iteratedFDeriv_comp_left hf.contDiffAt le_rfl
    _ ≤ ‖S‖ * ‖L‖ ^ j := by gcongr; exact norm_iteratedFDeriv_sin_clm L j x
    _ = |A| * ‖L‖ ^ j * ‖v‖ := by
      simp [S, ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
      ring

theorem norm_iteratedFDeriv_cos_smul (L : E →L[ℝ] ℝ) (A : ℝ) (v : V)
    (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => (A * Real.cos (L y)) • v) x‖ ≤
      |A| * ‖L‖ ^ j * ‖v‖ := by
  let S : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight (A • v)
  have hf : ContDiff ℝ j (fun y => Real.cos (L y)) := Real.contDiff_cos.comp L.contDiff
  have heq : (fun y => (A * Real.cos (L y)) • v) = S ∘ (fun y => Real.cos (L y)) := by
    funext y
    change (A * Real.cos (L y)) • v = Real.cos (L y) • (A • v)
    rw [smul_smul, mul_comm]
  rw [heq]
  calc
    _ ≤ ‖S‖ * ‖iteratedFDeriv ℝ j (fun y => Real.cos (L y)) x‖ :=
      S.norm_iteratedFDeriv_comp_left hf.contDiffAt le_rfl
    _ ≤ ‖S‖ * ‖L‖ ^ j := by gcongr; exact norm_iteratedFDeriv_cos_clm L j x
    _ = |A| * ‖L‖ ^ j * ‖v‖ := by
      simp [S, ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
      ring

theorem norm_coordProj_le_one (i : Fin 4) : ‖coordProj i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖x i‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i

def singleTensor : Mat4 := fun i j => if i = 0 ∧ j = 0 then 1 else 0

theorem norm_singleTensor_le_one : ‖singleTensor‖ ≤ 1 := by
  apply (Matrix.norm_le_iff (by norm_num)).mpr
  intro i j
  simp only [singleTensor]
  split_ifs <;> norm_num

theorem perturbation_cover_eq_sin_smul (alpha : ℝ) (n : ℕ) :
    coverCov2 (perturbation alpha n) = fun x =>
      (amplitude alpha n * Real.sin (((n : ℝ) • coordProj 0) x)) • singleTensor := by
  funext x i j
  rw [Geometry20261024.perturbation_lift]
  change (if i = 0 ∧ j = 0 then amplitude alpha n * Real.sin ((n : ℝ) * x 0) else 0) =
    (amplitude alpha n * Real.sin ((n : ℝ) * x 0)) * (if i = 0 ∧ j = 0 then 1 else 0)
  split_ifs <;> simp

theorem perturbation_derivative_bound (alpha : ℝ) (n j : ℕ) (x : FourSpace) :
    ‖iteratedFDeriv ℝ j (coverCov2 (perturbation alpha n)) x‖ ≤
      |amplitude alpha n| * (n : ℝ)^j := by
  rw [perturbation_cover_eq_sin_smul]
  have h := norm_iteratedFDeriv_sin_smul ((n : ℝ) • coordProj 0)
    (amplitude alpha n) singleTensor j x
  calc
    _ ≤ |amplitude alpha n| * ‖(n : ℝ) • coordProj 0‖ ^ j * ‖singleTensor‖ := h
    _ ≤ |amplitude alpha n| * ((n : ℝ) * 1)^j * 1 := by
      gcongr
      · simpa only [norm_smul, Real.norm_eq_abs, Nat.abs_cast] using
          mul_le_mul_of_nonneg_left (norm_coordProj_le_one 0) (Nat.cast_nonneg n)
      · exact norm_singleTensor_le_one
    _ = _ := by simp

theorem testVector_derivative_bound (j : ℕ) (x : FourSpace) :
    ‖iteratedFDeriv ℝ j (coverVector testVector) x‖ ≤ 1 := by
  have heq : coverVector testVector = fun x => (1 * Real.cos (coordProj 1 x)) • basisVector 0 := by
    funext x
    simpa using Geometry20261024.testVector_lift x
  rw [heq]
  have h := norm_iteratedFDeriv_cos_smul (coordProj 1) 1 (basisVector 0) j x
  simp only [abs_one, one_mul] at h
  have hb : ‖basisVector 0‖ = 1 := by simp [basisVector]
  rw [hb, mul_one] at h
  simpa only [one_mul] using
    h.trans (by simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_coordProj_le_one 1) j)

theorem perturbation_cover_smooth (alpha : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (coverCov2 (perturbation alpha n)) := by
  rw [perturbation_cover_eq_sin_smul]
  fun_prop

theorem testVector_cover_smooth : ContDiff ℝ ∞ (coverVector testVector) := by
  have heq : coverVector testVector = fun x => Real.cos (coordProj 1 x) • basisVector 0 := by
    funext x
    exact Geometry20261024.testVector_lift x
  rw [heq]
  fun_prop

end K24.Global.FlatTorus.HolderEstimates20261024


namespace K24.Global.FlatTorus.HolderEstimates20261024

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

def BoundedSmooth (f : E → V) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ j : ℕ, ∃ B : ℝ≥0, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B

theorem BoundedSmooth.coordinateHolderENorm_lt_top {f : E → V}
    (hf : BoundedSmooth f) (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    coordinateHolderENorm k alpha Set.univ f < ⊤ := by
  classical
  choose B hB using hf.2
  exact coordinateHolderENorm_lt_top_of_derivative_bounds k alpha ha f hf.1 B
    (fun j _ x => hB j x)

theorem BoundedSmooth.add {f g : E → V} (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro j
  obtain ⟨B, hB⟩ := hf.2 j
  obtain ⟨C, hC⟩ := hg.2 j
  refine ⟨B + C, fun x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply
    ((hf.1.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt)
    ((hg.1.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add (hB x) (hC x))

theorem BoundedSmooth.clm {f : E → V} (hf : BoundedSmooth f) (L : V →L[ℝ] W) :
    BoundedSmooth (fun x => L (f x)) := by
  refine ⟨L.contDiff.comp hf.1, ?_⟩
  intro j
  obtain ⟨B, hB⟩ := hf.2 j
  refine ⟨‖L‖₊ * B, fun x => ?_⟩
  have h := L.norm_iteratedFDeriv_comp_left (x := x) hf.1.contDiffAt
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  exact h.trans (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))

theorem BoundedSmooth.smul_const {f : E → ℝ} (hf : BoundedSmooth f) (v : V) :
    BoundedSmooth (fun x => f x • v) :=
  hf.clm ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

theorem BoundedSmooth.smul {f : E → ℝ} {g : E → V}
    (hf : BoundedSmooth f) (hg : BoundedSmooth g) :
    BoundedSmooth (fun x => f x • g x) := by
  classical
  refine ⟨hf.1.smul hg.1, ?_⟩
  choose B hB using hf.2
  choose C hC using hg.2
  intro j
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ≥0) * B i * C (j - i), fun x => ?_⟩
  have h := norm_iteratedFDeriv_smul_le hf.1 hg.1 x
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  apply h.trans
  push_cast
  apply Finset.sum_le_sum
  intro i hi
  gcongr
  · exact hB i x
  · exact hC (j - i) x

theorem boundedSmooth_sin_clm (L : E →L[ℝ] ℝ) :
    BoundedSmooth (fun x => Real.sin (L x)) := by
  refine ⟨Real.contDiff_sin.comp L.contDiff, fun j => ⟨‖L‖₊ ^ j, ?_⟩⟩
  exact norm_iteratedFDeriv_sin_clm L j

theorem boundedSmooth_cos_clm (L : E →L[ℝ] ℝ) :
    BoundedSmooth (fun x => Real.cos (L x)) := by
  refine ⟨Real.contDiff_cos.comp L.contDiff, fun j => ⟨‖L‖₊ ^ j, ?_⟩⟩
  exact norm_iteratedFDeriv_cos_clm L j

theorem expectedDefect_boundedSmooth (alpha : ℝ) (n : ℕ) :
    BoundedSmooth (expectedDefectCoefficients alpha n) := by
  let L : FourSpace →L[ℝ] ℝ := (n : ℝ) • coordProj 0
  let a : ℝ := amplitude alpha n * (1 + (n : ℝ)^2 / 2)
  let b : ℝ := amplitude alpha n * (n : ℝ) / 2
  let e0 : Fin 4 → ℝ := Pi.single 0 1
  let e1 : Fin 4 → ℝ := Pi.single 1 1
  have h0 := ((boundedSmooth_cos_clm (coordProj 1)).smul
    (boundedSmooth_sin_clm L)).smul_const (a • e0)
  have h1 := ((boundedSmooth_sin_clm (coordProj 1)).smul
    (boundedSmooth_cos_clm L)).smul_const (b • e1)
  have heq : expectedDefectCoefficients alpha n = fun x =>
      (Real.cos (coordProj 1 x) • Real.sin (L x)) • (a • e0) +
      (Real.sin (coordProj 1 x) • Real.cos (L x)) • (b • e1) := by
    funext x j
    fin_cases j <;>
      simp [expectedDefectCoefficients, CoefficientSharpness.liftedOscillation_deriv,
        CoefficientSharpness.liftedOscillation_deriv_two, liftedOscillation,
        L, a, b, e0, e1, Pi.single_apply, Geometry20261024.coordProj_apply] <;> ring
  rw [heq]
  exact h0.add h1

theorem actual_defect_holder_finite (alpha : HolderExponent) (n k : ℕ) :
    covectorHolderENorm k alpha.value (unprojectedDefect alpha.value n) < ⊤ := by
  unfold covectorHolderENorm
  have heq : coverCovector (unprojectedDefect alpha.value n) =
      expectedDefectCoefficients alpha.value n :=
    funext (Defect20261024.geometric_defect_coefficients alpha.value n)
  rw [heq]
  exact (expectedDefect_boundedSmooth alpha.value n).coordinateHolderENorm_lt_top
    k alpha.value alpha.lessThanOne.le

theorem perturbation_holder_finite (alpha : HolderExponent) (n k : ℕ) :
    tensorHolderENorm k alpha.value (perturbation alpha.value n) < ⊤ := by
  apply coordinateHolderENorm_lt_top_of_derivative_bounds k alpha.value alpha.lessThanOne.le
    _ (perturbation_cover_smooth alpha.value n)
    (fun j => ‖amplitude alpha.value n‖₊ * (n : ℝ≥0) ^ j)
  intro j hj x
  simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, coe_nnnorm,
    Real.norm_eq_abs] using perturbation_derivative_bound alpha.value n j x

theorem testVector_holder_finite (alpha : HolderExponent) (k : ℕ) :
    vectorHolderENorm k alpha.value testVector < ⊤ := by
  apply coordinateHolderENorm_lt_top_of_derivative_bounds k alpha.value alpha.lessThanOne.le
    _ testVector_cover_smooth (fun _ => 1)
  intro j hj x
  exact testVector_derivative_bound j x

end K24.Global.FlatTorus.HolderEstimates20261024


namespace K24.Global.FlatTorus.HolderEstimates20261024

/-- Explicit amplitude-frequency bound for the full, genuine tensor Hölder norm. -/
theorem perturbation_holder_frequency_bound (alpha : HolderExponent) (n k : ℕ) :
    tensorHolderNorm k alpha.value (perturbation alpha.value n) ≤
      (∑ j ∈ Finset.range (k + 1), |amplitude alpha.value n| * (n : ℝ)^j) +
        (2 * (|amplitude alpha.value n| * (n : ℝ)^k)) ^ (1 - (alpha.value : ℝ)) *
          (|amplitude alpha.value n| * (n : ℝ)^(k + 1)) ^ (alpha.value : ℝ) := by
  let B : ℕ → ℝ≥0 := fun j => ‖amplitude alpha.value n‖₊ * (n : ℝ≥0)^j
  have hB : ∀ j ≤ k + 1, ∀ x : FourSpace,
      ‖iteratedFDeriv ℝ j (coverCov2 (perturbation alpha.value n)) x‖ ≤ B j := by
    intro j hj x
    exact perturbation_derivative_bound alpha.value n j x
  have h := coordinateHolderENorm_le_of_derivative_bounds k alpha.value alpha.lessThanOne.le
    _ (perturbation_cover_smooth alpha.value n) B hB
  have h' : tensorHolderENorm k alpha.value (perturbation alpha.value n) ≤
      ((∑ j ∈ Finset.range (k + 1), B j) +
        (2 * B k) ^ (1 - (alpha.value : ℝ)) * B (k + 1) ^ (alpha.value : ℝ) : ℝ≥0) := by
    simpa only [tensorHolderENorm, ENNReal.coe_add, ENNReal.ofNNReal_finsetSum] using h
  have hr := ENNReal.toReal_mono ENNReal.coe_ne_top h'
  simpa only [tensorHolderNorm, ENNReal.coe_toReal, NNReal.coe_add, NNReal.coe_sum,
    NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_pow, NNReal.coe_ofNat,
    NNReal.coe_natCast, coe_nnnorm, Real.norm_eq_abs, B] using hr

end K24.Global.FlatTorus.HolderEstimates20261024


namespace K24.Global.FlatTorus.HolderEstimates20261024
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateHolderENorm_zero (k : ℕ) (alpha : ℝ≥0) :
    coordinateHolderENorm k alpha Set.univ (0 : E → V) = 0 := by
  simp [coordinateHolderENorm, derivativeENorm]
  exact eHolderNorm_const _ alpha 0

theorem perturbation_zero_frequency (alpha : ℝ) : perturbation alpha 0 = 0 := by
  funext p
  ext v w
  simp [perturbation, oscillatingScalar]

theorem perturbation_holderNorm_zero_frequency (alpha : HolderExponent) (k : ℕ) :
    tensorHolderNorm k alpha.value (perturbation alpha.value 0) = 0 := by
  rw [perturbation_zero_frequency]
  have heq : coverCov2 (0 : RawCov2 Torus) = 0 := by
    funext x i j
    simp [coverCov2, pullbackCov2]
  simp [tensorHolderNorm, tensorHolderENorm, heq, coordinateHolderENorm_zero]

end K24.Global.FlatTorus.HolderEstimates20261024


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace K24.Global.FlatTorus.HolderEstimates20261024

theorem amplitude_nonneg (alpha : ℝ) (n : ℕ) : 0 ≤ amplitude alpha n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem amplitude_mul_pow_eq (alpha : ℝ) (n k : ℕ) (hn : 0 < n) :
    amplitude alpha n * (n : ℝ)^k = Real.rpow (n : ℝ) ((k : ℝ) - 3 - alpha) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold amplitude
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_add hnR]
  congr 1
  ring

/-- The real Hölder interpolation term has exactly the required frequency power. -/
theorem wave_interpolation_scale (alpha : ℝ) (n k : ℕ) (hn : 0 < n) :
    Real.rpow (2 * (amplitude alpha n * (n : ℝ)^k)) (1 - alpha) *
        Real.rpow (amplitude alpha n * (n : ℝ)^(k + 1)) alpha =
      Real.rpow 2 (1 - alpha) * Real.rpow (n : ℝ) ((k : ℝ) - 3) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [amplitude_mul_pow_eq alpha n k hn, amplitude_mul_pow_eq alpha n (k + 1) hn]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnR.le _)]
  rw [← Real.rpow_mul hnR.le, ← Real.rpow_mul hnR.le, mul_assoc, ← Real.rpow_add hnR]
  congr 2
  push_cast
  ring

/-- The full bound, including every lower-order derivative and the top Hölder seminorm. -/
def waveHolderScale (alpha : ℝ) (n k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), amplitude alpha n * (n : ℝ)^j) +
    Real.rpow (2 * (amplitude alpha n * (n : ℝ)^k)) (1 - alpha) *
      Real.rpow (amplitude alpha n * (n : ℝ)^(k + 1)) alpha

theorem waveHolderScale_bound (alpha : ℝ) (ha : 0 ≤ alpha) (n k : ℕ) (hn : 1 ≤ n) :
    waveHolderScale alpha n k ≤ ((k : ℝ) + 3) * Real.rpow (n : ℝ) ((k : ℝ) - 3) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hsum : (∑ j ∈ Finset.range (k + 1), amplitude alpha n * (n : ℝ)^j) ≤
      ((k : ℝ) + 1) * Real.rpow (n : ℝ) ((k : ℝ) - 3) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (k + 1), Real.rpow (n : ℝ) ((k : ℝ) - 3) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [amplitude_mul_pow_eq alpha n j hn0]
        apply Real.rpow_le_rpow_of_exponent_le hnR
        have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        linarith
      _ = _ := by simp
  have htwo : Real.rpow 2 (1 - alpha) ≤ 2 := by
    calc
      _ ≤ Real.rpow 2 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := by norm_num
  unfold waveHolderScale
  rw [wave_interpolation_scale alpha n k hn0]
  have hnonneg : 0 ≤ Real.rpow (n : ℝ) ((k : ℝ) - 3) := Real.rpow_nonneg (by positivity) _
  nlinarith [mul_le_mul_of_nonneg_right htwo hnonneg]

theorem waveHolderScale_order_two (alpha : ℝ) (ha : 0 ≤ alpha) (n : ℕ) (hn : 1 ≤ n) :
    waveHolderScale alpha n 2 ≤ 5 / (n : ℝ) := by
  have h := waveHolderScale_bound alpha ha n 2 hn
  simpa only [Real.rpow_eq_pow, Nat.cast_ofNat, show (2 : ℝ) + 3 = 5 by norm_num,
    show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one, div_eq_mul_inv] using h

theorem waveHolderScale_order_three (alpha : ℝ) (ha : 0 ≤ alpha) (n : ℕ) (hn : 1 ≤ n) :
    waveHolderScale alpha n 3 ≤ 6 := by
  have h := waveHolderScale_bound alpha ha n 3 hn
  norm_num at h ⊢
  exact h

end K24.Global.FlatTorus.HolderEstimates20261024


namespace K24.Global.FlatTorus.HolderEstimates20261024

theorem perturbation_holderNorm_le_waveHolderScale (alpha : HolderExponent) (n k : ℕ) :
    tensorHolderNorm k alpha.value (perturbation alpha.value n) ≤
      waveHolderScale alpha.value n k := by
  simpa only [waveHolderScale, abs_of_nonneg (amplitude_nonneg alpha.value n),
    Real.rpow_eq_pow] using perturbation_holder_frequency_bound alpha n k

theorem perturbation_holderNorm_two_bound (alpha : HolderExponent) (n : ℕ) (hn : 1 ≤ n) :
    tensorHolderNorm 2 alpha.value (perturbation alpha.value n) ≤ 5 / (n : ℝ) :=
  (perturbation_holderNorm_le_waveHolderScale alpha n 2).trans
    (waveHolderScale_order_two alpha.value alpha.value.coe_nonneg n hn)

theorem perturbation_holderNorm_three_bound (alpha : HolderExponent) (n : ℕ) :
    tensorHolderNorm 3 alpha.value (perturbation alpha.value n) ≤ 6 := by
  by_cases hn : n = 0
  · subst n
    rw [perturbation_holderNorm_zero_frequency]
    norm_num
  · exact (perturbation_holderNorm_le_waveHolderScale alpha n 3).trans
      (waveHolderScale_order_three alpha.value alpha.value.coe_nonneg n (by omega))

theorem perturbation_holderNorm_two_tendsto_zero (alpha : HolderExponent) :
    Tendsto (fun n : ℕ => tensorHolderNorm 2 alpha.value (perturbation alpha.value n))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => ENNReal.toReal_nonneg)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact perturbation_holderNorm_two_bound alpha n hn

end K24.Global.FlatTorus.HolderEstimates20261024

namespace K24.Global.FlatTorus.SharpnessCompleted20261024
open Geometry20261024 Metric20261024 Action20261024 Difference20261024
open Defect20261024 HolderEstimates20261024 SharpnessReduction20261024

theorem sharpness : SharpnessStatement := by
  intro alpha
  have hV := testVector_holder_finite alpha 3
  have hlower : ∀ n : ℕ, 2 ≤ n →
      Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
        covectorHolderNorm 1 alpha.value (projectedDefect translationAction alpha.value n) := by
    intro n hn
    rw [projectedDefect_eq_unprojected]
    exact actual_defect_holder_lower_bound alpha n hn (actual_defect_holder_finite alpha n 1)
  refine ⟨torus_atlas_smooth, translationAction, 6, translationAction_act, by norm_num,
    flatMetric_isMetric, flatMetric_invariant, testVector_haar_integrable,
    testVector_nonzero_mode, hV, testVector_holderNorm_pos alpha.value hV, ?_,
    perturbation_holderNorm_two_tendsto_zero alpha, ?_, ?_⟩
  · intro n
    refine ⟨perturbation_holder_finite alpha n 2, perturbation_holder_finite alpha n 3,
      ?_, defect_haar_integrable alpha.value n, perturbation_holderNorm_three_bound alpha n⟩
    rw [projectedDefect_eq_unprojected]
    exact actual_defect_holder_finite alpha n 1
  · intro n hn
    exact ⟨nearbyMetric_isMetric alpha n hn, hlower n hn,
      actualVectorDifference_eq_projectedDefect translationAction alpha.value n⟩
  · apply shifted_bound_impossible
      (fun n => covectorHolderNorm 1 alpha.value (actualVectorDifference translationAction alpha.value n))
      (fun n => tensorHolderNorm 2 alpha.value (perturbation alpha.value n))
      (vectorHolderNorm 3 alpha.value testVector) (Real.rpow Real.pi (-(alpha.value : ℝ)))
      (Real.rpow_pos_of_pos Real.pi_pos _) ?_ (perturbation_holderNorm_two_tendsto_zero alpha)
    intro n hn
    rw [actualVectorDifference_eq_projectedDefect]
    exact hlower n hn

end K24.Global.FlatTorus.SharpnessCompleted20261024

open K24.Global K24.Global.FlatTorus

theorem solution : K24.Global.FlatTorus.SharpnessStatement :=
  K24.Global.FlatTorus.SharpnessCompleted20261024.sharpness

#print axioms K24.Global.FlatTorus.Geometry20261024.torus_atlas_smooth
#print axioms K24.Global.FlatTorus.Defect20261024.geometric_defect_coefficients
#print axioms K24.Global.FlatTorus.Action20261024.translationAction
#print axioms K24.Global.FlatTorus.Action20261024.defect_haar_integrable
#print axioms K24.Global.FlatTorus.Action20261024.defect_haar_average_zero
#print axioms K24.Global.FlatTorus.Metric20261024.nearbyMetric_isMetric
#print axioms K24.Global.FlatTorus.HolderEstimates20261024.perturbation_holderNorm_three_bound
#print axioms K24.Global.FlatTorus.HolderEstimates20261024.perturbation_holderNorm_two_tendsto_zero
#print axioms K24.Global.FlatTorus.HolderEstimates20261024.actual_defect_holder_finite
#print axioms K24.Global.FlatTorus.Difference20261024.actualVectorDifference_eq_projectedDefect
#print axioms K24.Global.FlatTorus.SharpnessCompleted20261024.sharpness
#print axioms solution
