-- Prove2me | solution 1 for K24.Global.nativeLieTensorRegularity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:04:22.64143+00:00
-- url     : https://prove2.me/submissions/9501effa-c394-4608-ba07-07a7e8bf1a1b

import Definitions.Def_K24GlobalGeometry


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.K24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- Genuine coordinate differentiation lowers C2 to C1 on an open domain. -/
theorem coordDeriv_contDiffOn {s : Set FourSpace} (hs : IsOpen s)
    (f : FourSpace → ℝ) (hf : ContDiffOn ℝ 2 f s) (i : Fin 4) :
    ContDiffOn ℝ 1 (fun x => coordDeriv f i x) s := by
  exact (hf.fderiv_of_isOpen hs (by norm_num)).clm_apply contDiffOn_const

/-- Native tensor coefficient regularity in a fixed canonical chart. -/
theorem cov2_coefficient_contDiffOn (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (c : M) (i j : Fin 4) :
    ContDiffOn ℝ 2 (fun x => cov2InChart g c x i j) (chartAt FourSpace c).target := by
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) i) j

/-- Native vector coefficient regularity in a fixed canonical chart. -/
theorem vector_coefficient_contDiffOn (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (p : Fin 4) :
    ContDiffOn ℝ 2 (fun x => vectorInChart Y c x p) (chartAt FourSpace c).target := by
  exact (coordProj p).contDiff.comp_contDiffOn (hY c)

/-- The genuine Lie coefficient formula is C1 in every fixed canonical chart. -/
theorem lieTensorInChart_contDiffOn (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) (c : M) :
    ContDiffOn ℝ 1 (lieTensorInChart Y g c) (chartAt FourSpace c).target := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply ContDiffOn.sum
  intro p _
  have hgij := cov2_coefficient_contDiffOn g hg c i j
  have hgpj := cov2_coefficient_contDiffOn g hg c p j
  have hgip := cov2_coefficient_contDiffOn g hg c i p
  have hYp := vector_coefficient_contDiffOn Y hY c p
  have hopen := (chartAt FourSpace c).open_target
  exact (((hYp.of_le (by norm_num)).mul (coordDeriv_contDiffOn hopen _ hgij p)).add
    ((coordDeriv_contDiffOn hopen _ hYp i).mul (hgpj.of_le (by norm_num)))).add
      ((coordDeriv_contDiffOn hopen _ hYp j).mul (hgip.of_le (by norm_num)))


end K24.Global.K24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.K24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

/-- The actual derivative from c-coordinates to d-coordinates. -/
def chartTransitionDerivative (c d : M) (x : FourSpace) : FourSpace →L[ℝ] FourSpace :=
  (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm x)).comp
    (mfderiv I4 I4 (chartAt FourSpace c).symm x)

@[simp] theorem matrixToBilinear_basis (A : Mat4) (i j : Fin 4) :
    matrixToBilinear A (basisVector i) (basisVector j) = A i j := by
  simp [matrixToBilinear, basisVector, coordProj, Pi.single_apply]

/-- The prescribed coefficient matrix is recovered inside its own chart. -/
theorem cov2InChart_fixed_reconstruction (c : M) (A : FourSpace → Mat4)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    cov2InChart (fun p => cov2FromChartAt c p (A (chartAt FourSpace c p))) c x = A x := by
  have hdi : ∀ v : FourSpace,
      mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
        (mfderiv I4 I4 (chartAt FourSpace c).symm x v) = v := by
    intro v
    exact congrArg (fun D => D v) ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hx)
  ext i j
  change matrixToBilinear (A ((chartAt FourSpace c) ((chartAt FourSpace c).symm x)))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i)))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))) = A x i j
  rw [hdi, hdi, (chartAt FourSpace c).right_inv hx, matrixToBilinear_basis]

/-- Actual tensor coefficients satisfy the genuine two-covariant transition law. -/
theorem cov2InChart_transition (u : RawCov2 M) (c d : M) (x : FourSpace)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    matrixToBilinear (cov2InChart u c x) =
      bilinearPullback
        (matrixToBilinear (cov2InChart u d
          (chartAt FourSpace d ((chartAt FourSpace c).symm x))))
        (chartTransitionDerivative c d x) := by
  let p := (chartAt FourSpace c).symm x
  let dc : FourSpace →L[ℝ] TangentSpace I4 p := mfderiv I4 I4 (chartAt FourSpace c).symm x
  have hr := cov2_chart_recovery u d p hd
  have hrec := matrixToBilinear_recover (bilinearPullback (u p) dc)
  change matrixToBilinear (fun i j => u p (dc (basisVector i)) (dc (basisVector j))) = _
  erw [hrec]
  ext v w
  have h := congrArg (fun B => B (dc v) (dc w)) hr
  exact h.symm

/-- A coefficient family transforms by the real chart derivatives on every overlap. -/
def Cov2CoordinateCompatible (A : M → FourSpace → Mat4) : Prop :=
  ∀ (c d p : M), p ∈ (chartAt FourSpace c).source →
    p ∈ (chartAt FourSpace d).source →
    matrixToBilinear (A c (chartAt FourSpace c p)) =
      bilinearPullback (matrixToBilinear (A d (chartAt FourSpace d p)))
        (chartTransitionDerivative c d (chartAt FourSpace c p))

/-- Coordinate compatibility implies equality of the actual reconstructed fibers. -/
theorem compatible_reconstructions (A : M → FourSpace → Mat4)
    (hA : Cov2CoordinateCompatible A) (c d p : M)
    (hc : p ∈ (chartAt FourSpace c).source)
    (hd : p ∈ (chartAt FourSpace d).source) :
    cov2FromChartAt c p (A c (chartAt FourSpace c p)) =
      cov2FromChartAt d p (A d (chartAt FourSpace d p)) := by
  have hdi : ∀ v : TangentSpace I4 p,
      mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p v) = v := by
    intro v
    exact congrArg (fun D => D v) ((mdifferentiable_chart (I := I4) c).symm_comp_deriv hc)
  have hcomp := hA c d p hc hd
  ext v w
  change matrixToBilinear (A c (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c) p v)
      (mfderiv I4 I4 (chartAt FourSpace c) p w) = _
  rw [hcomp]
  change matrixToBilinear (A d (chartAt FourSpace d p))
    (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p v)))
    (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p w))) = _
  rw [hdi, hdi, (chartAt FourSpace c).left_inv hc]
  rfl

/-- A compatible coefficient family is recovered from the native global reconstruction. -/
theorem cov2InChart_reconstruction (A : M → FourSpace → Mat4)
    (hA : Cov2CoordinateCompatible A) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    cov2InChart (cov2FromCoordinates A) c x = A c x := by
  have hp : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target hx
  have hrec := compatible_reconstructions A hA c ((chartAt FourSpace c).symm x)
    ((chartAt FourSpace c).symm x) hp (mem_chart_source FourSpace _)
  have hlocal := cov2InChart_fixed_reconstruction c (A c) x hx
  ext i j
  change cov2FromChartAt ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm x)
    (A ((chartAt FourSpace c).symm x)
      (chartAt FourSpace ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm x)))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j)) = A c x i j
  rw [← hrec]
  exact congrArg (fun B => B i j) hlocal

/-- Compatible genuinely Ck coefficients glue to a genuinely Ck native global tensor. -/
theorem cov2FromCoordinates_contDiff (A : M → FourSpace → Mat4)
    (hA : Cov2CoordinateCompatible A) (k : ℕ∞ω)
    (hregular : ∀ c : M, ContDiffOn ℝ k (A c) (chartAt FourSpace c).target) :
    Cov2ContDiff k (cov2FromCoordinates A) := by
  intro c
  apply (hregular c).congr
  intro x hx
  exact cov2InChart_reconstruction A hA c x hx

/-- The remaining global Lie obligation is precisely the genuine overlap law. -/
theorem lieTensor_contDiff_of_compatible (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y)
    (hcompat : Cov2CoordinateCompatible (lieTensorInChart Y g)) :
    Cov2ContDiff 1 (lieTensor Y g) := by
  exact cov2FromCoordinates_contDiff (lieTensorInChart Y g) hcompat 1
    (lieTensorInChart_contDiffOn g Y hg hY)


end K24.Global.K24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24REG

abbrev Bilinear4 := FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)

/-- Evaluation of the actual Euclidean Lie derivative on two fixed vectors. -/
def lieBilinearEval (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) : ℝ :=
  fderiv ℝ (fun y => Q y a b) x (V x) +
    Q x (fderiv ℝ V x a) b + Q x a (fderiv ℝ V x b)

theorem fderiv_bilinear_eval (Q : FourSpace → Bilinear4) (x a b v : FourSpace)
    (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun y => Q y a b) x v = fderiv ℝ Q x v a b := by
  have h := (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).clm_apply
    (hasFDerivAt_const b x)
  rw [h.fderiv]
  simp

/-- The genuine derivative of a tensor pullback contains both Jacobian derivative terms. -/
theorem fderiv_bilinear_pullback_eval
    (F : FourSpace → FourSpace) (Q : FourSpace → Bilinear4)
    (x a b v : FourSpace)
    (hF : DifferentiableAt ℝ F x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hQ : DifferentiableAt ℝ Q (F x)) :
    fderiv ℝ (fun y => bilinearPullback (Q (F y)) (fderiv ℝ F y) a b) x v =
      fderiv ℝ Q (F x) (fderiv ℝ F x v) (fderiv ℝ F x a) (fderiv ℝ F x b) +
      Q (F x) (fderiv ℝ (fderiv ℝ F) x v a) (fderiv ℝ F x b) +
      Q (F x) (fderiv ℝ F x a) (fderiv ℝ (fderiv ℝ F) x v b) := by
  have ha := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const a x)
  have hb := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const b x)
  have hQF : HasFDerivAt (fun y => Q (F y))
      ((fderiv ℝ Q (F x)).comp (fderiv ℝ F x)) x :=
    by simpa only [Function.comp_def] using
      (HasFDerivAt.comp x (f := F) (g := Q) hQ.hasFDerivAt hF.hasFDerivAt)
  have h := (hQF.clm_apply ha).clm_apply hb
  change fderiv ℝ (fun y => Q (F y) (fderiv ℝ F y a) (fderiv ℝ F y b)) x v = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.comp_zero, map_add]
  ring

/-- Differentiate the actual relation between two representations of a vector field. -/
theorem vector_relation_derivative
    (F V W : FourSpace → FourSpace) (x a : FourSpace)
    (hF : DifferentiableAt ℝ F x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hV : DifferentiableAt ℝ V (F x)) (hW : DifferentiableAt ℝ W x)
    (hrel : (fun y => V (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (W y))) :
    fderiv ℝ V (F x) (fderiv ℝ F x a) =
      fderiv ℝ F x (fderiv ℝ W x a) + fderiv ℝ (fderiv ℝ F) x a (W x) := by
  have h := hrel.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x hV hF, fderiv_clm_apply hJ hW] at h
  exact congrArg (fun D => D a) h

/-- Euclidean naturality follows from the actual pullback and vector relations.
The Hessian terms cancel by symmetry of the genuine second derivative. -/
theorem lieBilinearEval_pullback
    (F V W : FourSpace → FourSpace) (Q : FourSpace → Bilinear4)
    (x a b : FourSpace)
    (hF : DifferentiableAt ℝ F x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hQ : DifferentiableAt ℝ Q (F x))
    (hV : DifferentiableAt ℝ V (F x)) (hW : DifferentiableAt ℝ W x)
    (hsymm : IsSymmSndFDerivAt ℝ F x)
    (hrel : (fun y => V (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (W y))) :
    lieBilinearEval (fun y => bilinearPullback (Q (F y)) (fderiv ℝ F y)) W x a b =
      lieBilinearEval Q V (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) := by
  have hxrel := hrel.eq_of_nhds
  have ha := vector_relation_derivative F V W x a hF hJ hV hW hrel
  have hb := vector_relation_derivative F V W x b hF hJ hV hW hrel
  unfold lieBilinearEval
  rw [fderiv_bilinear_pullback_eval F Q x a b (W x) hF hJ hQ,
    fderiv_bilinear_eval Q (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) (V (F x)) hQ]
  rw [hxrel, ha, hb, hsymm a (W x), hsymm b (W x)]
  simp only [bilinearPullback_apply, map_add, ContinuousLinearMap.add_apply]
  ring

/-- C2 coordinate changes supply the symmetric second derivative automatically. -/
theorem lieBilinearEval_pullback_of_contDiff
    (F V W : FourSpace → FourSpace) (Q : FourSpace → Bilinear4)
    (x a b : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hQ : DifferentiableAt ℝ Q (F x))
    (hV : DifferentiableAt ℝ V (F x)) (hW : DifferentiableAt ℝ W x)
    (hrel : (fun y => V (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (W y))) :
    lieBilinearEval (fun y => bilinearPullback (Q (F y)) (fderiv ℝ F y)) W x a b =
      lieBilinearEval Q V (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) := by
  exact lieBilinearEval_pullback F V W Q x a b
    (hF.differentiableAt (by norm_num))
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    hQ hV hW (hF.isSymmSndFDerivAt (by norm_num)) hrel


end K24.Global.K24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem matrixToBilinear_sum (A : Mat4) :
    matrixToBilinear A = ∑ i, ∑ j, A i j • (coordProj i).smulRight (coordProj j) := by
  ext v w
  simp [matrixToBilinear, mul_assoc, mul_comm, mul_left_comm]

theorem matrixToBilinear_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    DifferentiableAt ℝ (fun y => matrixToBilinear (A y)) x := by
  simp_rw [matrixToBilinear_sum]
  exact DifferentiableAt.fun_sum (𝕜 := ℝ) (E := FourSpace) (F := Bilinear4)
    (fun i _ => DifferentiableAt.fun_sum (𝕜 := ℝ) (E := FourSpace) (F := Bilinear4)
      (fun j _ => (hA i j).smul_const ((coordProj i).smulRight (coordProj j))))

theorem fderiv_vector_coefficient (V : FourSpace → FourSpace) (x v : FourSpace)
    (hV : DifferentiableAt ℝ V x) (p : Fin 4) :
    fderiv ℝ (fun y => V y p) x v = fderiv ℝ V x v p := by
  have h := (hasFDerivAt_const (coordProj p) x).clm_apply hV.hasFDerivAt
  change fderiv ℝ (fun y => (coordProj p) (V y)) x v = _
  rw [h.fderiv]
  simp [coordProj]

/-- A bilinear form representing the same actual differential expression. -/
def lieBilinear (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x : FourSpace) : Bilinear4 :=
  fderiv ℝ Q x (V x) + (Q x).comp (fderiv ℝ V x) +
    (ContinuousLinearMap.precomp ℝ (fderiv ℝ V x)).comp (Q x)

theorem lieBilinear_apply (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) (hQ : DifferentiableAt ℝ Q x) :
    lieBilinear Q V x a b = lieBilinearEval Q V x a b := by
  rw [lieBilinearEval, fderiv_bilinear_eval Q x a b (V x) hQ]
  rfl

/-- The finite native formula is exactly evaluation of the genuine bilinear Lie expression. -/
theorem lieTensorInChart_eq_bilinear (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x)
    (hY : DifferentiableAt ℝ (vectorInChart Y c) x) :
    matrixToBilinear (lieTensorInChart Y g c x) =
      lieBilinear (fun y => matrixToBilinear (cov2InChart g c y)) (vectorInChart Y c) x := by
  have hQ := matrixToBilinear_differentiableAt _ x hg
  rw [← matrixToBilinear_recover (lieBilinear
    (fun y => matrixToBilinear (cov2InChart g c y)) (vectorInChart Y c) x)]
  apply congrArg matrixToBilinear
  ext i j
  rw [lieBilinear_apply _ _ x _ _ hQ]
  unfold lieBilinearEval
  simp only [matrixToBilinear_basis]
  have hfirst : fderiv ℝ (fun y => cov2InChart g c y i j) x (vectorInChart Y c x) =
      ∑ p, vectorInChart Y c x p * coordDeriv (fun y => cov2InChart g c y i j) p x := by
    conv_lhs => rw [← sum_basisVector (vectorInChart Y c x)]
    simp [coordDeriv, map_sum]
  rw [hfirst]
  have hsecond : matrixToBilinear (cov2InChart g c x)
      (fderiv ℝ (vectorInChart Y c) x (basisVector i)) (basisVector j) =
      ∑ p, coordDeriv (fun y => vectorInChart Y c y p) i x * cov2InChart g c x p j := by
    conv_lhs => rw [← sum_basisVector (fderiv ℝ (vectorInChart Y c) x (basisVector i))]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, matrixToBilinear_basis]
    apply Finset.sum_congr rfl
    intro p _
    rw [coordDeriv, fderiv_vector_coefficient _ x _ hY p]
  have hthird : matrixToBilinear (cov2InChart g c x) (basisVector i)
      (fderiv ℝ (vectorInChart Y c) x (basisVector j)) =
      ∑ p, coordDeriv (fun y => vectorInChart Y c y p) j x * cov2InChart g c x i p := by
    conv_lhs => rw [← sum_basisVector (fderiv ℝ (vectorInChart Y c) x (basisVector j))]
    simp only [map_sum, map_smul, smul_eq_mul, matrixToBilinear_basis]
    apply Finset.sum_congr rfl
    intro p _
    rw [coordDeriv, fderiv_vector_coefficient _ x _ hY p]
  rw [hsecond, hthird]
  simp [lieTensorInChart, Finset.sum_add_distrib]

/-- Equality near a point suffices for equality of the genuine Lie expression there. -/
theorem lieBilinearEval_congr (Q R : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) (hQR : Q =ᶠ[𝓝 x] R) :
    lieBilinearEval Q V x a b = lieBilinearEval R V x a b := by
  unfold lieBilinearEval
  have hscalar : (fun y => Q y a b) =ᶠ[𝓝 x] (fun y => R y a b) :=
    hQR.mono fun y hy => congrArg (fun B => B a b) hy
  rw [hscalar.fderiv_eq, hQR.eq_of_nhds]


end K24.Global.K24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

theorem chartTransitionDerivative_eq_fderiv (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    chartTransitionDerivative c d x =
      fderiv ℝ (fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)) x := by
  have h := mfderiv_comp x
    ((mdifferentiable_chart (I := I4) d).mdifferentiableAt hd)
    ((mdifferentiable_chart (I := I4) c).mdifferentiableAt_symm hx)
  simpa only [mfderiv_eq_fderiv, Function.comp_def, chartTransitionDerivative] using h.symm

theorem chartTransition_contDiffAt (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 2 (fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)) x := by
  have hc : ContMDiffAt I4 I4 2 (chartAt FourSpace c).symm x :=
    (contMDiffOn_chart_symm (I := I4) (n := 2) (x := c)).contMDiffAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hd' : ContMDiffAt I4 I4 2 (chartAt FourSpace d) ((chartAt FourSpace c).symm x) :=
    (contMDiffOn_chart (I := I4) (n := 2) (x := d)).contMDiffAt
      ((chartAt FourSpace d).open_source.mem_nhds hd)
  simpa only [Function.comp_def] using (hd'.comp x hc).contDiffAt

/-- Actual vector coefficients satisfy the genuine Jacobian transition relation. -/
theorem vectorInChart_transition (Y : RawVector M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    vectorInChart Y d (chartAt FourSpace d ((chartAt FourSpace c).symm x)) =
      chartTransitionDerivative c d x (vectorInChart Y c x) := by
  let p := (chartAt FourSpace c).symm x
  have hdi : ∀ v : TangentSpace I4 p,
      mfderiv I4 I4 (chartAt FourSpace c).symm x
        (mfderiv I4 I4 (chartAt FourSpace c) p v) = v := by
    intro v
    have h := congrArg (fun D => D v)
      ((mdifferentiable_chart (I := I4) c).symm_comp_deriv
        ((chartAt FourSpace c).map_target hx))
    change mfderiv I4 I4 (chartAt FourSpace c).symm
      (chartAt FourSpace c ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (chartAt FourSpace c) p v) = v at h
    rw [(chartAt FourSpace c).right_inv hx] at h
    exact h
  change mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace d).symm (chartAt FourSpace d p))
    (Y ((chartAt FourSpace d).symm (chartAt FourSpace d p))) =
    mfderiv I4 I4 (chartAt FourSpace d) p
      (mfderiv I4 I4 (chartAt FourSpace c).symm x
        (mfderiv I4 I4 (chartAt FourSpace c) p (Y p)))
  rw [(chartAt FourSpace d).left_inv hd, hdi]

/-- The genuine Lie coefficient formula transforms as a covariant tensor. -/
theorem lieTensorInChart_transition (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y)
    (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    matrixToBilinear (lieTensorInChart Y g c x) =
      bilinearPullback (matrixToBilinear (lieTensorInChart Y g d
        (chartAt FourSpace d ((chartAt FourSpace c).symm x))))
        (chartTransitionDerivative c d x) := by
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
  let Qc : FourSpace → Bilinear4 := fun y => matrixToBilinear (cov2InChart g c y)
  let Qd : FourSpace → Bilinear4 := fun y => matrixToBilinear (cov2InChart g d y)
  let Vc := vectorInChart Y c
  let Vd := vectorInChart Y d
  have hdx : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hgc : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x := by
    intro i j
    exact ((cov2_coefficient_contDiffOn g hg c i j).differentiableOn (by norm_num) x hx).differentiableAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hgd : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g d y i j) (F x) := by
    intro i j
    exact ((cov2_coefficient_contDiffOn g hg d i j).differentiableOn (by norm_num) (F x) hdx).differentiableAt ((chartAt FourSpace d).open_target.mem_nhds hdx)
  have hVc : DifferentiableAt ℝ Vc x :=
    ((hY c).differentiableOn (by norm_num) x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hVd : DifferentiableAt ℝ Vd (F x) :=
    ((hY d).differentiableOn (by norm_num) (F x) hdx).differentiableAt
      ((chartAt FourSpace d).open_target.mem_nhds hdx)
  have hQc : DifferentiableAt ℝ Qc x := matrixToBilinear_differentiableAt _ x hgc
  have hQd : DifferentiableAt ℝ Qd (F x) := matrixToBilinear_differentiableAt _ (F x) hgd
  have hnear : ∀ᶠ y in 𝓝 x,
      y ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source :=
    ((chartAt FourSpace c).symm.trans (chartAt FourSpace d)).open_source.mem_nhds ⟨hx, hd⟩
  have hQrel : Qc =ᶠ[𝓝 x] (fun y => bilinearPullback (Qd (F y)) (fderiv ℝ F y)) := by
    filter_upwards [hnear] with y hy
    exact (cov2InChart_transition g c d y hy.2).trans
      (congrArg (bilinearPullback (Qd (F y)))
        (chartTransitionDerivative_eq_fderiv c d y hy.1 hy.2))
  have hVrel : (fun y => Vd (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (Vc y)) := by
    filter_upwards [hnear] with y hy
    exact (vectorInChart_transition Y c d y hy.1 hy.2).trans
      (congrArg (fun D => D (Vc y))
        (chartTransitionDerivative_eq_fderiv c d y hy.1 hy.2))
  rw [lieTensorInChart_eq_bilinear g Y c x hgc hVc,
    lieTensorInChart_eq_bilinear g Y d (F x) hgd hVd,
    chartTransitionDerivative_eq_fderiv c d x hx hd]
  ext a b
  change lieBilinear Qc Vc x a b =
    lieBilinear Qd Vd (F x) (fderiv ℝ F x a) (fderiv ℝ F x b)
  rw [lieBilinear_apply _ _ x a b hQc,
    lieBilinear_apply _ _ (F x) _ _ hQd,
    lieBilinearEval_congr Qc _ Vc x a b hQrel]
  exact lieBilinearEval_pullback_of_contDiff F Vd Vc Qd x a b
    (chartTransition_contDiffAt c d x hx hd) hQd hVd hVc hVrel

/-- Actual C2 fields give a C1 native Lie tensor on the smooth manifold. -/
theorem lieTensor_contDiff (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) :
    Cov2ContDiff 1 (lieTensor Y g) := by
  apply lieTensor_contDiff_of_compatible g Y hg hY
  intro c d p hc hd
  have h := lieTensorInChart_transition g Y hg hY c d (chartAt FourSpace c p)
    ((chartAt FourSpace c).map_source hc) (by simpa only [(chartAt FourSpace c).left_inv hc] using hd)
  simpa only [(chartAt FourSpace c).left_inv hc] using h


end K24.Global.K24REG


namespace K24.Global.K24REG
universe u

/-- The native global Lie tensor loses exactly one derivative at this regularity. -/
theorem native_lie_regularity :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (g : RawCov2 M) (Y : RawVector M),
      Cov2ContDiff 2 g → VectorContDiff 2 Y → Cov2ContDiff 1 (lieTensor Y g) := by
  intro M _ _ _ g Y hg hY
  exact lieTensor_contDiff g Y hg hY

/-- Exact expanded canonical-only target check. -/
theorem exact_type_wrapper :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (g : RawCov2 M) (Y : RawVector M),
      Cov2ContDiff 2 g → VectorContDiff 2 Y → Cov2ContDiff 1 (lieTensor Y g) := native_lie_regularity

#print native_lie_regularity
#print axioms native_lie_regularity
#print axioms exact_type_wrapper

end K24.Global.K24REG

open K24.Global
open scoped Manifold ContDiff
universe u

/-- Global exact declaration for publication of the native Lie regularity theorem. -/
theorem solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (g : RawCov2 M) (Y : RawVector M),
      Cov2ContDiff 2 g → VectorContDiff 2 Y → Cov2ContDiff 1 (lieTensor Y g) := K24.Global.K24REG.native_lie_regularity

#print solution
#print axioms solution
