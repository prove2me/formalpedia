-- Prove2me | solution 1 for K24.Global.nativeWeitzenbockIdentity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:21:18.551238+00:00
-- url     : https://prove2.me/submissions/5230e9a1-f1bd-4acd-aca8-d43345e9bc63

import Definitions.Def_K24GlobalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24OPConnection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

lemma symmetric_inverse_contract (G : Mat4)
    (hs : ∀ i j, G i j = G j i) (hd : G.det ≠ 0) (q l : Fin 4) :
    (∑ p, G⁻¹ p q * G p l) = if l = q then 1 else 0 := by
  calc
    (∑ p, G⁻¹ p q * G p l) = (G * G⁻¹) l q := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro p _
      rw [hs p l, mul_comm]
    _ = if l = q then 1 else 0 := by
      rw [Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hd)]
      rfl

lemma lower_inverse_sum (G : Mat4)
    (hs : ∀ i j, G i j = G j i) (hd : G.det ≠ 0)
    (D : Fin 4 → ℝ) (l : Fin 4) :
    (∑ p, ((1 / 2 : ℝ) * ∑ q, G⁻¹ p q * D q) * G p l) =
      (1 / 2 : ℝ) * D l := by
  calc
    _ = (1 / 2 : ℝ) * ∑ q, (∑ p, G⁻¹ p q * G p l) * D q := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by simp [symmetric_inverse_contract G hs hd]

lemma cov2InChart_symm (g : RawCov2 M) (hs : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (i j : Fin 4) :
    cov2InChart g c x i j = cov2InChart g c x j i := by
  exact hs _ _ _

lemma christoffel_symm (g : RawCov2 M) (hs : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (p i j : Fin 4) :
    christoffelInChart g c x p i j = christoffelInChart g c x p j i := by
  have hfun : (fun y => cov2InChart g c y i j) =
      (fun y => cov2InChart g c y j i) := by
    funext y
    exact cov2InChart_symm g hs c y i j
  unfold christoffelInChart
  rw [hfun]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma christoffel_lower (g : RawCov2 M) (hs : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (hd : (cov2InChart g c x).det ≠ 0)
    (i j l : Fin 4) :
    (∑ p, christoffelInChart g c x p i j * cov2InChart g c x p l) =
    (1 / 2 : ℝ) *
      (coordDeriv (fun y => cov2InChart g c y j l) i x +
       coordDeriv (fun y => cov2InChart g c y i l) j x -
       coordDeriv (fun y => cov2InChart g c y i j) l x) := by
  unfold christoffelInChart inverseMetricInChart
  exact lower_inverse_sum _ (cov2InChart_symm g hs c x) hd _ l

variable [IsManifold I4 ∞ M]

theorem metric_chart_det_ne_zero (g : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    (cov2InChart g c x).det ≠ 0 := by
  have hpos : (cov2InChart g c x).PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · ext i j
      change cov2InChart g c x j i = cov2InChart g c x i j
      exact cov2InChart_symm g hg.1 c x j i
    · intro v hv
      let V : FourSpace := ∑ i : Fin 4, v i • basisVector i
      let di := mfderiv I4 I4 (chartAt FourSpace c).symm x
      have hV : V ≠ 0 := by
        intro h
        apply hv
        funext j
        have hj := congrArg (fun w : FourSpace => w j) h
        simpa [V, basisVector, Pi.single_apply] using hj
      have hleft : Function.LeftInverse
          (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)) di := by
        intro w
        have h := (mdifferentiable_chart (I := I4) c).comp_symm_deriv hx
        exact congrArg (fun A => A w) h
      have hdi : di V ≠ 0 := by
        simpa only [map_zero] using hleft.injective.ne hV
      have hp := hg.2 ((chartAt FourSpace c).symm x) (di V) hdi
      convert hp using 1 <;> try rfl
      simp [dotProduct, Matrix.mulVec, cov2InChart, V, di, map_sum, Finset.mul_sum,
        mul_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact congrArg (fun t : ℝ => v a * (v b * t)) (hg.1 _ _ _)
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hpos.isUnit).ne_zero

end K24.Global.K24OPConnection

namespace K24.Global.K24OP

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem coordDeriv_sub (f g : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    coordDeriv (fun y => f y - g y) i x = coordDeriv f i x - coordDeriv g i x := by
  simp [coordDeriv, fderiv_fun_sub hf hg]

theorem coordDeriv_mul (f g : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    coordDeriv (fun y => f y * g y) i x =
      coordDeriv f i x * g x + f x * coordDeriv g i x := by
  simp [coordDeriv, fderiv_fun_mul hf hg, mul_comm, add_comm]

theorem coordDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → FourSpace → ℝ)
    (x : FourSpace) (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) x) (i : Fin 4) :
    coordDeriv (fun y => ∑ a ∈ s, f a y) i x =
      ∑ a ∈ s, coordDeriv (f a) i x := by
  simp only [coordDeriv, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]

end K24.Global.K24OP

namespace K24.Global.K24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem cov2_coefficient_contDiffOn (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (c : M) (i j : Fin 4) :
    ContDiffOn ℝ 2 (fun x => cov2InChart g c x i j) (chartAt FourSpace c).target := by
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) i) j

theorem vector_coefficient_contDiffOn (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (p : Fin 4) :
    ContDiffOn ℝ 2 (fun x => vectorInChart Y c x p) (chartAt FourSpace c).target := by
  exact (coordProj p).contDiff.comp_contDiffOn (hY c)

end K24.Global.K24REG

namespace K24.Global.K24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

variable [IsManifold I4 ∞ M]

def chartTransitionDerivative (c d : M) (x : FourSpace) : FourSpace →L[ℝ] FourSpace :=
  (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm x)).comp
    (mfderiv I4 I4 (chartAt FourSpace c).symm x)

@[simp] theorem matrixToBilinear_basis (A : Mat4) (i j : Fin 4) :
    matrixToBilinear A (basisVector i) (basisVector j) = A i j := by
  simp [matrixToBilinear, basisVector, coordProj, Pi.single_apply]

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

def Cov2CoordinateCompatible (A : M → FourSpace → Mat4) : Prop :=
  ∀ (c d p : M), p ∈ (chartAt FourSpace c).source →
    p ∈ (chartAt FourSpace d).source →
    matrixToBilinear (A c (chartAt FourSpace c p)) =
      bilinearPullback (matrixToBilinear (A d (chartAt FourSpace d p)))
        (chartTransitionDerivative c d (chartAt FourSpace c p))

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

abbrev Bilinear4 := FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)

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

def lieBilinear (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x : FourSpace) : Bilinear4 :=
  fderiv ℝ Q x (V x) + (Q x).comp (fderiv ℝ V x) +
    (ContinuousLinearMap.precomp ℝ (fderiv ℝ V x)).comp (Q x)

theorem lieBilinear_apply (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) (hQ : DifferentiableAt ℝ Q x) :
    lieBilinear Q V x a b = lieBilinearEval Q V x a b := by
  rw [lieBilinearEval, fderiv_bilinear_eval Q x a b (V x) hQ]
  rfl

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

theorem lieBilinearEval_congr (Q R : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) (hQR : Q =ᶠ[𝓝 x] R) :
    lieBilinearEval Q V x a b = lieBilinearEval R V x a b := by
  unfold lieBilinearEval
  have hscalar : (fun y => Q y a b) =ᶠ[𝓝 x] (fun y => R y a b) :=
    hQR.mono fun y hy => congrArg (fun B => B a b) hy
  rw [hscalar.fderiv_eq, hQR.eq_of_nhds]

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

end K24.Global.K24REG

namespace K24.Global.K24SYM

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

variable [IsManifold I4 ∞ M]

theorem matrix_det_contDiffAt (A : FourSpace → Mat4) (x : FourSpace) (k : ℕ∞ω)
    (hA : ∀ a b, ContDiffAt ℝ k (fun y => A y a b) x) :
    ContDiffAt ℝ k (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  exact contDiffAt_prod fun i _ => hA (σ i) i

theorem matrix_inv_coefficient_contDiffAt (A : FourSpace → Mat4) (x : FourSpace) (k : ℕ∞ω)
    (hA : ∀ a b, ContDiffAt ℝ k (fun y => A y a b) x)
    (hdet : (A x).det ≠ 0) (a b : Fin 4) :
    ContDiffAt ℝ k (fun y => (A y)⁻¹ a b) x := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_apply]
  apply ContDiffAt.mul
  · exact (matrix_det_contDiffAt A x k hA).inv hdet
  · apply matrix_det_contDiffAt
    intro i j
    by_cases hi : i = b
    · subst i
      simp only [Matrix.updateRow_self]
      exact contDiffAt_const
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j

theorem metric_inverse_coefficient_C2 (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun y => inverseMetricInChart g c y a b) x := by
  apply matrix_inv_coefficient_contDiffAt
  · intro i j
    exact (K24REG.cov2_coefficient_contDiffOn g hg c i j).contDiffAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  · exact K24OPConnection.metric_chart_det_ne_zero g hm c x hx

theorem coordDeriv_contDiffAt {f : FourSpace → ℝ} {x : FourSpace}
    (hf : ContDiffAt ℝ 2 f x) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun y => coordDeriv f i y) x := by
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem christoffel_contDiffAt (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (k i j : Fin 4) :
    ContDiffAt ℝ 1 (fun y => christoffelInChart g c y k i j) x := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul
  · exact (metric_inverse_coefficient_C2 g hm hg c x hx k l).of_le (by norm_num)
  · apply ContDiffAt.sub
    · apply ContDiffAt.add
      · exact coordDeriv_contDiffAt
          ((K24REG.cov2_coefficient_contDiffOn g hg c j l).contDiffAt
            ((chartAt FourSpace c).open_target.mem_nhds hx)) i
      · exact coordDeriv_contDiffAt
          ((K24REG.cov2_coefficient_contDiffOn g hg c i l).contDiffAt
            ((chartAt FourSpace c).open_target.mem_nhds hx)) j
    · exact coordDeriv_contDiffAt
        ((K24REG.cov2_coefficient_contDiffOn g hg c i j).contDiffAt
          ((chartAt FourSpace c).open_target.mem_nhds hx)) l

end K24.Global.K24SYM


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.K24WEITZ
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

lemma inverseMetric_symm (g : RawCov2 M) (hs : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (a b : Fin 4) :
    inverseMetricInChart g c x a b = inverseMetricInChart g c x b a := by
  have h : (cov2InChart g c x).IsSymm := by
    ext i j
    exact K24OPConnection.cov2InChart_symm g hs c x j i
  exact congrArg (fun A : Mat4 => A b a) h.inv

lemma metric_compatibility (g : RawCov2 M) (hm : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (a i j : Fin 4) :
    coordDeriv (fun y => cov2InChart g c y i j) a x =
      (∑ p, christoffelInChart g c x p a i * cov2InChart g c x p j) +
      (∑ p, christoffelInChart g c x p a j * cov2InChart g c x i p) := by
  have hdet := K24OPConnection.metric_chart_det_ne_zero g hm c x hx
  simp_rw [K24OPConnection.cov2InChart_symm g hm.1 c x i]
  rw [K24OPConnection.christoffel_lower g hm.1 c x hdet a i j,
    K24OPConnection.christoffel_lower g hm.1 c x hdet a j i]
  have hij : (fun y => cov2InChart g c y j i) = (fun y => cov2InChart g c y i j) := by
    funext y
    exact K24OPConnection.cov2InChart_symm g hm.1 c y j i
  rw [hij]
  ring

lemma metric_coefficient_C2 (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun y => cov2InChart g c y i j) x :=
  (K24REG.cov2_coefficient_contDiffOn g hg c i j).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hx)

lemma vector_coefficient_C2 (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    ContDiffAt ℝ 2 (fun y => vectorInChart Y c y i) x :=
  (K24REG.vector_coefficient_contDiffOn Y hY c i).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hx)

lemma inverseMetric_coordDeriv (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i a b : Fin 4) :
    coordDeriv (fun y => inverseMetricInChart g c y a b) i x =
      -(∑ p, ∑ q, inverseMetricInChart g c x a p *
        coordDeriv (fun y => cov2InChart g c y p q) i x * inverseMetricInChart g c x q b) := by
  let G := cov2InChart g c x
  let P := inverseMetricInChart g c x
  let D : Mat4 := fun r s => coordDeriv (fun y => cov2InChart g c y r s) i x
  let S : Mat4 := fun r s => coordDeriv (fun y => inverseMetricInChart g c y r s) i x
  have hG (r s : Fin 4) := (metric_coefficient_C2 g hg c x hx r s).differentiableAt (by norm_num)
  have hP (r s : Fin 4) := (K24SYM.metric_inverse_coefficient_C2 g hm hg c x hx r s).differentiableAt (by norm_num)
  have hdiff : S * G + P * D = 0 := by
    ext r s
    have heq : (fun y => ∑ q, inverseMetricInChart g c y r q * cov2InChart g c y q s) =ᶠ[𝓝 x]
        (fun _ => (1 : Mat4) r s) := by
      filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
      exact congrArg (fun A : Mat4 => A r s)
        (Matrix.nonsing_inv_mul (cov2InChart g c y)
          (isUnit_iff_ne_zero.mpr (K24OPConnection.metric_chart_det_ne_zero g hm c y hy)))
    have he : coordDeriv (fun y => ∑ q, inverseMetricInChart g c y r q * cov2InChart g c y q s) i x = 0 := by
      unfold coordDeriv
      rw [heq.fderiv_eq]
      simp
    have hsum := K24OP.coordDeriv_sum Finset.univ
      (fun q y => inverseMetricInChart g c y r q * cov2InChart g c y q s) x
      (fun q _ => (hP r q).mul (hG q s)) i
    rw [hsum] at he
    simp_rw [K24OP.coordDeriv_mul _ _ x (hP r _) (hG _ s) i] at he
    simpa only [Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      G, P, D, S] using he
  have hGP : G * P = 1 := Matrix.mul_nonsing_inv G
    (isUnit_iff_ne_zero.mpr (K24OPConnection.metric_chart_det_ne_zero g hm c x hx))
  have hS : S = -(P * D * P) := by
    have he := congrArg (fun A : Mat4 => A * P) hdiff
    rw [add_mul, mul_assoc S G P, hGP, mul_one, zero_mul] at he
    exact eq_neg_of_add_eq_zero_left he
  have he := congrArg (fun A : Mat4 => A a b) hS
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul] at he
  rw [Finset.sum_comm] at he
  simpa only [S, P, D] using he

end K24.Global.K24WEITZ


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24WEITZCommutator

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

theorem coordDeriv_add (f h : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) (i : Fin 4) :
    coordDeriv (fun y => f y + h y) i x = coordDeriv f i x + coordDeriv h i x := by
  simp [coordDeriv, fderiv_fun_add hf hh]

/-- Coordinate second partials commute by the genuine C2 Schwarz theorem. -/
theorem coordDeriv_commute {f : FourSpace → ℝ} {x : FourSpace}
    (hf : ContDiffAt ℝ 2 f x) (a b : Fin 4) :
    coordDeriv (fun y => coordDeriv f b y) a x =
      coordDeriv (fun y => coordDeriv f a y) b x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold coordDeriv
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using (hf.isSymmSndFDerivAt (by norm_num)).eq (basisVector a) (basisVector b)

omit [IsManifold I4 ∞ M] in
theorem vector_coefficient_contDiffAt (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (p : Fin 4) :
    ContDiffAt ℝ 2 (fun y => vectorInChart Y c y p) x :=
  (K24REG.vector_coefficient_contDiffOn Y hY c p).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hx)

/-- A first covariant vector derivative has C1 coefficients in the chart interior. -/
theorem nablaVector_contDiffAt (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (a b : Fin 4) :
    ContDiffAt ℝ 1 (fun y => nablaVectorInChart g Y c y a b) x := by
  apply ContDiffAt.add
  · exact K24SYM.coordDeriv_contDiffAt (vector_coefficient_contDiffAt Y hY c x hx b) a
  · apply ContDiffAt.sum
    intro p _
    exact (K24SYM.christoffel_contDiffAt g hm hg c x hx b a p).mul
      ((vector_coefficient_contDiffAt Y hY c x hx p).of_le (by norm_num))

/-- The product rule applied to the actual coordinate covariant derivative. -/
theorem coordDeriv_nablaVector (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (a b d : Fin 4) :
    coordDeriv (fun y => nablaVectorInChart g Y c y b d) a x =
      coordDeriv (fun y => coordDeriv (fun z => vectorInChart Y c z d) b y) a x +
        ∑ p, (coordDeriv (fun y => christoffelInChart g c y d b p) a x *
          vectorInChart Y c x p + christoffelInChart g c x d b p *
            coordDeriv (fun y => vectorInChart Y c y p) a x) := by
  have hv : ∀ p, DifferentiableAt ℝ (fun y => vectorInChart Y c y p) x :=
    fun p => (vector_coefficient_contDiffAt Y hY c x hx p).differentiableAt (by norm_num)
  have hG : ∀ p, DifferentiableAt ℝ (fun y => christoffelInChart g c y d b p) x :=
    fun p => (K24SYM.christoffel_contDiffAt g hm hg c x hx d b p).differentiableAt (by norm_num)
  unfold nablaVectorInChart
  rw [coordDeriv_add]
  · congr 1
    rw [K24OP.coordDeriv_sum]
    · apply Finset.sum_congr rfl
      intro p _
      exact K24OP.coordDeriv_mul _ _ x (hG p) (hv p) a
    · intro p _
      exact (hG p).mul (hv p)
  · exact (K24SYM.coordDeriv_contDiffAt
      (vector_coefficient_contDiffAt Y hY c x hx d) b).differentiableAt (by norm_num)
  · exact DifferentiableAt.fun_sum fun p _ => (hG p).mul (hv p)

/-- The commutator of the genuine second covariant derivatives is curvature. -/
theorem secondNabla_commutator (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (a b d : Fin 4) :
    secondNablaVectorInChart g Y c x a b d - secondNablaVectorInChart g Y c x b a d =
      ∑ p, curvatureInChart g c x d a b p * vectorInChart Y c x p := by
  have hba : ∀ p, christoffelInChart g c x p b a = christoffelInChart g c x p a b :=
    fun p => K24OPConnection.christoffel_symm g hm.1 c x p b a
  simp only [secondNablaVectorInChart]
  rw [coordDeriv_nablaVector g hm hg Y hY c x hx a b d,
    coordDeriv_nablaVector g hm hg Y hY c x hx b a d,
    coordDeriv_commute (vector_coefficient_contDiffAt Y hY c x hx d) a b]
  simp_rw [hba]
  simp only [nablaVectorInChart, curvatureInChart, mul_add, sub_mul,
    add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  have hs1 :
      (∑ p, ∑ q, christoffelInChart g c x d a p *
        (christoffelInChart g c x p b q * vectorInChart Y c x q)) =
      ∑ p, ∑ q, christoffelInChart g c x d a q *
        (christoffelInChart g c x q b p * vectorInChart Y c x p) := Finset.sum_comm
  have hs2 :
      (∑ p, ∑ q, christoffelInChart g c x d b p *
        (christoffelInChart g c x p a q * vectorInChart Y c x q)) =
      ∑ p, ∑ q, christoffelInChart g c x d b q *
        (christoffelInChart g c x q a p * vectorInChart Y c x p) := Finset.sum_comm
  rw [hs1, hs2]
  ring

/-- Tracing the mixed tensor derivative cancels the two connection corrections. -/
theorem coordDeriv_nablaVector_trace (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    coordDeriv (fun y => ∑ a, nablaVectorInChart g Y c y a a) j x =
      ∑ a, secondNablaVectorInChart g Y c x j a a := by
  rw [K24OP.coordDeriv_sum]
  · simp only [secondNablaVectorInChart, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hc : (∑ a, ∑ p, christoffelInChart g c x a j p * nablaVectorInChart g Y c x a p) =
        ∑ a, ∑ p, christoffelInChart g c x p j a * nablaVectorInChart g Y c x p a :=
      Finset.sum_comm
    rw [hc]
    ring
  · intro a _
    exact (nablaVector_contDiffAt g hm hg Y hY c x hx a a).differentiableAt (by norm_num)


end K24.Global.K24WEITZCommutator


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.K24WEITZ
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

lemma lieTensor_eq_symm_nabla (g : RawCov2 M) (hm : IsMetric g)
    (Y : RawVector M) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    lieTensorInChart Y g c x i j =
      (∑ d, cov2InChart g c x j d * nablaVectorInChart g Y c x i d) +
      (∑ d, cov2InChart g c x i d * nablaVectorInChart g Y c x j d) := by
  have h1 : (∑ p, vectorInChart Y c x p *
      (∑ d, christoffelInChart g c x d p i * cov2InChart g c x d j)) =
      ∑ d, cov2InChart g c x j d *
        (∑ p, christoffelInChart g c x d i p * vectorInChart Y c x p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro p _
    rw [K24OPConnection.christoffel_symm g hm.1 c x d p i,
      K24OPConnection.cov2InChart_symm g hm.1 c x d j]
    ring
  have h2 : (∑ p, vectorInChart Y c x p *
      (∑ d, christoffelInChart g c x d p j * cov2InChart g c x i d)) =
      ∑ d, cov2InChart g c x i d *
        (∑ p, christoffelInChart g c x d j p * vectorInChart Y c x p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro p _
    rw [K24OPConnection.christoffel_symm g hm.1 c x d p j]
    ring
  unfold lieTensorInChart nablaVectorInChart
  simp_rw [metric_compatibility g hm c x hx]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h1, h2]
  have h3 : (∑ p, coordDeriv (fun y => vectorInChart Y c y p) i x * cov2InChart g c x p j) =
      ∑ p, cov2InChart g c x j p * coordDeriv (fun y => vectorInChart Y c y p) i x := by
    apply Finset.sum_congr rfl
    intro p _
    rw [K24OPConnection.cov2InChart_symm g hm.1 c x p j, mul_comm]
  rw [h3]
  simp_rw [mul_comm (coordDeriv (fun y => vectorInChart Y c y _) j x)]
  ring

lemma contract_lowered_nabla (G P N : Mat4) (hPG : P * G = 1) :
    (∑ a, ∑ b, P a b * ∑ d, G b d * N a d) = ∑ a, N a a := by
  calc
    _ = ∑ a, ∑ d, (P * G) a d * N a d := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by simp [hPG, Matrix.one_apply]

lemma lieTensor_trace (g : RawCov2 M) (hm : IsMetric g)
    (Y : RawVector M) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    (∑ a, ∑ b, inverseMetricInChart g c x a b * lieTensorInChart Y g c x a b) =
      2 * ∑ a, nablaVectorInChart g Y c x a a := by
  simp_rw [lieTensor_eq_symm_nabla g hm Y c x hx]
  simp only [mul_add, Finset.sum_add_distrib]
  have hPG : inverseMetricInChart g c x * cov2InChart g c x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (K24OPConnection.metric_chart_det_ne_zero g hm c x hx))
  rw [contract_lowered_nabla _ _ _ hPG]
  have he : (∑ a, ∑ b, inverseMetricInChart g c x a b *
      ∑ d, cov2InChart g c x a d * nablaVectorInChart g Y c x b d) =
      ∑ a, nablaVectorInChart g Y c x a a := by
    rw [Finset.sum_comm]
    simp_rw [inverseMetric_symm g hm.1 c x]
    exact contract_lowered_nabla _ _ _ hPG
  rw [he]
  ring

end K24.Global.K24WEITZ


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.K24WEITZ
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

def loweredNabla (g : RawCov2 M) (Y : RawVector M) (c : M) (x : FourSpace) (i j : Fin 4) : ℝ :=
  ∑ d, cov2InChart g c x j d * nablaVectorInChart g Y c x i d

lemma loweredNabla_differentiableAt (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => loweredNabla g Y c y i j) x := by
  apply DifferentiableAt.fun_sum
  intro d _
  exact ((metric_coefficient_C2 g hg c x hx j d).differentiableAt (by norm_num)).mul
    ((K24WEITZCommutator.nablaVector_contDiffAt g hm hg Y hY c x hx i d).differentiableAt (by norm_num))

lemma loweredNabla_coordDeriv (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b j : Fin 4) :
    coordDeriv (fun y => loweredNabla g Y c y b j) a x =
      (∑ d, cov2InChart g c x j d * secondNablaVectorInChart g Y c x a b d) +
      (∑ p, christoffelInChart g c x p a b * loweredNabla g Y c x p j) +
      (∑ p, christoffelInChart g c x p a j * loweredNabla g Y c x b p) := by
  have hG (r s : Fin 4) := (metric_coefficient_C2 g hg c x hx r s).differentiableAt (by norm_num)
  have hN (r s : Fin 4) :=
    (K24WEITZCommutator.nablaVector_contDiffAt g hm hg Y hY c x hx r s).differentiableAt (by norm_num)
  unfold loweredNabla
  rw [K24OP.coordDeriv_sum Finset.univ
    (fun d y => cov2InChart g c y j d * nablaVectorInChart g Y c y b d) x
    (fun d _ => (hG j d).mul (hN b d)) a]
  simp_rw [K24OP.coordDeriv_mul _ _ x (hG j _) (hN b _) a,
    metric_compatibility g hm c x hx]
  simp only [secondNablaVectorInChart, mul_add, add_mul, mul_sub, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ d, ∑ p, (christoffelInChart g c x p a j * cov2InChart g c x p d) *
      nablaVectorInChart g Y c x b d) =
      ∑ p, ∑ d, christoffelInChart g c x p a j *
        (cov2InChart g c x p d * nablaVectorInChart g Y c x b d) := by
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  have h2 : (∑ d, ∑ p, (christoffelInChart g c x p a d * cov2InChart g c x j p) *
      nablaVectorInChart g Y c x b d) =
      ∑ d, ∑ p, cov2InChart g c x j d *
        (christoffelInChart g c x d a p * nablaVectorInChart g Y c x b p) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h3 : (∑ d, ∑ p, cov2InChart g c x j d *
      (christoffelInChart g c x p a b * nablaVectorInChart g Y c x p d)) =
      ∑ p, ∑ d, christoffelInChart g c x p a b *
        (cov2InChart g c x j d * nablaVectorInChart g Y c x p d) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [h1, h2, h3]
  ring

lemma killing_coefficients (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    cov2InChart (killing g Y) c x = lieTensorInChart Y g c x := by
  refine K24REG.cov2InChart_reconstruction (lieTensorInChart Y g) ?_ c x hx
  intro c d p hc hd
  have h := K24REG.lieTensorInChart_transition g Y hg hY c d (chartAt FourSpace c p)
    ((chartAt FourSpace c).map_source hc) (by simpa only [(chartAt FourSpace c).left_inv hc] using hd)
  simpa only [(chartAt FourSpace c).left_inv hc] using h

lemma killing_nabla (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b j : Fin 4) :
    nablaTensorInChart g (killing g Y) c x a b j =
      (∑ d, cov2InChart g c x j d * secondNablaVectorInChart g Y c x a b d) +
      (∑ d, cov2InChart g c x b d * secondNablaVectorInChart g Y c x a j d) := by
  have heq : (fun y => cov2InChart (killing g Y) c y b j) =ᶠ[𝓝 x]
      (fun y => loweredNabla g Y c y b j + loweredNabla g Y c y j b) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    rw [killing_coefficients g hg Y hY c y hy]
    exact lieTensor_eq_symm_nabla g hm Y c y hy b j
  have hderiv : coordDeriv (fun y => cov2InChart (killing g Y) c y b j) a x =
      coordDeriv (fun y => loweredNabla g Y c y b j) a x +
      coordDeriv (fun y => loweredNabla g Y c y j b) a x := by
    unfold coordDeriv
    rw [heq.fderiv_eq, fderiv_fun_add
      (loweredNabla_differentiableAt g hm hg Y hY c x hx b j)
      (loweredNabla_differentiableAt g hm hg Y hY c x hx j b)]
    rfl
  unfold nablaTensorInChart
  rw [hderiv, loweredNabla_coordDeriv g hm hg Y hY c x hx a b j,
    loweredNabla_coordDeriv g hm hg Y hY c x hx a j b]
  simp_rw [killing_coefficients g hg Y hY c x hx, lieTensor_eq_symm_nabla g hm Y c x hx]
  change _ + _ - (∑ p, christoffelInChart g c x p a b *
    (loweredNabla g Y c x p j + loweredNabla g Y c x j p)) -
    (∑ p, christoffelInChart g c x p a j *
    (loweredNabla g Y c x b p + loweredNabla g Y c x p b)) = _
  simp only [mul_add, Finset.sum_add_distrib]
  ring

lemma killing_trace_coordDeriv (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    coordDeriv (metricTraceInChart g (killing g Y) c) j x =
      2 * ∑ a, secondNablaVectorInChart g Y c x j a a := by
  have heq : metricTraceInChart g (killing g Y) c =ᶠ[𝓝 x]
      (fun y => 2 * ∑ a, nablaVectorInChart g Y c y a a) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    unfold metricTraceInChart
    rw [killing_coefficients g hg Y hY c y hy]
    exact lieTensor_trace g hm Y c y hy
  have hdiff : DifferentiableAt ℝ (fun y => ∑ a, nablaVectorInChart g Y c y a a) x :=
    DifferentiableAt.fun_sum fun a _ =>
      (K24WEITZCommutator.nablaVector_contDiffAt g hm hg Y hY c x hx a a).differentiableAt (by norm_num)
  have hd : coordDeriv (metricTraceInChart g (killing g Y) c) j x =
      2 * coordDeriv (fun y => ∑ a, nablaVectorInChart g Y c y a a) j x := by
    unfold coordDeriv
    rw [heq.fderiv_eq, fderiv_const_mul hdiff]
    rfl
  rw [hd, K24WEITZCommutator.coordDeriv_nablaVector_trace g hm hg Y hY c x hx j]

end K24.Global.K24WEITZ


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24WEITZ
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
lemma curvature_antisymm (g : RawCov2 M) (c : M) (x : FourSpace) (d a b k : Fin 4) :
    curvatureInChart g c x d a b k = -curvatureInChart g c x d b a k := by
  simp only [curvatureInChart, Finset.sum_sub_distrib]
  ring

lemma secondNabla_trace_difference (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    (∑ a, secondNablaVectorInChart g Y c x j a a) -
      (∑ a, secondNablaVectorInChart g Y c x a j a) =
      -(∑ k, ricciInChart g c x j k * vectorInChart Y c x k) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [K24WEITZCommutator.secondNabla_commutator g hm hg Y hY c x hx]
  simp_rw [curvature_antisymm g c x _ j]
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [ricciInChart, Finset.sum_mul]

lemma bianchi_killing_ricci_transpose (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    bianchiInChart g (killing g Y) c x j =
      -(∑ a, ∑ b, ∑ d, inverseMetricInChart g c x a b * cov2InChart g c x j d *
        secondNablaVectorInChart g Y c x a b d) -
      (∑ k, ricciInChart g c x j k * vectorInChart Y c x k) := by
  have hPG : inverseMetricInChart g c x * cov2InChart g c x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (K24OPConnection.metric_chart_det_ne_zero g hm c x hx))
  unfold bianchiInChart
  rw [killing_trace_coordDeriv g hm hg Y hY c x hx j]
  simp_rw [killing_nabla g hm hg Y hY c x hx]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [contract_lowered_nabla _ _ (fun a d => secondNablaVectorInChart g Y c x a j d) hPG]
  have hcomm := secondNabla_trace_difference g hm hg Y hY c x hx j
  simp only [Finset.mul_sum, ← mul_assoc]
  norm_num only [show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  linarith

lemma matrixToBilinear_left (A : Mat4) (v : FourSpace) :
    matrixToBilinear A v = coefficientsToCovector (fun j => ∑ i, A i j * v i) := by
  ext w
  simp only [matrixToBilinear, coefficientsToCovector, sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, coordProj,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change v i * (A i j * w j) = A i j * v i * w j
  ring

lemma coefficientsToCovector_sub (a b : Fin 4 → ℝ) :
    coefficientsToCovector (a - b) = coefficientsToCovector a - coefficientsToCovector b := by
  simp only [coefficientsToCovector, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

end K24.Global.K24WEITZ


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24WEITZRicci

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
theorem coordDeriv_metric_symm (g : RawCov2 M) (hm : IsMetric g)
    (c : M) (x : FourSpace) (i a b : Fin 4) :
    coordDeriv (fun y => cov2InChart g c y a b) i x =
      coordDeriv (fun y => cov2InChart g c y b a) i x := by
  congr 1
  funext y
  exact K24OPConnection.cov2InChart_symm g hm.1 c y a b

/-- The trace of the actual Christoffel coefficients. -/
theorem christoffel_trace (g : RawCov2 M) (hm : IsMetric g)
    (c : M) (x : FourSpace) (j : Fin 4) :
    (∑ k, christoffelInChart g c x k k j) =
      (1 / 2 : ℝ) * ∑ a, ∑ b, inverseMetricInChart g c x a b *
        coordDeriv (fun y => cov2InChart g c y a b) j x := by
  have hc :
      (∑ a, ∑ b, inverseMetricInChart g c x a b *
        coordDeriv (fun y => cov2InChart g c y j b) a x) =
      ∑ a, ∑ b, inverseMetricInChart g c x a b *
        coordDeriv (fun y => cov2InChart g c y a j) b x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [K24WEITZ.inverseMetric_symm g hm.1 c x b a,
      coordDeriv_metric_symm g hm c x b j a]
  simp only [christoffelInChart, mul_add, mul_sub, Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [hc]
  ring

theorem matrix_pairing_eq_trace (A B : Mat4) (hB : ∀ a b, B a b = B b a) :
    (∑ a, ∑ b, A a b * B a b) = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hB a b]

theorem matrix_inverse_derivative_pairing_symm (P A B : Mat4)
    (hA : ∀ a b, A a b = A b a) (hB : ∀ a b, B a b = B b a) :
    (∑ a, ∑ b, (-(P * A * P)) a b * B a b) =
      ∑ a, ∑ b, (-(P * B * P)) a b * A a b := by
  rw [matrix_pairing_eq_trace _ _ hB, matrix_pairing_eq_trace _ _ hA]
  simp only [Matrix.neg_mul, Matrix.trace_neg]
  simpa only [Matrix.mul_assoc] using
    congrArg (fun t : ℝ => -t) (Matrix.trace_mul_comm (P * A) (P * B))

theorem inverseMetric_derivative_matrix (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    let D : Mat4 := fun a b => coordDeriv (fun y => cov2InChart g c y a b) i x
    let S : Mat4 := fun a b => coordDeriv (fun y => inverseMetricInChart g c y a b) i x
    S = -(inverseMetricInChart g c x * D * inverseMetricInChart g c x) := by
  dsimp only
  ext a b
  rw [K24WEITZ.inverseMetric_coordDeriv g hm hg c x hx i a b]
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

theorem inverseMetric_derivative_pairing_symm (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    (∑ a, ∑ b, coordDeriv (fun y => inverseMetricInChart g c y a b) i x *
      coordDeriv (fun y => cov2InChart g c y a b) j x) =
    ∑ a, ∑ b, coordDeriv (fun y => inverseMetricInChart g c y a b) j x *
      coordDeriv (fun y => cov2InChart g c y a b) i x := by
  have hi := inverseMetric_derivative_matrix g hm hg c x hx i
  have hj := inverseMetric_derivative_matrix g hm hg c x hx j
  dsimp only at hi hj
  change (∑ a, ∑ b, (fun a b => coordDeriv (fun y => inverseMetricInChart g c y a b) i x) a b *
      coordDeriv (fun y => cov2InChart g c y a b) j x) = _
  rw [hi]
  conv_rhs => change ∑ a, ∑ b, (fun a b => coordDeriv (fun y => inverseMetricInChart g c y a b) j x) a b *
      coordDeriv (fun y => cov2InChart g c y a b) i x
  rw [hj]
  exact matrix_inverse_derivative_pairing_symm _ _ _
    (coordDeriv_metric_symm g hm c x i) (coordDeriv_metric_symm g hm c x j)

theorem christoffel_trace_derivative (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    coordDeriv (fun y => ∑ k, christoffelInChart g c y k k j) i x =
      (1 / 2 : ℝ) * ∑ a, ∑ b,
        (coordDeriv (fun y => inverseMetricInChart g c y a b) i x *
          coordDeriv (fun y => cov2InChart g c y a b) j x +
        inverseMetricInChart g c x a b *
          coordDeriv (fun y => coordDeriv (fun z => cov2InChart g c z a b) j y) i x) := by
  have hP : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x :=
    fun a b => (K24SYM.metric_inverse_coefficient_C2 g hm hg c x hx a b).differentiableAt (by norm_num)
  have hD : ∀ a b, DifferentiableAt ℝ
      (fun y => coordDeriv (fun z => cov2InChart g c z a b) j y) x :=
    fun a b => (K24SYM.coordDeriv_contDiffAt
      (K24WEITZ.metric_coefficient_C2 g hg c x hx a b) j).differentiableAt (by norm_num)
  have hinner : ∀ a, DifferentiableAt ℝ (fun y => ∑ b, inverseMetricInChart g c y a b *
      coordDeriv (fun z => cov2InChart g c z a b) j y) x :=
    fun a => DifferentiableAt.fun_sum fun b _ => (hP a b).mul (hD a b)
  have htotal : DifferentiableAt ℝ (fun y => ∑ a, ∑ b, inverseMetricInChart g c y a b *
      coordDeriv (fun z => cov2InChart g c z a b) j y) x :=
    DifferentiableAt.fun_sum fun a _ => hinner a
  have heq : (fun y => ∑ k, christoffelInChart g c y k k j) =
      (fun y => (1 / 2 : ℝ) * ∑ a, ∑ b, inverseMetricInChart g c y a b *
        coordDeriv (fun z => cov2InChart g c z a b) j y) :=
    funext fun y => christoffel_trace g hm c y j
  rw [heq, K24OP.coordDeriv_mul _ _ x (differentiableAt_const _) htotal i]
  have hz : coordDeriv (fun _ => (1 / 2 : ℝ)) i x = 0 := by simp [coordDeriv]
  rw [hz, zero_mul, zero_add, K24OP.coordDeriv_sum _ _ x (fun a _ => hinner a) i]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [K24OP.coordDeriv_sum Finset.univ
    (fun b y => inverseMetricInChart g c y a b * coordDeriv (fun z => cov2InChart g c z a b) j y)
    x (fun b _ => (hP a b).mul (hD a b)) i]
  apply Finset.sum_congr rfl
  intro b _
  exact K24OP.coordDeriv_mul _ _ x (hP a b) (hD a b) i

/-- The contracted connection is a closed one-form in each chart. -/
theorem christoffel_trace_coordDeriv_symm (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    coordDeriv (fun y => ∑ k, christoffelInChart g c y k k j) i x =
      coordDeriv (fun y => ∑ k, christoffelInChart g c y k k i) j x := by
  rw [christoffel_trace_derivative g hm hg c x hx i j,
    christoffel_trace_derivative g hm hg c x hx j i]
  simp only [Finset.sum_add_distrib]
  rw [inverseMetric_derivative_pairing_symm g hm hg c x hx i j]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [K24WEITZCommutator.coordDeriv_commute (K24WEITZ.metric_coefficient_C2 g hg c x hx a b) i j]

/-- Ricci symmetry for the actual canonical curvature of a C2 metric. -/
theorem ricciInChart_symm (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ricciInChart g c x i j = ricciInChart g c x j i := by
  have hG : ∀ a b d, DifferentiableAt ℝ (fun y => christoffelInChart g c y a b d) x :=
    fun a b d => (K24SYM.christoffel_contDiffAt g hm hg c x hx a b d).differentiableAt (by norm_num)
  have ht : (∑ k, coordDeriv (fun y => christoffelInChart g c y k k j) i x) =
      ∑ k, coordDeriv (fun y => christoffelInChart g c y k k i) j x := by
    have h := christoffel_trace_coordDeriv_symm g hm hg c x hx i j
    rw [K24OP.coordDeriv_sum Finset.univ (fun k y => christoffelInChart g c y k k j) x
        (fun k _ => hG k k j) i,
      K24OP.coordDeriv_sum Finset.univ (fun k y => christoffelInChart g c y k k i) x
        (fun k _ => hG k k i) j] at h
    exact h
  have hd : ∀ k, coordDeriv (fun y => christoffelInChart g c y k i j) k x =
      coordDeriv (fun y => christoffelInChart g c y k j i) k x := by
    intro k
    congr 1
    funext y
    exact K24OPConnection.christoffel_symm g hm.1 c y k i j
  have hp : (∑ k, ∑ p, christoffelInChart g c x k k p * christoffelInChart g c x p i j) =
      ∑ k, ∑ p, christoffelInChart g c x k k p * christoffelInChart g c x p j i := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro p _
    rw [K24OPConnection.christoffel_symm g hm.1 c x p i j]
  have hq : (∑ k, ∑ p, christoffelInChart g c x k i p * christoffelInChart g c x p k j) =
      ∑ k, ∑ p, christoffelInChart g c x k j p * christoffelInChart g c x p k i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro p _
    rw [K24OPConnection.christoffel_symm g hm.1 c x p i k,
      K24OPConnection.christoffel_symm g hm.1 c x k p j]
    ring
  simp only [ricciInChart, curvatureInChart, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [hd]
  rw [ht, hp, hq]


end K24.Global.K24WEITZRicci


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24WEITZ
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

lemma bianchi_killing_coefficients (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    bianchiInChart g (killing g Y) c x j =
      -(∑ a, ∑ b, ∑ d, inverseMetricInChart g c x a b * cov2InChart g c x j d *
        secondNablaVectorInChart g Y c x a b d) -
      (∑ k, ricciInChart g c x k j * vectorInChart Y c x k) := by
  rw [bianchi_killing_ricci_transpose g hm hg Y hY c x hx j]
  simp_rw [K24WEITZRicci.ricciInChart_symm g hm hg c x hx j]

theorem native_weitzenbock (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (Y : RawVector M) (hY : VectorContDiff 2 Y) :
    bianchi g (killing g Y) = roughVectorLaplacianFlat g Y - ricciVectorFlat g Y := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  have hx : chartAt FourSpace p p ∈ (chartAt FourSpace p).target :=
    (chartAt FourSpace p).map_source (mem_chart_source FourSpace p)
  have hb : bianchiInChart g (killing g Y) p (chartAt FourSpace p p) =
      (fun j => -(∑ a, ∑ b, ∑ d, inverseMetricInChart g p (chartAt FourSpace p p) a b *
        cov2InChart g p (chartAt FourSpace p p) j d *
        secondNablaVectorInChart g Y p (chartAt FourSpace p p) a b d)) -
      (fun j => ∑ k, ricciInChart g p (chartAt FourSpace p p) k j *
        vectorInChart Y p (chartAt FourSpace p p) k) := by
    funext j
    exact bianchi_killing_coefficients g hm hg Y hY p (chartAt FourSpace p p) hx j
  have hV : vectorInChart Y p (chartAt FourSpace p p) =
      mfderiv I4 I4 (chartAt FourSpace p) p (Y p) := by
    dsimp only [vectorInChart]
    erw [(chartAt FourSpace p).left_inv (mem_chart_source FourSpace p)]
  change coefficientsToCovector (bianchiInChart g (killing g Y) p (chartAt FourSpace p p))
      (mfderiv I4 I4 (chartAt FourSpace p) p v) =
    coefficientsToCovector (fun j => -(∑ a, ∑ b, ∑ d,
      inverseMetricInChart g p (chartAt FourSpace p p) a b *
      cov2InChart g p (chartAt FourSpace p p) j d *
      secondNablaVectorInChart g Y p (chartAt FourSpace p p) a b d))
      (mfderiv I4 I4 (chartAt FourSpace p) p v) -
    matrixToBilinear (ricciInChart g p (chartAt FourSpace p p))
      (mfderiv I4 I4 (chartAt FourSpace p) p (Y p))
      (mfderiv I4 I4 (chartAt FourSpace p) p v)
  rw [hb, coefficientsToCovector_sub, sub_apply, matrixToBilinear_left, hV]

end K24.Global.K24WEITZ


open K24.Global
universe u

theorem solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (g : RawCov2 M) (Y : RawVector M),
      IsMetric g → Cov2ContDiff 2 g → VectorContDiff 2 Y →
      bianchi g (killing g Y) = roughVectorLaplacianFlat g Y - ricciVectorFlat g Y := by
  intro M _ _ _ g Y hm hg hY
  exact K24WEITZ.native_weitzenbock g hm hg Y hY

theorem K24WEITZ_exact_type_wrapper :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (g : RawCov2 M) (Y : RawVector M),
      IsMetric g → Cov2ContDiff 2 g → VectorContDiff 2 Y →
      bianchi g (killing g Y) = roughVectorLaplacianFlat g Y - ricciVectorFlat g Y := solution

#print axioms solution
#print axioms K24WEITZ_exact_type_wrapper
