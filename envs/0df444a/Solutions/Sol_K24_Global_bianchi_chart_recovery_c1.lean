-- Prove2me | solution 1 for K24.Global.bianchi_chart_recovery_c1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:27:18.534578+00:00
-- url     : https://prove2.me/submissions/d0f6d14c-993e-4a68-9a6f-62ab04385db4

import Definitions.Def_K24GlobalStatement

/- Inlined checked module: Infrastructure.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem cov2InChart_symmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (i j : Fin 4) :
    cov2InChart g c x i j = cov2InChart g c x j i := by
  exact hg _ _ _

theorem cov2InChart_isUnit_det [IsManifold I4 ∞ M] (g : RawCov2 M)
    (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    IsUnit (cov2InChart g c x).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.PosDef.isUnit
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      cov2InChart_symmetric g hg.1 c x j i
  · intro v hv
    let w : FourSpace := ∑ i, v i • basisVector i
    have hw : w ≠ 0 := by
      intro hw
      apply hv
      funext i
      have h := congrArg (fun q : FourSpace => q i) hw
      simpa [w, basisVector, Pi.single_apply] using h
    let e := chartAt FourSpace c
    let di := mfderiv I4 I4 e.symm x
    have hinj : Function.Injective di := by
      apply Function.LeftInverse.injective (g := mfderiv I4 I4 e (e.symm x))
      intro v
      exact congrArg (fun A => A v) ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hx)
    have hdi : di w ≠ 0 := by
      intro h
      exact hw (hinj (h.trans (map_zero di).symm))
    have hpos := hg.2 (e.symm x) (di w) hdi
    have heq : star v ⬝ᵥ (cov2InChart g c x *ᵥ v) =
        g (e.symm x) (di w) (di w) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        cov2InChart, w, map_sum, map_smul, _root_.sum_apply,
        _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hg.1 (e.symm x) (di (basisVector j)) (di (basisVector i))]
      ring
    rw [heq]
    exact hpos

theorem differentiableAt_inverseMetric [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x) :
    DifferentiableAt ℝ (inverseMetricInChart g c) x := by
  have hentry (a b : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hDg a) b
  have hdet : DifferentiableAt ℝ (fun y => (cov2InChart g c y).det) x := by
    simp only [Matrix.det_apply']
    apply DifferentiableAt.fun_sum
    intro σ _
    apply DifferentiableAt.const_mul
    exact (HasFDerivAt.finsetProd (u := Finset.univ)
      (fun i _ => (hentry (σ i) i).hasFDerivAt)).differentiableAt
  have hne : (cov2InChart g c x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (cov2InChart_isUnit_det g hg c x hx)
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  simp only [inverseMetricInChart, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  apply (hdet.inv hne).mul
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  have hrow (i : Fin 4) : DifferentiableAt ℝ
      (fun y => Matrix.updateRow (cov2InChart g c y) b (Pi.single a 1) (σ i) i) x := by
    simp only [Matrix.updateRow_apply]
    split_ifs <;> first | exact differentiableAt_const _ | exact hentry _ _
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun i _ => (hrow i).hasFDerivAt)).differentiableAt

theorem christoffel_symmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (d a b : Fin 4) :
    christoffelInChart g c x d a b = christoffelInChart g c x d b a := by
  have hs : (fun y => cov2InChart g c y a b) =
      (fun y => cov2InChart g c y b a) := by
    funext y
    exact hg _ _ _
  unfold christoffelInChart
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem christoffel_lower [IsManifold I4 ∞ M]
    (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b d : Fin 4) :
    2 * (∑ p : Fin 4, christoffelInChart g c x p a b * cov2InChart g c x p d) =
      coordDeriv (fun y => cov2InChart g c y b d) a x +
      coordDeriv (fun y => cov2InChart g c y a d) b x -
      coordDeriv (fun y => cov2InChart g c y a b) d x := by
  let A := cov2InChart g c x
  let K := fun r => coordDeriv (fun y => cov2InChart g c y b r) a x +
    coordDeriv (fun y => cov2InChart g c y a r) b x -
    coordDeriv (fun y => cov2InChart g c y a b) r x
  have hsum : (∑ p, christoffelInChart g c x p a b * cov2InChart g c x p d) =
      (1 / 2 : ℝ) * (A *ᵥ (A⁻¹ *ᵥ K)) d := by
    change (∑ p, christoffelInChart g c x p a b * cov2InChart g c x p d) =
      (1 / 2 : ℝ) * ∑ p, cov2InChart g c x d p * ∑ r, inverseMetricInChart g c x p r * K r
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [cov2InChart_symmetric g hg.1 c x p d]
    unfold christoffelInChart K
    ring
  rw [hsum, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
    (cov2InChart_isUnit_det g hg c x hx), Matrix.one_mulVec]
  dsimp [K]
  ring


end K24.Global.IdentityProof

namespace K24.Global.LieNaturality
abbrev Form := FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)

abbrev matrixToForm : Mat4 → Form := matrixToBilinear

@[simp] theorem matrixToForm_apply (A : Mat4) : matrixToForm A = matrixToBilinear A := rfl

theorem fderiv_form_apply (A : FourSpace → Form) (U V : FourSpace → FourSpace)
    (x t : FourSpace) (hA : DifferentiableAt ℝ A x)
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => A y (U y) (V y)) x t =
      fderiv ℝ A x t (U x) (V x) + A x (fderiv ℝ U x t) (V x) +
        A x (U x) (fderiv ℝ V x t) := by
  rw [fderiv_clm_apply (hA.clm_apply hU) hV, fderiv_clm_apply hA hU]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

theorem fderiv_form_const (A : FourSpace → Form) (x t u v : FourSpace)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => A y u v) x t = fderiv ℝ A x t u v := by
  rw [fderiv_form_apply A (fun _ => u) (fun _ => v) x t hA
    (differentiableAt_const _) (differentiableAt_const _)]
  simp

theorem fderiv_derivative_apply (F : FourSpace → FourSpace) (x t u : FourSpace)
    (hF : DifferentiableAt ℝ (fderiv ℝ F) x) :
    fderiv ℝ (fun y => fderiv ℝ F y u) x t = fderiv ℝ (fderiv ℝ F) x t u := by
  rw [fderiv_clm_apply hF (differentiableAt_const _)]
  simp

@[simp] theorem matrixToForm_basis (A : Mat4) (i j : Fin 4) :
    matrixToForm A (basisVector i) (basisVector j) = A i j := by
  simp [matrixToForm_apply, matrixToBilinear, coordProj, basisVector]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def formInChart (g : RawCov2 M) (c : M) : FourSpace → Form :=
  matrixToForm ∘ cov2InChart g c

theorem formInChart_eq (g : RawCov2 M) (c : M) (x : FourSpace) :
    formInChart g c x = bilinearPullback (g ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (chartAt FourSpace c).symm x) := by
  exact matrixToBilinear_recover
    (bilinearPullback (g ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (chartAt FourSpace c).symm x))

theorem formInChart_differentiableAt (g : RawCov2 M) (c : M) (x : FourSpace)
    (hg : DifferentiableAt ℝ (cov2InChart g c) x) :
    DifferentiableAt ℝ (formInChart g c) x := by
  have heq : formInChart g c = fun y => ∑ i : Fin 4, ∑ j : Fin 4,
      cov2InChart g c y i j • (coordProj i).smulRight (coordProj j) := by
    ext y u v
    simp only [formInChart, Function.comp_apply, matrixToForm_apply, matrixToBilinear,
      _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  apply DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun i y => ∑ j : Fin 4, cov2InChart g c y i j • (coordProj i).smulRight (coordProj j))
  intro i _
  apply DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun j y => cov2InChart g c y i j • (coordProj i).smulRight (coordProj j))
  intro j _
  let T : ℝ →L[ℝ] Form := ContinuousLinearMap.toSpanSingleton ℝ
    ((coordProj i).smulRight (coordProj j))
  exact DifferentiableAt.comp (g := T) (f := fun y => cov2InChart g c y i j) x
    (ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := ℝ) (F := Form) T) (differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j)


end K24.Global.LieNaturality

namespace K24.Global.LieNaturality
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

def chartTransition (c d : M) : FourSpace → FourSpace :=
  (chartAt FourSpace d) ∘ (chartAt FourSpace c).symm

theorem chartTransition_smooth (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (chartTransition c d) x := by
  apply ContMDiffAt.contDiffAt
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas d) hd).comp x
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hx)

theorem chartTransition_derivative (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (chartTransition c d) x =
      (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm x)).comp
        (mfderiv I4 I4 (chartAt FourSpace c).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x ((mdifferentiable_chart (I := I4) d).mdifferentiableAt hd)
    ((mdifferentiable_chart (I := I4) c).symm.mdifferentiableAt hx)

theorem chartTransition_inverse_differential (c d : M) (x v : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v) =
      mfderiv I4 I4 (chartAt FourSpace c).symm x v := by
  rw [chartTransition_derivative c d x hx hd]
  exact congrArg (fun D => D (mfderiv I4 I4 (chartAt FourSpace c).symm x v))
    ((mdifferentiable_chart (I := I4) d).symm_comp_deriv hd)

theorem chartTransition_form (g : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    formInChart g c x = bilinearPullback (formInChart g d (chartTransition c d x))
      (fderiv ℝ (chartTransition c d) x) := by
  rw [formInChart_eq, formInChart_eq]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change g ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x u)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x v) =
    g ((chartAt FourSpace d).symm (chartTransition c d x))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x u))
      (mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v))
  rw [chartTransition_inverse_differential c d x u hx hd,
    chartTransition_inverse_differential c d x v hx hd]
  change g ((chartAt FourSpace c).symm x) _ _ =
    g ((chartAt FourSpace d).symm ((chartAt FourSpace d) ((chartAt FourSpace c).symm x))) _ _
  rw [(chartAt FourSpace d).left_inv hd]

theorem chartTransition_overlap_eventually (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source := by
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx,
    ((chartAt FourSpace c).continuousAt_symm hx).tendsto
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hdy
  exact ⟨hy, hdy⟩

theorem chartTransition_comp_chart_differential (c d p : M)
    (hc : p ∈ (chartAt FourSpace c).source) (hd : p ∈ (chartAt FourSpace d).source)
    (v : TangentSpace I4 p) :
    fderiv ℝ (chartTransition c d) (chartAt FourSpace c p)
      (mfderiv I4 I4 (chartAt FourSpace c) p v) = mfderiv I4 I4 (chartAt FourSpace d) p v := by
  have hcd : (chartAt FourSpace c).symm (chartAt FourSpace c p) ∈ (chartAt FourSpace d).source := by
    rw [(chartAt FourSpace c).left_inv hc]
    exact hd
  rw [chartTransition_derivative c d _ ((chartAt FourSpace c).map_source hc) hcd]
  have hcancel := congrArg (fun D => D v) ((mdifferentiable_chart (I := I4) c).symm_comp_deriv hc)
  change mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
    (mfderiv I4 I4 (chartAt FourSpace c) p v) = v at hcancel
  change mfderiv I4 I4 (chartAt FourSpace d)
    ((chartAt FourSpace c).symm (chartAt FourSpace c p))
    (mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
      (mfderiv I4 I4 (chartAt FourSpace c) p v)) = _
  rw [hcancel, (chartAt FourSpace c).left_inv hc]


end K24.Global.LieNaturality

/- Inlined checked module: Connection.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

abbrev Cov3 := FourSpace →L[ℝ] Form
abbrev Gamma := FourSpace →L[ℝ] (FourSpace →L[ℝ] FourSpace)

def flipForm : Form →L[ℝ] Form :=
  (ContinuousLinearMap.flipₗᵢ ℝ FourSpace FourSpace ℝ).toContinuousLinearEquiv.toContinuousLinearMap

def koszulForm (D : Cov3) : Cov3 := D + D.flip - flipForm.comp D.flip

@[simp] theorem koszulForm_apply (D : Cov3) (v w t : FourSpace) :
    koszulForm D v w t = D v w t + D w v t - D t v w := rfl

def gammaForm (g : RawCov2 M) (c : M) (x : FourSpace) : Gamma :=
  ∑ i : Fin 4, ∑ j : Fin 4, (coordProj i).smulRight
    ((coordProj j).smulRight (∑ p : Fin 4, christoffelInChart g c x p i j • basisVector p))

@[simp] theorem gammaForm_basis (g : RawCov2 M) (c : M) (x : FourSpace) (i j : Fin 4) :
    gammaForm g c x (basisVector i) (basisVector j) =
      ∑ p : Fin 4, christoffelInChart g c x p i j • basisVector p := by
  simp [gammaForm, coordProj, basisVector]

theorem clm_eq_of_basis {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : FourSpace →L[ℝ] V) (h : ∀ i, A (basisVector i) = B (basisVector i)) : A = B := by
  ext v
  calc
    A v = A (∑ i, v i • basisVector i) := by rw [sum_basisVector]
    _ = B (∑ i, v i • basisVector i) := by simp only [map_sum, map_smul, h]
    _ = B v := by rw [sum_basisVector]

def lowerGamma (G : Form) (Q : Gamma) : Cov3 :=
  (ContinuousLinearMap.compL ℝ FourSpace FourSpace (FourSpace →L[ℝ] ℝ) G).comp Q

@[simp] theorem lowerGamma_apply (G : Form) (Q : Gamma) (v w t : FourSpace) :
    lowerGamma G Q v w t = G (Q v w) t := rfl

theorem formInChart_derivative_basis (g : RawCov2 M) (c : M) (x : FourSpace)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x) (i j k : Fin 4) :
    fderiv ℝ (formInChart g c) x (basisVector i) (basisVector j) (basisVector k) =
      coordDeriv (fun y => cov2InChart g c y j k) i x := by
  rw [← fderiv_form_const _ x (basisVector i) (basisVector j) (basisVector k)
    (formInChart_differentiableAt g c x hDg)]
  have heq : (fun y => formInChart g c y (basisVector j) (basisVector k)) =
      (fun y => cov2InChart g c y j k) := by
    funext y
    exact matrixToForm_basis _ j k
  rw [heq]
  rfl

theorem gammaForm_lower (g : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x) (v w t : FourSpace) :
    2 * formInChart g c x (gammaForm g c x v w) t =
      koszulForm (fderiv ℝ (formInChart g c) x) v w t := by
  have heq : (2 : ℝ) • lowerGamma (formInChart g c x) (gammaForm g c x) =
      koszulForm (fderiv ℝ (formInChart g c) x) := by
    apply clm_eq_of_basis
    intro i
    apply clm_eq_of_basis
    intro j
    apply clm_eq_of_basis
    intro k
    simp only [_root_.smul_apply, smul_eq_mul, lowerGamma_apply, koszulForm_apply,
      gammaForm_basis, map_sum, map_smul, _root_.sum_apply,
      formInChart_derivative_basis g c x hDg]
    simp only [formInChart, Function.comp_apply, matrixToForm_basis]
    change 2 * (∑ p, christoffelInChart g c x p i j * cov2InChart g c x p k) = _
    exact christoffel_lower g hg c x hx i j k
  exact congrArg (fun D : Cov3 => D v w t) heq

theorem fderiv_pullback_relation (A B : FourSpace → Form) (F : FourSpace → FourSpace)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hA : DifferentiableAt ℝ A (F x)) (hB : DifferentiableAt ℝ B x)
    (heq : B =ᶠ[𝓝 x] (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y)))
    (v w t : FourSpace) :
    fderiv ℝ B x v w t =
      fderiv ℝ A (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) (fderiv ℝ F x t) +
      A (F x) (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x t) +
      A (F x) (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v t) := by
  have hF1 := hF.differentiableAt (by norm_num)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heval : (fun y => B y w t) =ᶠ[𝓝 x]
      (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y) w t) :=
    heq.mono (fun y hy => congrArg (fun Q : Form => Q w t) hy)
  have h := congrArg (fun D : FourSpace →L[ℝ] ℝ => D v) (heval.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_form_const B x v w t hB] at h
  change fderiv ℝ B x v w t =
    fderiv ℝ (fun y => A (F y) (fderiv ℝ F y w) (fderiv ℝ F y t)) x v at h
  rw [fderiv_form_apply (fun y => A (F y)) (fun y => fderiv ℝ F y w)
    (fun y => fderiv ℝ F y t) x v (hA.comp x hF1)
      (hDF.clm_apply (differentiableAt_const _)) (hDF.clm_apply (differentiableAt_const _)),
    fderiv_fun_comp x hA hF1, fderiv_derivative_apply F x v w hDF,
    fderiv_derivative_apply F x v t hDF] at h
  exact h

theorem koszulForm_natural (A B : FourSpace → Form) (F : FourSpace → FourSpace)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hA : DifferentiableAt ℝ A (F x)) (hB : DifferentiableAt ℝ B x)
    (hsym : ∀ v w, A (F x) v w = A (F x) w v)
    (heq : B =ᶠ[𝓝 x] (fun y => bilinearPullback (A (F y)) (fderiv ℝ F y)))
    (v w t : FourSpace) :
    koszulForm (fderiv ℝ B x) v w t =
      koszulForm (fderiv ℝ A (F x)) (fderiv ℝ F x v) (fderiv ℝ F x w) (fderiv ℝ F x t) +
      2 * A (F x) (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x t) := by
  simp only [koszulForm_apply]
  rw [fderiv_pullback_relation A B F x hF hA hB heq v w t,
    fderiv_pullback_relation A B F x hF hA hB heq w v t,
    fderiv_pullback_relation A B F x hF hA hB heq t v w]
  have hH := hF.isSymmSndFDerivAt (by norm_num)
  rw [hH.eq w v, hH.eq t v, hH.eq t w,
    hsym (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v t)]
  ring

theorem formInChart_symmetric (g : RawCov2 M) (hg : IsSymmetricCov2 g)
    (c : M) (x v w : FourSpace) : formInChart g c x v w = formInChart g c x w v := by
  rw [formInChart_eq]
  exact hg _ _ _

theorem formInChart_positive (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (v : FourSpace) (hv : v ≠ 0) :
    0 < formInChart g c x v v := by
  rw [formInChart_eq]
  apply hg.2
  intro hzero
  apply hv
  have hinj := (mdifferentiable_chart (I := I4) c).symm.mfderiv_injective hx
  apply hinj
  exact hzero.trans (map_zero _).symm

theorem formInChart_separates (g : RawCov2 M) (hg : IsMetric g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (v w : FourSpace)
    (h : ∀ t, formInChart g c x v t = formInChart g c x w t) : v = w := by
  by_contra hne
  have hpos := formInChart_positive g hg c x hx (v-w) (sub_ne_zero.mpr hne)
  have hzero : formInChart g c x (v-w) (v-w) = 0 := by
    rw [map_sub (formInChart g c x) v w, ContinuousLinearMap.sub_apply, h, sub_self]
  linarith


theorem chartTransition_derivative_bijective (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    Function.Bijective (fderiv ℝ (chartTransition c d) x) := by
  rw [chartTransition_derivative c d x hx hd]
  exact ((mdifferentiable_chart (I := I4) d).mfderiv_bijective hd).comp
    ((mdifferentiable_chart (I := I4) c).symm.mfderiv_bijective hx)

theorem chartTransition_form_eventually (u : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    formInChart u c =ᶠ[𝓝 x] (fun y =>
      bilinearPullback (formInChart u d (chartTransition c d y))
        (fderiv ℝ (chartTransition c d) y)) := by
  filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
  exact chartTransition_form u c d y hy.1 hy.2

theorem gammaForm_natural (g : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (v w : FourSpace) :
    fderiv ℝ (chartTransition c d) x (gammaForm g c x v w) =
      gammaForm g d (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) +
      fderiv ℝ (fderiv ℝ (chartTransition c d)) x v w := by
  let F := chartTransition c d
  have hFx : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hgc := ((hDg c).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd := ((hDg d).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hFx)).differentiableAt (by norm_num)
  apply formInChart_separates g hg d (F x) hFx
  intro t
  obtain ⟨r, rfl⟩ := (chartTransition_derivative_bijective c d x hx hd).2 t
  have hG := congrArg (fun Q : Form => Q (gammaForm g c x v w) r)
    (chartTransition_form g c d x hx hd)
  change formInChart g c x (gammaForm g c x v w) r =
    formInChart g d (F x) (fderiv ℝ F x (gammaForm g c x v w)) (fderiv ℝ F x r) at hG
  have hK := koszulForm_natural (formInChart g d) (formInChart g c) F x
    ((chartTransition_smooth c d x hx hd).of_le (by decide))
    (formInChart_differentiableAt g d (F x) hgd)
    (formInChart_differentiableAt g c x hgc)
    (formInChart_symmetric g hg.1 d (F x))
    (chartTransition_form_eventually g c d x hx hd) v w r
  rw [← gammaForm_lower g hg c x hx hgc v w r,
    ← gammaForm_lower g hg d (F x) hFx hgd] at hK
  rw [hG] at hK
  simp only [map_add, ContinuousLinearMap.add_apply]
  change formInChart g d (F x) (fderiv ℝ F x (gammaForm g c x v w)) (fderiv ℝ F x r) = _
  linarith

end K24.Global.BianchiNaturality

/- Inlined checked module: Covariant.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem chartTransition_symm_apply (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    chartTransition d c (chartTransition c d x) = x := by
  simp only [chartTransition, Function.comp_apply,
    (chartAt FourSpace d).left_inv hd, (chartAt FourSpace c).right_inv hx]

theorem cov2InChart_differentiableAt_overlap (u : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) :
    DifferentiableAt ℝ (cov2InChart u d) (chartTransition c d x) := by
  let y := chartTransition c d x
  let F := chartTransition d c
  have hy : y ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hc : (chartAt FourSpace d).symm y ∈ (chartAt FourSpace c).source := by
    dsimp [y, chartTransition]
    rw [(chartAt FourSpace d).left_inv hd]
    exact (chartAt FourSpace c).map_target hx
  have hFy : F y = x := chartTransition_symm_apply c d x hx hd
  have hF : ContDiffAt ℝ 2 F y := (chartTransition_smooth d c y hy hc).of_le (by decide)
  have hF1 := hF.differentiableAt (by norm_num)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hU : DifferentiableAt ℝ (formInChart u c) (F y) := by
    rw [hFy]
    exact formInChart_differentiableAt u c x hDu
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have h := ((hU.comp y hF1).clm_apply (hDF.clm_apply (differentiableAt_const (basisVector i)))).clm_apply
    (hDF.clm_apply (differentiableAt_const (basisVector j)))
  apply h.congr_of_eventuallyEq
  filter_upwards [chartTransition_form_eventually u d c y hy hc] with z hz
  have hz' := congrArg (fun A : Form => A (basisVector i) (basisVector j)) hz
  simpa only [bilinearPullback_apply, formInChart, Function.comp_apply, matrixToForm_basis] using hz'

def nablaForm (g u : RawCov2 M) (c : M) (x : FourSpace) : Cov3 :=
  fderiv ℝ (formInChart u c) x - lowerGamma (formInChart u c x) (gammaForm g c x) -
    flipForm.comp (lowerGamma (formInChart u c x).flip (gammaForm g c x))

@[simp] theorem nablaForm_apply (g u : RawCov2 M) (c : M) (x v w t : FourSpace) :
    nablaForm g u c x v w t = fderiv ℝ (formInChart u c) x v w t -
      formInChart u c x (gammaForm g c x v w) t -
      formInChart u c x w (gammaForm g c x v t) := rfl

theorem nablaForm_basis (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (i j k : Fin 4) :
    nablaForm g u c x (basisVector i) (basisVector j) (basisVector k) =
      nablaTensorInChart g u c x i j k := by
  simp only [nablaForm_apply, formInChart_derivative_basis u c x hDu,
    gammaForm_basis, map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp only [formInChart, Function.comp_apply, matrixToForm_basis, nablaTensorInChart]

theorem nablaForm_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (v w t : FourSpace) :
    nablaForm g u c x v w t = nablaForm g u d (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w)
      (fderiv ℝ (chartTransition c d) x t) := by
  have hDd := cov2InChart_differentiableAt_overlap u c d x hx hd hDu
  simp only [nablaForm_apply]
  rw [fderiv_pullback_relation (formInChart u d) (formInChart u c) (chartTransition c d) x
    ((chartTransition_smooth c d x hx hd).of_le (by decide))
    (formInChart_differentiableAt u d _ hDd)
    (formInChart_differentiableAt u c x hDu)
    (chartTransition_form_eventually u c d x hx hd)]
  rw [chartTransition_form u c d x hx hd]
  simp only [bilinearPullback_apply, gammaForm_natural g hg hDg c d x hx hd,
    map_add, _root_.add_apply]
  ring

end K24.Global.BianchiNaturality

/- Inlined checked module: Contraction.lean -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise

namespace K24.Global.BianchiContraction

def matrixOf (J : FourSpace →L[ℝ] FourSpace) : Mat4 :=
  fun k i => J (basisVector i) k

theorem matrixToBilinear_apply (G : Mat4) (v w : FourSpace) :
    matrixToBilinear G v w = ∑ i : Fin 4, ∑ j : Fin 4, v i * (G i j * w j) := by
  simp [matrixToBilinear, coordProj]

theorem matrixToBilinear_basis (G : Mat4) (i j : Fin 4) :
    matrixToBilinear G (basisVector i) (basisVector j) = G i j := by
  simp [matrixToBilinear_apply, basisVector]

theorem bilinear_apply (A : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)) (v w : FourSpace) :
    A v w = ∑ i : Fin 4, ∑ j : Fin 4,
      v i * (A (basisVector i) (basisVector j) * w j) := by
  have h := congrArg (fun B : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ) => B v w)
    (matrixToBilinear_recover A)
  exact h.symm.trans (matrixToBilinear_apply _ _ _)

theorem metric_matrix (J : FourSpace →L[ℝ] FourSpace) (G H : Mat4)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w)) :
    G = (matrixOf J).transpose * H * matrixOf J := by
  ext i j
  calc
    G i j = matrixToBilinear H (J (basisVector i)) (J (basisVector j)) := by
      rw [← hmetric, matrixToBilinear_basis]
    _ = ((matrixOf J).transpose * H * matrixOf J) i j := by
      simp only [matrixToBilinear_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.sum_mul, matrixOf]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem matrixOf_isUnit_det (J : FourSpace →L[ℝ] FourSpace) (G H : Mat4)
    (hG : IsUnit G.det)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w)) :
    IsUnit (matrixOf J).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply isUnit_iff_ne_zero.mp hG
  rw [metric_matrix J G H hmetric, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp [hz]

theorem inverse_metric_matrix (J : FourSpace →L[ℝ] FourSpace) (G H : Mat4)
    (hG : IsUnit G.det)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w)) :
    matrixOf J * G⁻¹ * (matrixOf J).transpose = H⁻¹ := by
  have hJ := matrixOf_isUnit_det J G H hG hmetric
  calc
    matrixOf J * G⁻¹ * (matrixOf J).transpose =
        (matrixOf J * (matrixOf J)⁻¹) * H⁻¹ *
          (((matrixOf J).transpose)⁻¹ * (matrixOf J).transpose) := by
      rw [metric_matrix J G H hmetric, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    _ = H⁻¹ := by
      rw [Matrix.mul_nonsing_inv _ hJ,
        Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose _ hJ)]
      simp


theorem contract_natural (J : FourSpace →L[ℝ] FourSpace) (_hJ : Function.Bijective J)
    (G H : Mat4) (hG : IsUnit G.det) (_hH : IsUnit H.det)
    (hmetric : ∀ v w : FourSpace,
      matrixToBilinear G v w = matrixToBilinear H (J v) (J w))
    (A : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)) :
    (∑ i : Fin 4, ∑ j : Fin 4, (G⁻¹) i j * A (J (basisVector i)) (J (basisVector j))) =
      ∑ i : Fin 4, ∑ j : Fin 4, (H⁻¹) i j * A (basisVector i) (basisVector j) := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        (matrixOf J k i * (G⁻¹) i j * matrixOf J l j) *
          A (basisVector k) (basisVector l) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [bilinear_apply A (J (basisVector i)) (J (basisVector j))]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      dsimp [matrixOf]
      ring
    _ = ∑ k : Fin 4, ∑ l : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        (matrixOf J k i * (G⁻¹) i j * matrixOf J l j) *
          A (basisVector k) (basisVector l) := by
      simpa only [Fintype.sum_prod_type] using
        (Finset.sum_comm (s := (Finset.univ : Finset (Fin 4 × Fin 4)))
          (t := (Finset.univ : Finset (Fin 4 × Fin 4)))
          (f := fun p q => (matrixOf J q.1 p.1 * (G⁻¹) p.1 p.2 * matrixOf J q.2 p.2) *
            A (basisVector q.1) (basisVector q.2)))
    _ = ∑ k : Fin 4, ∑ l : Fin 4,
        (matrixOf J * G⁻¹ * (matrixOf J).transpose) k l *
          A (basisVector k) (basisVector l) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by rw [inverse_metric_matrix J G H hG hmetric]

end K24.Global.BianchiContraction

/- Inlined checked module: TraceBasics.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

def cov3Slice (C : Cov3) (t : FourSpace) : Form :=
  (ContinuousLinearMap.compL ℝ FourSpace (FourSpace →L[ℝ] ℝ) ℝ
    (ContinuousLinearMap.apply ℝ ℝ t)).comp C

@[simp] theorem cov3Slice_apply (C : Cov3) (t v w : FourSpace) :
    cov3Slice C t v w = C v w t := rfl

def divergenceForm (g u : RawCov2 M) (c : M) (x : FourSpace) : FourSpace →L[ℝ] ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, inverseMetricInChart g c x i j •
    nablaForm g u c x (basisVector i) (basisVector j)

@[simp] theorem divergenceForm_apply (g u : RawCov2 M) (c : M) (x t : FourSpace) :
    divergenceForm g u c x t = ∑ i : Fin 4, ∑ j : Fin 4,
      inverseMetricInChart g c x i j * nablaForm g u c x (basisVector i) (basisVector j) t := by
  simp [divergenceForm]

def bianchiForm (g u : RawCov2 M) (c : M) (x : FourSpace) : FourSpace →L[ℝ] ℝ :=
  -divergenceForm g u c x + (1 / 2 : ℝ) • fderiv ℝ (metricTraceInChart g u c) x

@[simp] theorem bianchiForm_apply (g u : RawCov2 M) (c : M) (x t : FourSpace) :
    bianchiForm g u c x t = -divergenceForm g u c x t +
      (1 / 2 : ℝ) * fderiv ℝ (metricTraceInChart g u c) x t := by
  rfl

theorem bianchiForm_basis (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (j : Fin 4) :
    bianchiForm g u c x (basisVector j) = bianchiInChart g u c x j := by
  simp only [bianchiForm_apply, divergenceForm_apply, nablaForm_basis g u c x hDu,
    bianchiInChart, coordDeriv]

theorem bianchiForm_eq (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) :
    bianchiForm g u c x = coefficientsToCovector (bianchiInChart g u c x) := by
  rw [← coefficientsToCovector_recover (bianchiForm g u c x)]
  congr 1
  funext j
  exact bianchiForm_basis g u c x hDu j

theorem metricTraceInChart_differentiableAt (g u : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hDg : DifferentiableAt ℝ (cov2InChart g c) x)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  have hinv := differentiableAt_inverseMetric g hg c x hx hDg
  unfold metricTraceInChart
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.fun_sum
  intro j _
  exact ((differentiableAt_pi.mp (differentiableAt_pi.mp hinv i) j)).mul
    (differentiableAt_pi.mp (differentiableAt_pi.mp hDu i) j)


theorem covectorFromCoordinates_chart_value
    (a : M → FourSpace → Fin 4 → ℝ) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    covectorInChart (covectorFromCoordinates a) c x j =
      coefficientsToCovector
        (a ((chartAt FourSpace c).symm x)
          (chartAt FourSpace ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm x)))
        (fderiv ℝ (chartTransition c ((chartAt FourSpace c).symm x)) x (basisVector j)) := by
  rw [chartTransition_derivative c ((chartAt FourSpace c).symm x) x hx
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm x))]
  rfl

end K24.Global.BianchiNaturality

/- Inlined checked module: BianchiRecovery.lean -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 32
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter Matrix

namespace K24.Global.BianchiNaturality
open LieNaturality IdentityProof BianchiContraction
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem chartTransition_metric (g : RawCov2 M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) (v w : FourSpace) :
    matrixToBilinear (cov2InChart g c x) v w =
      matrixToBilinear (cov2InChart g d (chartTransition c d x))
        (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) := by
  exact congrArg (fun A : Form => A v w) (chartTransition_form g c d x hx hd)

theorem metricTraceInChart_natural (g u : RawCov2 M) (hg : IsMetric g)
    (c d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    metricTraceInChart g u c x = metricTraceInChart g u d (chartTransition c d x) := by
  have hy := (chartAt FourSpace d).map_source hd
  have hC := contract_natural (fderiv ℝ (chartTransition c d) x)
    (chartTransition_derivative_bijective c d x hx hd)
    (cov2InChart g c x) (cov2InChart g d (chartTransition c d x))
    (cov2InChart_isUnit_det g hg c x hx)
    (cov2InChart_isUnit_det g hg d _ hy)
    (chartTransition_metric g c d x hx hd)
    (formInChart u d (chartTransition c d x))
  have hu (i j : Fin 4) : cov2InChart u c x i j =
      formInChart u d (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x (basisVector i))
        (fderiv ℝ (chartTransition c d) x (basisVector j)) := by
    simpa only [bilinearPullback_apply, formInChart, Function.comp_apply, matrixToForm_basis] using
      congrArg (fun A : Form => A (basisVector i) (basisVector j))
        (chartTransition_form u c d x hx hd)
  unfold metricTraceInChart inverseMetricInChart
  simp_rw [hu]
  simpa only [formInChart, Function.comp_apply, matrixToForm_basis] using hC

theorem divergenceForm_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (t : FourSpace) :
    divergenceForm g u c x t = divergenceForm g u d (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x t) := by
  have hy := (chartAt FourSpace d).map_source hd
  have hC := contract_natural (fderiv ℝ (chartTransition c d) x)
    (chartTransition_derivative_bijective c d x hx hd)
    (cov2InChart g c x) (cov2InChart g d (chartTransition c d x))
    (cov2InChart_isUnit_det g hg c x hx)
    (cov2InChart_isUnit_det g hg d _ hy)
    (chartTransition_metric g c d x hx hd)
    (cov3Slice (nablaForm g u d (chartTransition c d x))
      (fderiv ℝ (chartTransition c d) x t))
  simp only [divergenceForm_apply]
  simp_rw [nablaForm_natural g u hg hDg c d x hx hd hDu]
  simpa only [cov3Slice_apply, inverseMetricInChart] using hC

theorem metricTraceInChart_derivative_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (t : FourSpace) :
    fderiv ℝ (metricTraceInChart g u c) x t =
      fderiv ℝ (metricTraceInChart g u d) (chartTransition c d x)
        (fderiv ℝ (chartTransition c d) x t) := by
  have hy := (chartAt FourSpace d).map_source hd
  have hgd := ((hDg d).contDiffAt ((chartAt FourSpace d).open_target.mem_nhds hy)).differentiableAt (by norm_num)
  have hud := cov2InChart_differentiableAt_overlap u c d x hx hd hDu
  have htrace : metricTraceInChart g u c =ᶠ[𝓝 x]
      (fun y => metricTraceInChart g u d (chartTransition c d y)) := by
    filter_upwards [chartTransition_overlap_eventually c d x hx hd] with y hy
    exact metricTraceInChart_natural g u hg c d y hy.1 hy.2
  have hder := htrace.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x (metricTraceInChart_differentiableAt g u hg d _ hy hgd hud)
    ((chartTransition_smooth c d x hx hd).differentiableAt (by decide))] at hder
  exact congrArg (fun D : FourSpace →L[ℝ] ℝ => D t) hder

theorem bianchiForm_natural (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (t : FourSpace) :
    bianchiForm g u c x t = bianchiForm g u d (chartTransition c d x)
      (fderiv ℝ (chartTransition c d) x t) := by
  simp only [bianchiForm_apply,
    divergenceForm_natural g u hg hDg c d x hx hd hDu,
    metricTraceInChart_derivative_natural g u hg hDg c d x hx hd hDu]

theorem bianchi_chart_recovery_of_differentiableAt (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDu : DifferentiableAt ℝ (cov2InChart u c) x) (j : Fin 4) :
    covectorInChart (bianchi g u) c x j = bianchiInChart g u c x j := by
  let p := (chartAt FourSpace c).symm x
  have hp : p ∈ (chartAt FourSpace p).source := mem_chart_source FourSpace p
  have hud := cov2InChart_differentiableAt_overlap u c p x hx hp hDu
  change covectorInChart (covectorFromCoordinates (bianchiInChart g u)) c x j = _
  rw [covectorFromCoordinates_chart_value (bianchiInChart g u) c x hx j]
  change coefficientsToCovector (bianchiInChart g u p (chartTransition c p x))
    (fderiv ℝ (chartTransition c p) x (basisVector j)) = _
  rw [← bianchiForm_eq g u p _ hud,
    ← bianchiForm_natural g u hg hDg c p x hx hp hDu]
  exact bianchiForm_basis g u c x hDu j

theorem bianchi_chart_recovery (g u : RawCov2 M) (hg : IsMetric g)
    (hDg : Cov2ContDiff 1 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hDu : ContDiffAt ℝ 1 (cov2InChart u c) x) (j : Fin 4) :
    covectorInChart (bianchi g u) c x j = bianchiInChart g u c x j :=
  bianchi_chart_recovery_of_differentiableAt g u hg hDg c x hx
    (hDu.differentiableAt (by norm_num)) j

end K24.Global.BianchiNaturality

set_option autoImplicit false
open scoped Manifold ContDiff Matrix.Norms.Elementwise

universe u

theorem K24.Global.bianchi_chart_recovery_c1 :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
      [IsManifold K24.Global.I4 ∞ M],
    ∀ (g u : K24.Global.RawCov2 M), K24.Global.IsMetric g → K24.Global.Cov2ContDiff 1 g →
      ∀ (c : M) (x : K24.Global.FourSpace), x ∈ (chartAt K24.Global.FourSpace c).target →
        ContDiffAt ℝ 1 (K24.Global.cov2InChart u c) x →
        ∀ j : Fin 4, K24.Global.covectorInChart (K24.Global.bianchi g u) c x j =
          K24.Global.bianchiInChart g u c x j := by
  intro M _ _ _ g u hg hDg c x hx hDu j
  exact K24.Global.BianchiNaturality.bianchi_chart_recovery g u hg hDg c x hx hDu j

theorem solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
      [IsManifold K24.Global.I4 ∞ M],
    ∀ (g u : K24.Global.RawCov2 M), K24.Global.IsMetric g → K24.Global.Cov2ContDiff 1 g →
      ∀ (c : M) (x : K24.Global.FourSpace), x ∈ (chartAt K24.Global.FourSpace c).target →
        ContDiffAt ℝ 1 (K24.Global.cov2InChart u c) x →
        ∀ j : Fin 4, K24.Global.covectorInChart (K24.Global.bianchi g u) c x j =
          K24.Global.bianchiInChart g u c x j := K24.Global.bianchi_chart_recovery_c1
