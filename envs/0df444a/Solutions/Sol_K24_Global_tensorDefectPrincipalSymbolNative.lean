-- Prove2me | solution 1 for K24.Global.tensorDefectPrincipalSymbolNative
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:57:23.884738+00:00
-- url     : https://prove2.me/submissions/28951e5d-6c89-474e-b150-ed884899a64f

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

theorem coordDeriv_metricTrace
    (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x)
    (j : Fin 4) :
    coordDeriv (metricTraceInChart g u c) j x =
      ∑ a, ∑ b,
        (coordDeriv (fun y => inverseMetricInChart g c y a b) j x *
           cov2InChart u c x a b +
         inverseMetricInChart g c x a b *
           coordDeriv (fun y => cov2InChart u c y a b) j x) := by
  unfold metricTraceInChart
  rw [coordDeriv_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [coordDeriv_sum]
    · apply Finset.sum_congr rfl
      intro b _
      exact coordDeriv_mul _ _ x (hg a b) (hu a b) j
    · intro b _
      exact (hg a b).mul (hu a b)
  · intro a _
    exact DifferentiableAt.fun_sum fun b _ => (hg a b).mul (hu a b)

theorem matrix_det_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ a b, DifferentiableAt ℝ (fun y => A y a b) x) :
    DifferentiableAt ℝ (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  exact (HasFDerivAt.finsetProd (fun i _ => (hA (σ i) i).hasFDerivAt)).differentiableAt

theorem matrix_inv_coefficient_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ a b, DifferentiableAt ℝ (fun y => A y a b) x)
    (hdet : (A x).det ≠ 0) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => (A y)⁻¹ a b) x := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_apply]
  apply DifferentiableAt.mul
  · exact (matrix_det_differentiableAt A x hA).inv hdet
  · apply matrix_det_differentiableAt
    intro i j
    by_cases hi : i = b
    · subst i
      simp only [Matrix.updateRow_self]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j

theorem cov2_coefficients_differentiableAt (u : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x := by
  have hmatrix : DifferentiableAt ℝ (cov2InChart u c) x :=
    ((hu c).differentiableOn_one x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  exact (differentiableAt_apply b _).comp x ((differentiableAt_apply a _).comp x hmatrix)

theorem metricTraceInChart_differentiableAt (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.fun_sum
  intro b _
  exact (hg a b).mul (hu a b)

end K24.Global.K24OP

namespace K24.Global.K24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

variable [IsManifold I4 ∞ M]

theorem cov2_coefficient_contDiffOn (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (c : M) (i j : Fin 4) :
    ContDiffOn ℝ 2 (fun x => cov2InChart g c x i j) (chartAt FourSpace c).target := by
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) i) j

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

abbrev Bilinear4 := FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)

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

end K24.Global.K24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24NAT

/-- Actual differentiated metric combination with its output index lowered. -/
def koszulEval (Q : FourSpace → K24REG.Bilinear4) (x a b w : FourSpace) : ℝ :=
  (1 / 2 : ℝ) * (fderiv ℝ (fun y => Q y b w) x a +
    fderiv ℝ (fun y => Q y a w) x b - fderiv ℝ (fun y => Q y a b) x w)

/-- The genuine second derivative supplies exactly the inhomogeneous connection term. -/
theorem koszulEval_pullback (F : FourSpace → FourSpace)
    (Q : FourSpace → K24REG.Bilinear4) (x a b w : FourSpace)
    (hF : ContDiffAt ℝ 2 F x) (hQ : DifferentiableAt ℝ Q (F x))
    (hs : ∀ v w, Q (F x) v w = Q (F x) w v) :
    koszulEval (fun y => bilinearPullback (Q (F y)) (fderiv ℝ F y)) x a b w =
      koszulEval Q (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) (fderiv ℝ F x w) +
      Q (F x) (fderiv ℝ (fderiv ℝ F) x a b) (fderiv ℝ F x w) := by
  have hFd := hF.differentiableAt (by norm_num)
  have hJ := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH := hF.isSymmSndFDerivAt (by norm_num)
  unfold koszulEval
  rw [K24REG.fderiv_bilinear_pullback_eval F Q x b w a hFd hJ hQ,
    K24REG.fderiv_bilinear_pullback_eval F Q x a w b hFd hJ hQ,
    K24REG.fderiv_bilinear_pullback_eval F Q x a b w hFd hJ hQ,
    K24REG.fderiv_bilinear_eval Q (F x) _ _ _ hQ,
    K24REG.fderiv_bilinear_eval Q (F x) _ _ _ hQ,
    K24REG.fderiv_bilinear_eval Q (F x) _ _ _ hQ]
  rw [hH b a, hH w a, hH w b, hs (fderiv ℝ (fderiv ℝ F) x a w)]
  ring

/-- Equality on a neighborhood determines the actual lowered connection expression. -/
theorem koszulEval_congr (Q R : FourSpace → K24REG.Bilinear4) (x a b w : FourSpace)
    (hQR : Q =ᶠ[𝓝 x] R) : koszulEval Q x a b w = koszulEval R x a b w := by
  unfold koszulEval
  have h (v w : FourSpace) : (fun y => Q y v w) =ᶠ[𝓝 x] (fun y => R y v w) :=
    hQR.mono fun y hy => congrArg (fun B => B v w) hy
  rw [(h b w).fderiv_eq, (h a w).fderiv_eq, (h a b).fderiv_eq]


end K24.Global.K24NAT


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24NAT

abbrev Trilinear4 := FourSpace →L[ℝ] K24REG.Bilinear4
abbrev Connection4 := FourSpace →L[ℝ] FourSpace →L[ℝ] FourSpace

def koszulTrilinear (Q : FourSpace → K24REG.Bilinear4) (x : FourSpace) : Trilinear4 :=
  (1 / 2 : ℝ) • (fderiv ℝ Q x + (fderiv ℝ Q x).flip -
    (ContinuousLinearMap.flipₗᵢ ℝ FourSpace FourSpace ℝ).toContinuousLinearMap.comp
      (fderiv ℝ Q x).flip)

theorem koszulTrilinear_apply (Q : FourSpace → K24REG.Bilinear4) (x a b w : FourSpace)
    (hQ : DifferentiableAt ℝ Q x) :
    koszulTrilinear Q x a b w = koszulEval Q x a b w := by
  unfold koszulEval
  rw [K24REG.fderiv_bilinear_eval Q x b w a hQ,
    K24REG.fderiv_bilinear_eval Q x a w b hQ,
    K24REG.fderiv_bilinear_eval Q x a b w hQ]
  rfl

theorem trilinear_ext_basis (T S : Trilinear4)
    (h : ∀ i j k, T (basisVector i) (basisVector j) (basisVector k) =
      S (basisVector i) (basisVector j) (basisVector k)) : T = S := by
  ext a b w
  conv_lhs => rw [← sum_basisVector a, ← sum_basisVector b, ← sum_basisVector w]
  conv_rhs => rw [← sum_basisVector a, ← sum_basisVector b, ← sum_basisVector w]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, h]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- The native Christoffel coefficients evaluated on two arbitrary coordinate vectors. -/
def connectionBilinear (g : RawCov2 M) (c : M) (x : FourSpace) : Connection4 :=
  ∑ i, ∑ j, (coordProj i).smulRight ((coordProj j).smulRight
    (∑ k, christoffelInChart g c x k i j • basisVector k))

theorem connectionBilinear_basis (g : RawCov2 M) (c : M) (x : FourSpace) (i j : Fin 4) :
    connectionBilinear g c x (basisVector i) (basisVector j) =
      ∑ k, christoffelInChart g c x k i j • basisVector k := by
  simp [connectionBilinear, coordProj, basisVector]

def lowerConnection (Q : K24REG.Bilinear4) (G : Connection4) : Trilinear4 :=
  (ContinuousLinearMap.compL ℝ FourSpace FourSpace (FourSpace →L[ℝ] ℝ) Q).comp G

@[simp] theorem lowerConnection_apply (Q : K24REG.Bilinear4) (G : Connection4)
    (a b w : FourSpace) : lowerConnection Q G a b w = Q (G a b) w := rfl

/-- Lowering the actual native Christoffel symbols yields the actual metric derivative. -/
theorem lowerConnection_eq_koszul (g : RawCov2 M) (hs : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (hdet : (cov2InChart g c x).det ≠ 0)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x) :
    lowerConnection (matrixToBilinear (cov2InChart g c x)) (connectionBilinear g c x) =
      koszulTrilinear (fun y => matrixToBilinear (cov2InChart g c y)) x := by
  have hQ := K24REG.matrixToBilinear_differentiableAt _ x hg
  apply trilinear_ext_basis
  intro i j l
  rw [lowerConnection_apply, connectionBilinear_basis, koszulTrilinear_apply _ _ _ _ _ hQ]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, K24REG.matrixToBilinear_basis]
  rw [K24OPConnection.christoffel_lower g hs c x hdet i j l]
  simp only [koszulEval, K24REG.matrixToBilinear_basis, coordDeriv]


end K24.Global.K24NAT


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24NAT
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

/-- Chart coefficients are the actual bilinear form pulled back by the inverse differential. -/
theorem cov2InChart_bilinear (g : RawCov2 M) (c : M) (x : FourSpace) :
    matrixToBilinear (cov2InChart g c x) =
      bilinearPullback (g ((chartAt FourSpace c).symm x))
        (mfderiv I4 I4 (chartAt FourSpace c).symm x) := by
  let p := (chartAt FourSpace c).symm x
  let di : FourSpace →L[ℝ] TangentSpace I4 p := mfderiv I4 I4 (chartAt FourSpace c).symm x
  exact matrixToBilinear_recover (bilinearPullback (g p) di)

theorem metric_chart_bilinear_pos (g : RawCov2 M) (hm : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (v : FourSpace) (hv : v ≠ 0) :
    0 < matrixToBilinear (cov2InChart g c x) v v := by
  let p := (chartAt FourSpace c).symm x
  let di := mfderiv I4 I4 (chartAt FourSpace c).symm x
  have hleft : Function.LeftInverse
      (mfderiv I4 I4 (chartAt FourSpace c) p) di := by
    intro w
    exact congrArg (fun D => D w) ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hx)
  have hdi : di v ≠ 0 := by
    simpa only [map_zero] using hleft.injective.ne hv
  have hp := hm.2 p (di v) hdi
  rw [cov2InChart_bilinear]
  exact hp

theorem metric_chart_bilinear_separates (g : RawCov2 M) (hm : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (v z : FourSpace)
    (he : ∀ w, matrixToBilinear (cov2InChart g c x) v w =
      matrixToBilinear (cov2InChart g c x) z w) : v = z := by
  by_contra hne
  have hp := metric_chart_bilinear_pos g hm c x hx (v - z) (sub_ne_zero.mpr hne)
  have heq : matrixToBilinear (cov2InChart g c x) (v - z) (v - z) = 0 := by
    simp only [map_sub, ContinuousLinearMap.sub_apply, he, sub_self]
  linarith

theorem chartTransition_fderiv_surjective (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    Function.Surjective
      (fderiv ℝ (fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)) x) := by
  rw [← K24REG.chartTransitionDerivative_eq_fderiv c d x hx hd]
  exact ((mdifferentiable_chart (I := I4) d).mfderiv_surjective hd).comp
    ((mdifferentiable_chart (I := I4) c).symm.mfderiv_surjective hx)

/-- The actual native Christoffel connection obeys the genuine chart transformation law. -/
theorem connectionBilinear_transition (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c d : M) (x a b : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
    fderiv ℝ F x (connectionBilinear g c x a b) =
      connectionBilinear g d (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) +
        fderiv ℝ (fderiv ℝ F) x a b := by
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
  let Qc : FourSpace → K24REG.Bilinear4 := fun y => matrixToBilinear (cov2InChart g c y)
  let Qd : FourSpace → K24REG.Bilinear4 := fun y => matrixToBilinear (cov2InChart g d y)
  have hdx : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hgc := K24OP.cov2_coefficients_differentiableAt g hg c x hx
  have hgd := K24OP.cov2_coefficients_differentiableAt g hg d (F x) hdx
  have hQc : DifferentiableAt ℝ Qc x := K24REG.matrixToBilinear_differentiableAt _ x hgc
  have hQd : DifferentiableAt ℝ Qd (F x) := K24REG.matrixToBilinear_differentiableAt _ (F x) hgd
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source :=
    ((chartAt FourSpace c).symm.trans (chartAt FourSpace d)).open_source.mem_nhds ⟨hx, hd⟩
  have hrel : Qc =ᶠ[𝓝 x] (fun y => bilinearPullback (Qd (F y)) (fderiv ℝ F y)) := by
    filter_upwards [hnear] with y hy
    exact (K24REG.cov2InChart_transition g c d y hy.2).trans
      (congrArg (bilinearPullback (Qd (F y)))
        (K24REG.chartTransitionDerivative_eq_fderiv c d y hy.1 hy.2))
  have hlc (u v w : FourSpace) :
      Qc x (connectionBilinear g c x u v) w = koszulEval Qc x u v w := by
    have h := congrArg (fun T : Trilinear4 => T u v w)
      (lowerConnection_eq_koszul g hm.1 c x
        (K24OPConnection.metric_chart_det_ne_zero g hm c x hx) hgc)
    rw [koszulTrilinear_apply _ _ _ _ _ hQc] at h
    exact h
  have hld (u v w : FourSpace) :
      Qd (F x) (connectionBilinear g d (F x) u v) w = koszulEval Qd (F x) u v w := by
    have h := congrArg (fun T : Trilinear4 => T u v w)
      (lowerConnection_eq_koszul g hm.1 d (F x)
        (K24OPConnection.metric_chart_det_ne_zero g hm d (F x) hdx) hgd)
    rw [koszulTrilinear_apply _ _ _ _ _ hQd] at h
    exact h
  have hs : ∀ v w, Qd (F x) v w = Qd (F x) w v := by
    intro v w
    dsimp only [Qd]
    rw [cov2InChart_bilinear]
    exact hm.1 _ _ _
  apply metric_chart_bilinear_separates g hm d (F x) hdx
  intro w
  obtain ⟨w, rfl⟩ := chartTransition_fderiv_surjective c d x hx hd w
  change Qd (F x) (fderiv ℝ F x (connectionBilinear g c x a b)) (fderiv ℝ F x w) =
    Qd (F x) (connectionBilinear g d (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) +
      fderiv ℝ (fderiv ℝ F) x a b) (fderiv ℝ F x w)
  calc
    _ = Qc x (connectionBilinear g c x a b) w :=
      (congrArg (fun B : K24REG.Bilinear4 => B (connectionBilinear g c x a b) w)
        hrel.eq_of_nhds).symm
    _ = koszulEval Qc x a b w := hlc a b w
    _ = koszulEval (fun y => bilinearPullback (Qd (F y)) (fderiv ℝ F y)) x a b w :=
      koszulEval_congr _ _ x a b w hrel
    _ = koszulEval Qd (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) (fderiv ℝ F x w) +
        Qd (F x) (fderiv ℝ (fderiv ℝ F) x a b) (fderiv ℝ F x w) :=
      koszulEval_pullback F Qd x a b w (K24REG.chartTransition_contDiffAt c d x hx hd) hQd hs
    _ = _ := by rw [map_add, ContinuousLinearMap.add_apply, hld]


end K24.Global.K24NAT

namespace K24.Global.K24NAT

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

variable [IsManifold I4 ∞ M]

abbrev Covector4 := FourSpace →L[ℝ] ℝ

@[simp] theorem coefficientsToCovector_basis (a : Fin 4 → ℝ) (i : Fin 4) :
    coefficientsToCovector a (basisVector i) = a i := by
  simp [coefficientsToCovector, coordProj, basisVector]

theorem coefficientsToCovector_differentiableAt (a : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x) :
    DifferentiableAt ℝ (fun y => coefficientsToCovector (a y)) x := by
  unfold coefficientsToCovector
  exact DifferentiableAt.fun_sum fun i _ => (ha i).smul_const (coordProj i)

theorem fderiv_covector_eval (U : FourSpace → Covector4) (x a v : FourSpace)
    (hU : DifferentiableAt ℝ U x) :
    fderiv ℝ (fun y => U y v) x a = fderiv ℝ U x a v := by
  rw [(hU.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
  simp

def covariantCovector (U : FourSpace → Covector4) (G : Connection4)
    (x : FourSpace) : K24REG.Bilinear4 :=
  fderiv ℝ U x - (ContinuousLinearMap.compL ℝ FourSpace FourSpace ℝ (U x)).comp G

@[simp] theorem covariantCovector_apply (U : FourSpace → Covector4) (G : Connection4)
    (x a b : FourSpace) :
    covariantCovector U G x a b = fderiv ℝ U x a b - U x (G a b) := rfl

theorem fderiv_covector_pullback_eval (F : FourSpace → FourSpace)
    (U : FourSpace → Covector4) (x a b : FourSpace)
    (hF : ContDiffAt ℝ 2 F x) (hU : DifferentiableAt ℝ U (F x)) :
    fderiv ℝ (fun y => U (F y) (fderiv ℝ F y b)) x a =
      fderiv ℝ U (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) +
        U (F x) (fderiv ℝ (fderiv ℝ F) x a b) := by
  have hFd := hF.differentiableAt (by norm_num)
  have hJ := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hUF : HasFDerivAt (fun y => U (F y))
      ((fderiv ℝ U (F x)).comp (fderiv ℝ F x)) x := by
    simpa only [Function.comp_def] using
      (HasFDerivAt.comp x (f := F) (g := U) hU.hasFDerivAt hFd.hasFDerivAt)
  have h := hUF.clm_apply (hJ.hasFDerivAt.clm_apply (hasFDerivAt_const b x))
  rw [h.fderiv]
  simp [add_comm]

theorem covectorInChart_transition (eta : RawCovector M) (c d : M) (x : FourSpace)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    coefficientsToCovector (covectorInChart eta c x) =
      (coefficientsToCovector (covectorInChart eta d
        (chartAt FourSpace d ((chartAt FourSpace c).symm x)))).comp
          (K24REG.chartTransitionDerivative c d x) := by
  let p := (chartAt FourSpace c).symm x
  let dc : FourSpace →L[ℝ] TangentSpace I4 p := mfderiv I4 I4 (chartAt FourSpace c).symm x
  have hr := covector_chart_recovery eta d p hd
  have hrec := coefficientsToCovector_recover ((eta p).comp dc)
  change coefficientsToCovector (fun i => eta p (dc (basisVector i))) = _
  erw [hrec]
  ext v
  exact (congrArg (fun B => B (dc v)) hr).symm

end K24.Global.K24NAT

namespace K24.Global.K24NAT

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def covariantTensor (U : FourSpace → K24REG.Bilinear4) (G : Connection4)
    (x : FourSpace) : Trilinear4 :=
  fderiv ℝ U x - lowerConnection (U x) G -
    (ContinuousLinearMap.flipₗᵢ ℝ FourSpace FourSpace ℝ).toContinuousLinearMap.comp
      (lowerConnection (U x).flip G)

@[simp] theorem covariantTensor_apply (U : FourSpace → K24REG.Bilinear4) (G : Connection4)
    (x a b w : FourSpace) :
    covariantTensor U G x a b w = fderiv ℝ U x a b w - U x (G a b) w - U x b (G a w) := rfl

end K24.Global.K24NAT


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24NAT

def linearMatrix (J : FourSpace →L[ℝ] FourSpace) : Mat4 := fun i j => J (basisVector j) i

theorem bilinear_apply_eq_sum (T : K24REG.Bilinear4) (v w : FourSpace) :
    T v w = ∑ i, ∑ j, v i * w j * T (basisVector i) (basisVector j) := by
  rw [← matrixToBilinear_recover T]
  simp [matrixToBilinear, coordProj, basisVector, mul_assoc, mul_comm, mul_left_comm]

theorem four_sum_comm (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ p, ∑ q, F a b p q) = ∑ p, ∑ q, ∑ a, ∑ b, F a b p q := by
  have h := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun ab pq : Fin 4 × Fin 4 => F ab.1 ab.2 pq.1 pq.2)
  simpa only [Fintype.sum_prod_type] using h

/-- The inverse metric contracts transformed covariant indices invariantly. -/
theorem inverse_pullback (P Q J : Mat4) (hP : P.det ≠ 0)
    (hrel : P = J.transpose * Q * J) : J * P⁻¹ * J.transpose = Q⁻¹ := by
  have hJ : J.det ≠ 0 := by
    intro h
    apply hP
    rw [hrel, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h]
    ring
  have hJt : J.transpose.det ≠ 0 := by simpa only [Matrix.det_transpose] using hJ
  calc
    _ = (J * J⁻¹) * Q⁻¹ * (J.transpose⁻¹ * J.transpose) := by
      rw [hrel, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    _ = Q⁻¹ := by
      rw [Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.mpr hJ),
        Matrix.nonsing_inv_mul J.transpose (isUnit_iff_ne_zero.mpr hJt)]
      simp

theorem inverse_pullback_coefficients (P Q J : Mat4) (hP : P.det ≠ 0)
    (hrel : P = J.transpose * Q * J) (p q : Fin 4) :
    (∑ a, ∑ b, P⁻¹ a b * J p a * J q b) = Q⁻¹ p q := by
  have h := congrArg (fun A : Mat4 => A p q) (inverse_pullback P Q J hP hrel)
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Bilinear contraction invariance, derived from genuine coordinate matrix multiplication. -/
theorem metric_contraction_pullback (P Q : Mat4) (J : FourSpace →L[ℝ] FourSpace)
    (hP : P.det ≠ 0) (hrel : P = (linearMatrix J).transpose * Q * linearMatrix J)
    (T : K24REG.Bilinear4) :
    (∑ a, ∑ b, P⁻¹ a b * T (J (basisVector a)) (J (basisVector b))) =
      ∑ p, ∑ q, Q⁻¹ p q * T (basisVector p) (basisVector q) := by
  simp_rw [bilinear_apply_eq_sum T (J _) (J _)]
  simp only [Finset.mul_sum]
  rw [four_sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  calc
    _ = (∑ a, ∑ b, P⁻¹ a b * linearMatrix J p a * linearMatrix J q b) *
        T (basisVector p) (basisVector q) := by
      simp only [Finset.sum_mul, linearMatrix, mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by rw [inverse_pullback_coefficients P Q (linearMatrix J) hP hrel]

/-- The matrix of a genuine bilinear pullback is the Jacobian congruence. -/
theorem matrix_bilinearPullback (Q : Mat4) (J : FourSpace →L[ℝ] FourSpace) :
    (fun i j => bilinearPullback (matrixToBilinear Q) J (basisVector i) (basisVector j)) =
      (linearMatrix J).transpose * Q * linearMatrix J := by
  ext i j
  simp only [bilinearPullback_apply, matrixToBilinear, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    coordProj, PiLp.proj_apply, Matrix.mul_apply, Matrix.transpose_apply,
    linearMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_left_comm, mul_comm]


end K24.Global.K24NAT

namespace K24.Global.K24NAT

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

variable [IsManifold I4 ∞ M]

theorem cov2InChart_matrix_transition (u : RawCov2 M) (c d : M) (x : FourSpace)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    cov2InChart u c x =
      (linearMatrix (K24REG.chartTransitionDerivative c d x)).transpose *
        cov2InChart u d (chartAt FourSpace d ((chartAt FourSpace c).symm x)) *
          linearMatrix (K24REG.chartTransitionDerivative c d x) := by
  rw [← matrix_bilinearPullback]
  ext i j
  rw [← K24REG.cov2InChart_transition u c d x hd, K24REG.matrixToBilinear_basis]

theorem metricTraceInChart_transition (g u : RawCov2 M) (hm : IsMetric g)
    (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    metricTraceInChart g u c x =
      metricTraceInChart g u d (chartAt FourSpace d ((chartAt FourSpace c).symm x)) := by
  let J := K24REG.chartTransitionDerivative c d x
  let y := chartAt FourSpace d ((chartAt FourSpace c).symm x)
  have h := metric_contraction_pullback (cov2InChart g c x) (cov2InChart g d y) J
    (K24OPConnection.metric_chart_det_ne_zero g hm c x hx)
    (cov2InChart_matrix_transition g c d x hd) (matrixToBilinear (cov2InChart u d y))
  have hu := K24REG.cov2InChart_transition u c d x hd
  have he (a b : Fin 4) :
      matrixToBilinear (cov2InChart u d y) (J (basisVector a)) (J (basisVector b)) =
        cov2InChart u c x a b := by
    have h := congrArg (fun B : K24REG.Bilinear4 => B (basisVector a) (basisVector b)) hu
    simpa only [K24REG.matrixToBilinear_basis, bilinearPullback_apply] using h.symm
  simpa only [he, K24REG.matrixToBilinear_basis, metricTraceInChart, inverseMetricInChart] using h

end K24.Global.K24NAT

namespace K24.Global.K24NAT

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

variable [IsManifold I4 ∞ M]

def trilinearLast (T : Trilinear4) (v : FourSpace) : K24REG.Bilinear4 :=
  ((ContinuousLinearMap.flipₗᵢ ℝ FourSpace FourSpace ℝ).toContinuousLinearMap.comp T).flip v

@[simp] theorem trilinearLast_apply (T : Trilinear4) (v a b : FourSpace) :
    trilinearLast T v a b = T a b v := rfl

def bianchiCovectorInChart (g u : RawCov2 M) (c : M) (x : FourSpace) : Covector4 :=
  -(∑ a, ∑ b, inverseMetricInChart g c x a b •
    covariantTensor (fun y => matrixToBilinear (cov2InChart u c y))
      (connectionBilinear g c x) x (basisVector a) (basisVector b)) +
  (1 / 2 : ℝ) • fderiv ℝ (metricTraceInChart g u c) x

end K24.Global.K24NAT


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24SYM

/-- The actual linear covector represented by the symbol frequency. -/
def frequencyLinear (xi : Fin 4 → ℝ) : FourSpace →L[ℝ] ℝ := coefficientsToCovector xi

def jetPhase (x : FourSpace) (xi : Fin 4 → ℝ) (y : FourSpace) : ℝ :=
  ∑ a : Fin 4, xi a * (y a - x a)

def jetCoefficient (x : FourSpace) (xi : Fin 4 → ℝ) (a : ℝ) (y : FourSpace) : ℝ :=
  (1 / 2 : ℝ) * jetPhase x xi y ^ 2 * a

@[simp] theorem frequencyLinear_basis (xi : Fin 4 → ℝ) (i : Fin 4) :
    frequencyLinear xi (basisVector i) = xi i := by
  simp [frequencyLinear, coefficientsToCovector, coordProj, basisVector]

theorem jetPhase_eq (x : FourSpace) (xi : Fin 4 → ℝ) (y : FourSpace) :
    jetPhase x xi y = frequencyLinear xi y - frequencyLinear xi x := by
  simp [jetPhase, frequencyLinear, coefficientsToCovector, coordProj,
    mul_sub, Finset.sum_sub_distrib]

theorem jetPhase_hasFDerivAt (x : FourSpace) (xi : Fin 4 → ℝ) (y : FourSpace) :
    HasFDerivAt (jetPhase x xi) (frequencyLinear xi) y := by
  have hfun : jetPhase x xi = fun z => frequencyLinear xi z - frequencyLinear xi x :=
    funext (jetPhase_eq x xi)
  rw [hfun]
  exact (frequencyLinear xi).hasFDerivAt.sub_const _

theorem jetCoefficient_hasFDerivAt (x : FourSpace) (xi : Fin 4 → ℝ) (a : ℝ)
    (y : FourSpace) :
    HasFDerivAt (jetCoefficient x xi a) ((jetPhase x xi y * a) • frequencyLinear xi) y := by
  have h := (((jetPhase_hasFDerivAt x xi y).pow 2).const_mul (1 / 2 : ℝ)).mul_const a
  convert h using 1 <;> ext v <;> simp [jetCoefficient] <;> ring

theorem coordDeriv_jetCoefficient (x : FourSpace) (xi : Fin 4 → ℝ) (a : ℝ)
    (y : FourSpace) (i : Fin 4) :
    coordDeriv (jetCoefficient x xi a) i y = jetPhase x xi y * xi i * a := by
  unfold coordDeriv
  rw [(jetCoefficient_hasFDerivAt x xi a y).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, frequencyLinear_basis]
  ring

theorem coordDeriv_coordDeriv_jetCoefficient (x : FourSpace) (xi : Fin 4 → ℝ)
    (a : ℝ) (y : FourSpace) (i j : Fin 4) :
    coordDeriv (fun z => coordDeriv (jetCoefficient x xi a) j z) i y = xi i * xi j * a := by
  simp_rw [coordDeriv_jetCoefficient]
  unfold coordDeriv
  rw [(((jetPhase_hasFDerivAt x xi y).mul_const (xi j)).mul_const a).fderiv]
  simp [mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem jetPhase_center (x : FourSpace) (xi : Fin 4 → ℝ) : jetPhase x xi x = 0 := by
  simp [jetPhase]

@[simp] theorem jetCoefficient_center (x : FourSpace) (xi : Fin 4 → ℝ) (a : ℝ) :
    jetCoefficient x xi a x = 0 := by simp [jetCoefficient]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

/-- These are the actual coefficients of the globally defined quadratic test tensor. -/
theorem quadraticJetTensor_coefficients (c : M) (x y : FourSpace)
    (hy : y ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (a : Mat4) :
    cov2InChart (quadraticJetTensor c x xi a) c y =
      fun i j => jetCoefficient x xi (a i j) y := by
  exact K24REG.cov2InChart_fixed_reconstruction c
    (fun z i j => jetCoefficient x xi (a i j) z) y hy

theorem quadraticJetTensor_first_derivative (c : M) (x y : FourSpace)
    (hy : y ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (a : Mat4)
    (r i j : Fin 4) :
    coordDeriv (fun z => cov2InChart (quadraticJetTensor c x xi a) c z i j) r y =
      jetPhase x xi y * xi r * a i j := by
  have heq : (fun z => cov2InChart (quadraticJetTensor c x xi a) c z i j) =ᶠ[𝓝 y]
      jetCoefficient x xi (a i j) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hy] with z hz
    exact congrArg (fun A => A i j) (quadraticJetTensor_coefficients c x z hz xi a)
  unfold coordDeriv
  rw [heq.fderiv_eq]
  exact coordDeriv_jetCoefficient x xi (a i j) y r

/-- The second jet is the actual tensor xi ⊗ xi ⊗ a, with no symmetry restriction on a. -/
theorem quadraticJetTensor_second_derivative (c : M) (x y : FourSpace)
    (hy : y ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (a : Mat4)
    (s r i j : Fin 4) :
    coordDeriv (fun w => coordDeriv
      (fun z => cov2InChart (quadraticJetTensor c x xi a) c z i j) r w) s y =
      xi s * xi r * a i j := by
  have heq : (fun w => coordDeriv
      (fun z => cov2InChart (quadraticJetTensor c x xi a) c z i j) r w) =ᶠ[𝓝 y]
      (fun w => coordDeriv (jetCoefficient x xi (a i j)) r w) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hy] with w hw
    rw [quadraticJetTensor_first_derivative c x w hw xi a, coordDeriv_jetCoefficient]
  unfold coordDeriv at heq ⊢
  rw [heq.fderiv_eq]
  exact coordDeriv_coordDeriv_jetCoefficient x xi (a i j) y s r

/-- Value and first derivative vanish for the genuine native tensor at the test point. -/
theorem quadraticJetTensor_zero_first_jet (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (a : Mat4) :
    cov2InChart (quadraticJetTensor c x xi a) c x = 0 ∧
    ∀ r i j, coordDeriv
      (fun y => cov2InChart (quadraticJetTensor c x xi a) c y i j) r x = 0 := by
  constructor
  · ext i j
    rw [quadraticJetTensor_coefficients c x x hx xi a]
    simp
  · intro r i j
    rw [quadraticJetTensor_first_derivative c x x hx xi a]
    simp


end K24.Global.K24SYM


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24SYM

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

def bianchiSingleSymbol (g : RawCov2 M) (c : M) (y : FourSpace)
    (xi : Fin 4 → ℝ) (A : Mat4) (j : Fin 4) : ℝ :=
  -(∑ a, ∑ b, inverseMetricInChart g c y a b * xi a * A b j) +
    (1 / 2 : ℝ) * ∑ a, ∑ b, inverseMetricInChart g c y a b * xi j * A a b

def bianchiJetLower (g : RawCov2 M) (c : M) (y : FourSpace) (A : Mat4) (j : Fin 4) : ℝ :=
  (∑ a, ∑ b, ∑ p, inverseMetricInChart g c y a b * christoffelInChart g c y p a b * A p j) +
  (∑ a, ∑ b, ∑ p, inverseMetricInChart g c y a b * christoffelInChart g c y p a j * A b p) +
  (1 / 2 : ℝ) * ∑ a, ∑ b, coordDeriv (fun z => inverseMetricInChart g c z a b) j y * A a b

theorem jetCoefficient_eq_factor (x : FourSpace) (xi : Fin 4 → ℝ) (a : ℝ) (y : FourSpace) :
    jetCoefficient x xi a y = jetCoefficient x xi 1 y * a := by simp [jetCoefficient]

/-- Exact local Bianchi evaluation of the actual quadratic tensor. -/
theorem bianchi_quadraticJet_decomposition (g : RawCov2 M) (c : M) (x y : FourSpace)
    (hy : y ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (A : Mat4) (j : Fin 4)
    (hI : ∀ a b, DifferentiableAt ℝ (fun z => inverseMetricInChart g c z a b) y) :
    bianchiInChart g (quadraticJetTensor c x xi A) c y j =
      jetPhase x xi y * bianchiSingleSymbol g c y xi A j +
      jetCoefficient x xi 1 y * bianchiJetLower g c y A j := by
  have hQ : ∀ a b, DifferentiableAt ℝ
      (fun z => cov2InChart (quadraticJetTensor c x xi A) c z a b) y := by
    intro a b
    apply (jetCoefficient_hasFDerivAt x xi (A a b) y).differentiableAt.congr_of_eventuallyEq
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hy] with z hz
    exact congrArg (fun B => B a b) (quadraticJetTensor_coefficients c x z hz xi A)
  unfold bianchiInChart
  rw [K24OP.coordDeriv_metricTrace g (quadraticJetTensor c x xi A) c y hI hQ]
  simp only [nablaTensorInChart]
  simp_rw [quadraticJetTensor_first_derivative c x y hy xi A]
  rw [quadraticJetTensor_coefficients c x y hy xi A]
  simp only [jetCoefficient, mul_one]
  unfold bianchiSingleSymbol bianchiJetLower
  simp only [mul_add, mul_sub, mul_neg, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ring

/-- For genuine differentiable coefficients, only the first-order factor survives. -/
theorem derivative_jet_decomposition (x : FourSpace) (xi : Fin 4 → ℝ)
    (S L : FourSpace → ℝ) (hS : DifferentiableAt ℝ S x) (hL : DifferentiableAt ℝ L x)
    (i : Fin 4) :
    coordDeriv (fun y => jetPhase x xi y * S y + jetCoefficient x xi 1 y * L y) i x =
      xi i * S x := by
  have h := ((jetPhase_hasFDerivAt x xi x).mul hS.hasFDerivAt).add
    ((jetCoefficient_hasFDerivAt x xi 1 x).mul hL.hasFDerivAt)
  change HasFDerivAt (fun y => jetPhase x xi y * S y + jetCoefficient x xi 1 y * L y) _ x at h
  unfold coordDeriv
  rw [h.fderiv]
  simp [mul_comm]

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

theorem bianchiSingleSymbol_differentiableAt (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (A : Mat4) (j : Fin 4) :
    DifferentiableAt ℝ (fun y => bianchiSingleSymbol g c y xi A j) x := by
  have hI : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x :=
    fun a b => (metric_inverse_coefficient_C2 g hm hg c x hx a b).differentiableAt (by norm_num)
  apply DifferentiableAt.add
  · apply DifferentiableAt.neg
    exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      ((hI a b).mul_const (xi a)).mul_const (A b j)
  · apply DifferentiableAt.const_mul
    exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      ((hI a b).mul_const (xi j)).mul_const (A a b)

theorem bianchiJetLower_differentiableAt (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (A : Mat4) (j : Fin 4) :
    DifferentiableAt ℝ (fun y => bianchiJetLower g c y A j) x := by
  have hI : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x :=
    fun a b => (metric_inverse_coefficient_C2 g hm hg c x hx a b).differentiableAt (by norm_num)
  have hG : ∀ p a b, DifferentiableAt ℝ (fun y => christoffelInChart g c y p a b) x :=
    fun p a b => (christoffel_contDiffAt g hm hg c x hx p a b).differentiableAt (by norm_num)
  apply DifferentiableAt.add
  · apply DifferentiableAt.add
    · exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
        DifferentiableAt.fun_sum fun p _ => ((hI a b).mul (hG p a b)).mul_const (A p j)
    · exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
        DifferentiableAt.fun_sum fun p _ => ((hI a b).mul (hG p a j)).mul_const (A b p)
  · apply DifferentiableAt.const_mul
    exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
      ((coordDeriv_contDiffAt (metric_inverse_coefficient_C2 g hm hg c x hx a b) j).differentiableAt (by norm_num)).mul_const (A a b)

/-- The actual local Bianchi expression has a genuine derivative on the quadratic test. -/
theorem bianchi_quadraticJet_differentiableAt (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (A : Mat4) (j : Fin 4) :
    DifferentiableAt ℝ (fun y => bianchiInChart g (quadraticJetTensor c x xi A) c y j) x := by
  have hS := bianchiSingleSymbol_differentiableAt g hm hg c x hx xi A j
  have hL := bianchiJetLower_differentiableAt g hm hg c x hx A j
  apply (((jetPhase_hasFDerivAt x xi x).differentiableAt.mul hS).add
    ((jetCoefficient_hasFDerivAt x xi 1 x).differentiableAt.mul hL)).congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
  exact bianchi_quadraticJet_decomposition g c x y hy xi A j
    (fun a b => (metric_inverse_coefficient_C2 g hm hg c y hy a b).differentiableAt (by norm_num))

/-- All lower coefficient derivatives vanish in the actual Bianchi first jet. -/
theorem bianchi_quadraticJet_derivative (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (A : Mat4) (i j : Fin 4) :
    coordDeriv (fun y => bianchiInChart g (quadraticJetTensor c x xi A) c y j) i x =
      xi i * bianchiSingleSymbol g c x xi A j := by
  have heq : (fun y => bianchiInChart g (quadraticJetTensor c x xi A) c y j) =ᶠ[𝓝 x]
      (fun y => jetPhase x xi y * bianchiSingleSymbol g c y xi A j +
        jetCoefficient x xi 1 y * bianchiJetLower g c y A j) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    exact bianchi_quadraticJet_decomposition g c x y hy xi A j
      (fun a b => (metric_inverse_coefficient_C2 g hm hg c y hy a b).differentiableAt (by norm_num))
  unfold coordDeriv
  rw [heq.fderiv_eq]
  exact derivative_jet_decomposition x xi _ _
    (bianchiSingleSymbol_differentiableAt g hm hg c x hx xi A j)
    (bianchiJetLower_differentiableAt g hm hg c x hx A j) i

theorem bianchi_quadraticJet_center (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (A : Mat4) (j : Fin 4) :
    bianchiInChart g (quadraticJetTensor c x xi A) c x j = 0 := by
  rw [bianchi_quadraticJet_decomposition g c x x hx xi A j
    (fun a b => (metric_inverse_coefficient_C2 g hm hg c x hx a b).differentiableAt (by norm_num))]
  simp

theorem bianchiSingleSymbol_sub (ghat z : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (A : Mat4) (j : Fin 4) :
    bianchiSingleSymbol ghat c x xi A j - bianchiSingleSymbol z c x xi A j =
      bianchiDifferenceSymbol ghat z c x xi A j := by
  simp only [bianchiSingleSymbol, bianchiDifferenceSymbol, inverseDifferenceInChart,
    Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring


end K24.Global.K24SYM


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24LOC
open K24NAT

theorem differentiableAt_bilinearPullback (U : FourSpace → K24REG.Bilinear4)
    (J : FourSpace → FourSpace →L[ℝ] FourSpace) (x : FourSpace)
    (hU : DifferentiableAt ℝ U x) (hJ : DifferentiableAt ℝ J x) :
    DifferentiableAt ℝ (fun y => bilinearPullback (U y) (J y)) x := by
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ FourSpace FourSpace ℝ).toContinuousLinearMap
  have h1 := flipL.differentiableAt.comp x (hU.clm_comp hJ)
  have h2 := h1.clm_comp hJ
  have h3 := flipL.differentiableAt.comp x h2
  have heq : (fun y => bilinearPullback (U y) (J y)) =
      (fun y => (((U y).comp (J y)).flip.comp (J y)).flip) := by
    funext y
    ext a b
    rfl
  rw [heq]
  exact h3

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

/-- Actual covector differentiability at a point transfers through a genuine chart transition. -/
theorem covector_differentiableAt_change (eta : RawCovector M) (c d p : M)
    (hc : p ∈ (chartAt FourSpace c).source) (hd : p ∈ (chartAt FourSpace d).source)
    (hU : DifferentiableAt ℝ (fun y => coefficientsToCovector (covectorInChart eta c y))
      (chartAt FourSpace c p)) :
    DifferentiableAt ℝ (fun y => coefficientsToCovector (covectorInChart eta d y))
      (chartAt FourSpace d p) := by
  let x := chartAt FourSpace d p
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace c ((chartAt FourSpace d).symm y)
  have hx : x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hc' : (chartAt FourSpace d).symm x ∈ (chartAt FourSpace c).source := by
    simpa only [x, (chartAt FourSpace d).left_inv hd] using hc
  have hF : ContDiffAt ℝ 2 F x := K24REG.chartTransition_contDiffAt d c x hx hc'
  have hUc : DifferentiableAt ℝ (fun y => coefficientsToCovector (covectorInChart eta c y)) (F x) := by
    simpa only [F, x, (chartAt FourSpace d).left_inv hd] using hU
  have hJ := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : DifferentiableAt ℝ
      (fun y => (coefficientsToCovector (covectorInChart eta c (F y))).comp (fderiv ℝ F y)) x :=
    (hUc.comp x (hF.differentiableAt (by norm_num))).clm_comp hJ
  apply hcomp.congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace d).target ∧
      (chartAt FourSpace d).symm y ∈ (chartAt FourSpace c).source :=
    ((chartAt FourSpace d).symm.trans (chartAt FourSpace c)).open_source.mem_nhds ⟨hx, hc'⟩
  filter_upwards [hnear] with y hy
  exact (K24NAT.covectorInChart_transition eta d c y hy.2).trans
    (congrArg (fun J => (coefficientsToCovector (covectorInChart eta c (F y))).comp J)
      (K24REG.chartTransitionDerivative_eq_fderiv d c y hy.1 hy.2))

/-- Actual tensor differentiability at a point transfers without global regularity assumptions. -/
theorem cov2_differentiableAt_change (u : RawCov2 M) (c d p : M)
    (hc : p ∈ (chartAt FourSpace c).source) (hd : p ∈ (chartAt FourSpace d).source)
    (hU : DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u c y))
      (chartAt FourSpace c p)) :
    DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u d y))
      (chartAt FourSpace d p) := by
  let x := chartAt FourSpace d p
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace c ((chartAt FourSpace d).symm y)
  have hx : x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hc' : (chartAt FourSpace d).symm x ∈ (chartAt FourSpace c).source := by
    simpa only [x, (chartAt FourSpace d).left_inv hd] using hc
  have hF : ContDiffAt ℝ 2 F x := K24REG.chartTransition_contDiffAt d c x hx hc'
  have hUc : DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u c y)) (F x) := by
    simpa only [F, x, (chartAt FourSpace d).left_inv hd] using hU
  have hJ := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : DifferentiableAt ℝ
      (fun y => bilinearPullback (matrixToBilinear (cov2InChart u c (F y))) (fderiv ℝ F y)) x :=
    differentiableAt_bilinearPullback _ _ x (hUc.comp x (hF.differentiableAt (by norm_num))) hJ
  apply hcomp.congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace d).target ∧
      (chartAt FourSpace d).symm y ∈ (chartAt FourSpace c).source :=
    ((chartAt FourSpace d).symm.trans (chartAt FourSpace c)).open_source.mem_nhds ⟨hx, hc'⟩
  filter_upwards [hnear] with y hy
  exact (K24REG.cov2InChart_transition u d c y hy.2).trans
    (congrArg (bilinearPullback (matrixToBilinear (cov2InChart u c (F y))))
      (K24REG.chartTransitionDerivative_eq_fderiv d c y hy.1 hy.2))


end K24.Global.K24LOC


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24LOC
open K24NAT
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

def CovectorDifferentiableAt (eta : RawCovector M) (p : M) : Prop :=
  ∀ c : M, p ∈ (chartAt FourSpace c).source →
    DifferentiableAt ℝ (fun y => coefficientsToCovector (covectorInChart eta c y))
      (chartAt FourSpace c p)

def Cov2DifferentiableAt (u : RawCov2 M) (p : M) : Prop :=
  ∀ c : M, p ∈ (chartAt FourSpace c).source →
    DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u c y))
      (chartAt FourSpace c p)

theorem covector_at_this_chart (eta : RawCovector M) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hU : CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x)) :
    DifferentiableAt ℝ (fun y => coefficientsToCovector (covectorInChart eta c y)) x := by
  simpa only [(chartAt FourSpace c).right_inv hx] using
    hU c ((chartAt FourSpace c).map_target hx)

theorem cov2_at_this_chart (u : RawCov2 M) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hU : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) :
    DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u c y)) x := by
  simpa only [(chartAt FourSpace c).right_inv hx] using
    hU c ((chartAt FourSpace c).map_target hx)

theorem covector_differentiableAt_of_chart (eta : RawCovector M) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hU : DifferentiableAt ℝ (fun y => coefficientsToCovector (covectorInChart eta c y)) x) :
    CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x) := by
  intro d hd
  apply covector_differentiableAt_change eta c d ((chartAt FourSpace c).symm x)
    ((chartAt FourSpace c).map_target hx) hd
  simpa only [(chartAt FourSpace c).right_inv hx] using hU

theorem cov2_differentiableAt_of_chart (u : RawCov2 M) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hU : DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u c y)) x) :
    Cov2DifferentiableAt u ((chartAt FourSpace c).symm x) := by
  intro d hd
  apply cov2_differentiableAt_change u c d ((chartAt FourSpace c).symm x)
    ((chartAt FourSpace c).map_target hx) hd
  simpa only [(chartAt FourSpace c).right_inv hx] using hU

theorem cov2_coefficient_differentiableAt (u : RawCov2 M) (c : M) (x : FourSpace)
    (hU : DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u c y)) x) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => cov2InChart u c y i j) x := by
  simpa only [K24REG.matrixToBilinear_basis] using
    (hU.clm_apply (differentiableAt_const (basisVector i))).clm_apply
      (differentiableAt_const (basisVector j))

end K24.Global.K24LOC


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
namespace K24.Global.K24LOC
open K24NAT
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

theorem covariantCovector_transition_local (g : RawCov2 M) (eta : RawCovector M)
    (hm : IsMetric g) (hg : Cov2ContDiff 1 g)
    (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (heta : CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x)) :
    let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
    covariantCovector (fun y => coefficientsToCovector (covectorInChart eta c y))
        (connectionBilinear g c x) x =
      bilinearPullback
        (covariantCovector (fun y => coefficientsToCovector (covectorInChart eta d y))
          (connectionBilinear g d (F x)) (F x)) (fderiv ℝ F x) := by
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
  let Uc : FourSpace → Covector4 := fun y => coefficientsToCovector (covectorInChart eta c y)
  let Ud : FourSpace → Covector4 := fun y => coefficientsToCovector (covectorInChart eta d y)
  have hdx : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hUc : DifferentiableAt ℝ Uc x := covector_at_this_chart eta c x hx heta
  have hUd : DifferentiableAt ℝ Ud (F x) := heta d hd
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source :=
    ((chartAt FourSpace c).symm.trans (chartAt FourSpace d)).open_source.mem_nhds ⟨hx, hd⟩
  have hrel : Uc =ᶠ[𝓝 x] (fun y => (Ud (F y)).comp (fderiv ℝ F y)) := by
    filter_upwards [hnear] with y hy
    exact (covectorInChart_transition eta c d y hy.2).trans
      (congrArg (fun J => (Ud (F y)).comp J)
        (K24REG.chartTransitionDerivative_eq_fderiv c d y hy.1 hy.2))
  ext a b
  change covariantCovector Uc (connectionBilinear g c x) x a b =
    covariantCovector Ud (connectionBilinear g d (F x)) (F x)
      (fderiv ℝ F x a) (fderiv ℝ F x b)
  simp only [covariantCovector_apply]
  rw [← fderiv_covector_eval Uc x a b hUc]
  have hr : (fun y => Uc y b) =ᶠ[𝓝 x] (fun y => Ud (F y) (fderiv ℝ F y b)) :=
    hrel.mono fun y hy => congrArg (fun L => L b) hy
  rw [hr.fderiv_eq, fderiv_covector_pullback_eval F Ud x a b
    (K24REG.chartTransition_contDiffAt c d x hx hd) hUd, hrel.eq_of_nhds]
  change _ + _ - Ud (F x) (fderiv ℝ F x (connectionBilinear g c x a b)) = _
  rw [connectionBilinear_transition g hm hg c d x a b hx hd, map_add]
  ring

theorem covariantCovector_basis_local (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (heta : CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x)) (i j : Fin 4) :
    covariantCovector (fun y => coefficientsToCovector (covectorInChart eta c y))
      (connectionBilinear g c x) x (basisVector i) (basisVector j) =
      nablaCovectorInChart g eta c x i j := by
  rw [covariantCovector_apply, ← fderiv_covector_eval _ x _ _
    (covector_at_this_chart eta c x hx heta), connectionBilinear_basis]
  simp only [coefficientsToCovector_basis, map_sum, map_smul, smul_eq_mul]
  rfl

theorem deltaStarInChart_eq_symmetrization_local (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (heta : CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x)) :
    let N := covariantCovector (fun y => coefficientsToCovector (covectorInChart eta c y))
      (connectionBilinear g c x) x
    matrixToBilinear (deltaStarInChart g eta c x) = (1 / 2 : ℝ) • (N + N.flip) := by
  dsimp only
  rw [← matrixToBilinear_recover ((1 / 2 : ℝ) •
    (covariantCovector (fun y => coefficientsToCovector (covectorInChart eta c y))
      (connectionBilinear g c x) x +
    (covariantCovector (fun y => coefficientsToCovector (covectorInChart eta c y))
      (connectionBilinear g c x) x).flip))]
  apply congrArg matrixToBilinear
  ext i j
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, covariantCovector_basis_local g eta c x hx heta]
  rfl

theorem deltaStarInChart_transition_local (g : RawCov2 M) (eta : RawCovector M)
    (hm : IsMetric g) (hg : Cov2ContDiff 1 g)
    (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (heta : CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x)) :
    matrixToBilinear (deltaStarInChart g eta c x) =
      bilinearPullback (matrixToBilinear (deltaStarInChart g eta d
        (chartAt FourSpace d ((chartAt FourSpace c).symm x))))
        (K24REG.chartTransitionDerivative c d x) := by
  have hdx := (chartAt FourSpace d).map_source hd
  have heta_d : CovectorDifferentiableAt eta
      ((chartAt FourSpace d).symm (chartAt FourSpace d ((chartAt FourSpace c).symm x))) := by
    simpa only [(chartAt FourSpace d).left_inv hd] using heta
  rw [deltaStarInChart_eq_symmetrization_local g eta c x hx heta,
    deltaStarInChart_eq_symmetrization_local g eta d _ hdx heta_d,
    K24REG.chartTransitionDerivative_eq_fderiv c d x hx hd]
  rw [covariantCovector_transition_local g eta hm hg c d x hx hd heta]
  ext a b
  simp [bilinearPullback_apply]

/-- Actual native deltaStar recovery needs only differentiability at the chosen point. -/
theorem deltaStar_coefficients_local (g : RawCov2 M) (eta : RawCovector M)
    (hm : IsMetric g) (hg : Cov2ContDiff 1 g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (heta : CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x)) :
    cov2InChart (deltaStar g eta) c x = deltaStarInChart g eta c x := by
  have ht := deltaStarInChart_transition_local g eta hm hg c ((chartAt FourSpace c).symm x)
    x hx (mem_chart_source FourSpace _) heta
  ext i j
  have h := congrArg (fun B : K24REG.Bilinear4 => B (basisVector i) (basisVector j)) ht
  rw [K24REG.matrixToBilinear_basis] at h
  exact h.symm

end K24.Global.K24LOC


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology
namespace K24.Global.K24LOC
open K24NAT
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

theorem covariantTensor_basis_local (g u : RawCov2 M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) (i j k : Fin 4) :
    covariantTensor (fun y => matrixToBilinear (cov2InChart u c y))
      (connectionBilinear g c x) x (basisVector i) (basisVector j) (basisVector k) =
      nablaTensorInChart g u c x i j k := by
  have hU := cov2_at_this_chart u c x hx hu
  rw [covariantTensor_apply, ← K24REG.fderiv_bilinear_eval _ x _ _ _ hU,
    connectionBilinear_basis, connectionBilinear_basis]
  simp only [K24REG.matrixToBilinear_basis, map_sum, map_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

theorem covariantTensor_transition_local (g u : RawCov2 M)
    (hm : IsMetric g) (hg : Cov2ContDiff 1 g)
    (c d : M) (x a b w : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) :
    let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
    covariantTensor (fun y => matrixToBilinear (cov2InChart u c y))
        (connectionBilinear g c x) x a b w =
      covariantTensor (fun y => matrixToBilinear (cov2InChart u d y))
        (connectionBilinear g d (F x)) (F x)
          (fderiv ℝ F x a) (fderiv ℝ F x b) (fderiv ℝ F x w) := by
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
  let Uc : FourSpace → K24REG.Bilinear4 := fun y => matrixToBilinear (cov2InChart u c y)
  let Ud : FourSpace → K24REG.Bilinear4 := fun y => matrixToBilinear (cov2InChart u d y)
  have hdx : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hUc : DifferentiableAt ℝ Uc x := cov2_at_this_chart u c x hx hu
  have hUd : DifferentiableAt ℝ Ud (F x) := hu d hd
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source :=
    ((chartAt FourSpace c).symm.trans (chartAt FourSpace d)).open_source.mem_nhds ⟨hx, hd⟩
  have hrel : Uc =ᶠ[𝓝 x] (fun y => bilinearPullback (Ud (F y)) (fderiv ℝ F y)) := by
    filter_upwards [hnear] with y hy
    exact (K24REG.cov2InChart_transition u c d y hy.2).trans
      (congrArg (bilinearPullback (Ud (F y)))
        (K24REG.chartTransitionDerivative_eq_fderiv c d y hy.1 hy.2))
  change covariantTensor Uc (connectionBilinear g c x) x a b w =
    covariantTensor Ud (connectionBilinear g d (F x)) (F x)
      (fderiv ℝ F x a) (fderiv ℝ F x b) (fderiv ℝ F x w)
  simp only [covariantTensor_apply]
  rw [← K24REG.fderiv_bilinear_eval Uc x b w a hUc]
  have hr : (fun y => Uc y b w) =ᶠ[𝓝 x]
      (fun y => bilinearPullback (Ud (F y)) (fderiv ℝ F y) b w) :=
    hrel.mono fun y hy => congrArg (fun L => L b w) hy
  have hF := K24REG.chartTransition_contDiffAt c d x hx hd
  rw [hr.fderiv_eq, K24REG.fderiv_bilinear_pullback_eval F Ud x b w a
    (hF.differentiableAt (by norm_num))
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) hUd,
    hrel.eq_of_nhds]
  simp only [bilinearPullback_apply]
  rw [connectionBilinear_transition g hm hg c d x a b hx hd,
    connectionBilinear_transition g hm hg c d x a w hx hd]
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

theorem metricTrace_differentiableAt_local (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hU : DifferentiableAt ℝ (fun y => matrixToBilinear (cov2InChart u c y)) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  apply K24OP.metricTraceInChart_differentiableAt
  · intro a b
    exact K24OP.matrix_inv_coefficient_differentiableAt _ x
      (K24OP.cov2_coefficients_differentiableAt g hg c x hx)
      (K24OPConnection.metric_chart_det_ne_zero g hm c x hx) a b
  · exact cov2_coefficient_differentiableAt u c x hU

theorem metricTrace_fderiv_transition_local (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c d : M) (x v : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) :
    let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
    fderiv ℝ (metricTraceInChart g u c) x v =
      fderiv ℝ (metricTraceInChart g u d) (F x) (fderiv ℝ F x v) := by
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
  have hrel : metricTraceInChart g u c =ᶠ[𝓝 x] (fun y => metricTraceInChart g u d (F y)) := by
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ (chartAt FourSpace c).target ∧
        (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source :=
      ((chartAt FourSpace c).symm.trans (chartAt FourSpace d)).open_source.mem_nhds ⟨hx, hd⟩
    filter_upwards [hnear] with y hy
    exact metricTraceInChart_transition g u hm c d y hy.1 hy.2
  rw [hrel.fderiv_eq, fderiv_fun_comp x
    (metricTrace_differentiableAt_local g u hm hg d (F x) ((chartAt FourSpace d).map_source hd) (hu d hd))
    ((K24REG.chartTransition_contDiffAt c d x hx hd).differentiableAt (by norm_num))]
  rfl

theorem bianchiCovectorInChart_basis_local (g u : RawCov2 M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) (j : Fin 4) :
    bianchiCovectorInChart g u c x (basisVector j) = bianchiInChart g u c x j := by
  simp only [bianchiCovectorInChart, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, covariantTensor_basis_local g u c x hx hu]
  rfl

theorem bianchiInChart_eq_covector_local (g u : RawCov2 M)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) :
    coefficientsToCovector (bianchiInChart g u c x) = bianchiCovectorInChart g u c x := by
  rw [← coefficientsToCovector_recover (bianchiCovectorInChart g u c x)]
  simp only [bianchiCovectorInChart_basis_local g u c x hx hu]

theorem bianchiCovectorInChart_transition_local (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) :
    let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
    bianchiCovectorInChart g u c x = (bianchiCovectorInChart g u d (F x)).comp (fderiv ℝ F x) := by
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
  let J := fderiv ℝ F x
  let Tc := covariantTensor (fun y => matrixToBilinear (cov2InChart u c y))
    (connectionBilinear g c x) x
  let Td := covariantTensor (fun y => matrixToBilinear (cov2InChart u d y))
    (connectionBilinear g d (F x)) (F x)
  have hG : cov2InChart g c x = (linearMatrix J).transpose *
      cov2InChart g d (F x) * linearMatrix J := by
    dsimp only [J, F]
    rw [← K24REG.chartTransitionDerivative_eq_fderiv c d x hx hd]
    exact cov2InChart_matrix_transition g c d x hd
  have hc (v : FourSpace) :
      (∑ a, ∑ b, inverseMetricInChart g c x a b * Tc (basisVector a) (basisVector b) v) =
      ∑ a, ∑ b, inverseMetricInChart g d (F x) a b * Td (basisVector a) (basisVector b) (J v) := by
    calc
      _ = ∑ a, ∑ b, inverseMetricInChart g c x a b * Td (J (basisVector a)) (J (basisVector b)) (J v) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [covariantTensor_transition_local g u hm hg c d x (basisVector a) (basisVector b) v hx hd hu]
      _ = _ := metric_contraction_pullback (cov2InChart g c x) (cov2InChart g d (F x)) J
        (K24OPConnection.metric_chart_det_ne_zero g hm c x hx) hG (trilinearLast Td (J v))
  ext v
  simp only [bianchiCovectorInChart, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hc v, metricTrace_fderiv_transition_local g u hm hg c d x v hx hd hu]

theorem bianchiInChart_transition_local (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) :
    coefficientsToCovector (bianchiInChart g u c x) =
      (coefficientsToCovector (bianchiInChart g u d
        (chartAt FourSpace d ((chartAt FourSpace c).symm x)))).comp
          (K24REG.chartTransitionDerivative c d x) := by
  have hu_d : Cov2DifferentiableAt u
      ((chartAt FourSpace d).symm (chartAt FourSpace d ((chartAt FourSpace c).symm x))) := by
    simpa only [(chartAt FourSpace d).left_inv hd] using hu
  rw [bianchiInChart_eq_covector_local g u c x hx hu,
    bianchiInChart_eq_covector_local g u d _ ((chartAt FourSpace d).map_source hd) hu_d,
    K24REG.chartTransitionDerivative_eq_fderiv c d x hx hd]
  exact bianchiCovectorInChart_transition_local g u hm hg c d x hx hd hu

/-- Actual native Bianchi recovery needs only differentiability at the chosen point. -/
theorem bianchi_coefficients_local (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hu : Cov2DifferentiableAt u ((chartAt FourSpace c).symm x)) :
    covectorInChart (bianchi g u) c x = bianchiInChart g u c x := by
  have ht := bianchiInChart_transition_local g u hm hg c ((chartAt FourSpace c).symm x)
    x hx (mem_chart_source FourSpace _) hu
  ext i
  have h := congrArg (fun B : Covector4 => B (basisVector i)) ht
  rw [coefficientsToCovector_basis] at h
  exact h.symm

end K24.Global.K24LOC


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.K24LOC
open K24NAT
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

theorem quadraticJetTensor_differentiableAt (c : M) (x y : FourSpace)
    (hy : y ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (A : Mat4) :
    Cov2DifferentiableAt (quadraticJetTensor c x xi A) ((chartAt FourSpace c).symm y) := by
  apply cov2_differentiableAt_of_chart _ c y hy
  apply K24REG.matrixToBilinear_differentiableAt
  intro i j
  apply (K24SYM.jetCoefficient_hasFDerivAt x xi (A i j) y).differentiableAt.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hy] with z hz
  exact congrArg (fun B => B i j) (K24SYM.quadraticJetTensor_coefficients c x z hz xi A)

/-- Actual globally reconstructed Bianchi coefficients agree locally with the genuine jet computation. -/
theorem bianchi_quadraticJet_coefficients (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c : M) (x y : FourSpace)
    (hy : y ∈ (chartAt FourSpace c).target) (xi : Fin 4 → ℝ) (A : Mat4) :
    covectorInChart (bianchi g (quadraticJetTensor c x xi A)) c y =
      bianchiInChart g (quadraticJetTensor c x xi A) c y := by
  exact bianchi_coefficients_local g _ hm hg c y hy
    (quadraticJetTensor_differentiableAt c x y hy xi A)

@[simp] theorem covectorInChart_sub (eta zeta : RawCovector M) (c : M) (x : FourSpace)
    (i : Fin 4) :
    covectorInChart (eta - zeta) c x i = covectorInChart eta c x i - covectorInChart zeta c x i := rfl

/-- The genuine native principal symbol on every smooth four-manifold. -/
theorem tensorDefectPrincipalSymbol_native (ghat z : RawCov2 M)
    (hmh : IsMetric ghat) (hmz : IsMetric z)
    (hh : Cov2ContDiff 2 ghat) (hz : Cov2ContDiff 2 z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (xi : Fin 4 → ℝ) (A : Mat4) (i j : Fin 4) :
    tensorDefectPrincipalSymbol ghat z c x xi A i j =
      tensorDefectSymbolFormula ghat z c x xi A i j := by
  have hh1 : Cov2ContDiff 1 ghat := fun d => (hh d).of_le (by norm_num)
  have hz1 : Cov2ContDiff 1 z := fun d => (hz d).of_le (by norm_num)
  let Q := quadraticJetTensor c x xi A
  let eta := bianchi ghat Q - bianchi z Q
  have heq (k : Fin 4) :
      (fun y => covectorInChart eta c y k) =ᶠ[𝓝 x]
        (fun y => bianchiInChart ghat Q c y k - bianchiInChart z Q c y k) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hx] with y hy
    change covectorInChart (bianchi ghat Q - bianchi z Q) c y k = _
    rw [covectorInChart_sub, bianchi_quadraticJet_coefficients ghat hmh hh1 c x y hy xi A,
      bianchi_quadraticJet_coefficients z hmz hz1 c x y hy xi A]
  have hbd (k : Fin 4) : DifferentiableAt ℝ
      (fun y => bianchiInChart ghat Q c y k - bianchiInChart z Q c y k) x :=
    (K24SYM.bianchi_quadraticJet_differentiableAt ghat hmh hh c x hx xi A k).sub
      (K24SYM.bianchi_quadraticJet_differentiableAt z hmz hz c x hx xi A k)
  have heta : CovectorDifferentiableAt eta ((chartAt FourSpace c).symm x) := by
    apply covector_differentiableAt_of_chart eta c x hx
    apply coefficientsToCovector_differentiableAt
    intro k
    exact (hbd k).congr_of_eventuallyEq (heq k)
  have heta_zero (k : Fin 4) : covectorInChart eta c x k = 0 := by
    rw [(heq k).eq_of_nhds,
      K24SYM.bianchi_quadraticJet_center ghat hmh hh c x hx xi A k,
      K24SYM.bianchi_quadraticJet_center z hmz hz c x hx xi A k]
    ring
  have heta_deriv (r k : Fin 4) :
      coordDeriv (fun y => covectorInChart eta c y k) r x =
        xi r * bianchiDifferenceSymbol ghat z c x xi A k := by
    change fderiv ℝ (fun y => covectorInChart eta c y k) x (basisVector r) = _
    rw [(heq k).fderiv_eq]
    change coordDeriv (fun y => bianchiInChart ghat Q c y k - bianchiInChart z Q c y k) r x = _
    rw [K24OP.coordDeriv_sub _ _ x
      (K24SYM.bianchi_quadraticJet_differentiableAt ghat hmh hh c x hx xi A k)
      (K24SYM.bianchi_quadraticJet_differentiableAt z hmz hz c x hx xi A k),
      K24SYM.bianchi_quadraticJet_derivative ghat hmh hh c x hx xi A r k,
      K24SYM.bianchi_quadraticJet_derivative z hmz hz c x hx xi A r k,
      ← mul_sub, K24SYM.bianchiSingleSymbol_sub]
  change cov2InChart (deltaStar z eta) c x i j = _
  rw [deltaStar_coefficients_local z eta hmz hz1 c x hx heta]
  simp only [deltaStarInChart, nablaCovectorInChart, heta_zero, heta_deriv,
    mul_zero, Finset.sum_const_zero, sub_zero, tensorDefectSymbolFormula]


end K24.Global.K24LOC

set_option autoImplicit false
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open K24.Global
universe u

theorem solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (ghat z : RawCov2 M),
      IsMetric ghat → IsMetric z → Cov2ContDiff 2 ghat → Cov2ContDiff 2 z →
      ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      ∀ (xi : Fin 4 → ℝ) (A : Mat4) (i j : Fin 4),
        tensorDefectPrincipalSymbol ghat z c x xi A i j =
          tensorDefectSymbolFormula ghat z c x xi A i j := by
  intro M _ _ _ ghat z hmh hmz hh hz c x hx xi A i j
  exact K24LOC.tensorDefectPrincipalSymbol_native ghat z hmh hmz hh hz c x hx xi A i j


theorem K24LOC_exact_type_wrapper :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (ghat z : RawCov2 M),
      IsMetric ghat → IsMetric z → Cov2ContDiff 2 ghat → Cov2ContDiff 2 z →
      ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      ∀ (xi : Fin 4 → ℝ) (A : Mat4) (i j : Fin 4),
        tensorDefectPrincipalSymbol ghat z c x xi A i j =
          tensorDefectSymbolFormula ghat z c x xi A i j := solution

#print axioms solution
#print axioms K24LOC_exact_type_wrapper
