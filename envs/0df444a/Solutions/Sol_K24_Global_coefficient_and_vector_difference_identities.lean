-- Prove2me | solution 1 for K24.Global.coefficient_and_vector_difference_identities
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:47:20.870188+00:00
-- url     : https://prove2.me/submissions/a9c3d4f3-c211-48fa-8aac-f48fc95dfe28

import Definitions.Def_K24GlobalGeometry


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

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

lemma raise_lower_sum (G : Mat4)
    (hs : ∀ i j, G i j = G j i) (hd : G.det ≠ 0)
    (V : Fin 4 → ℝ) (k : Fin 4) :
    (∑ l, G⁻¹ k l * ∑ p, V p * G p l) = V k := by
  calc
    _ = ∑ p, ((G⁻¹ * G) k p) * V p := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro l _
      rw [hs p l]
      ring
    _ = _ := by
      rw [Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hd)]
      simp [Matrix.one_apply]

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

lemma cov2InChart_sub (g z : RawCov2 M) (c : M) (x : FourSpace) (i j : Fin 4) :
    cov2InChart (g - z) c x i j = cov2InChart g c x i j - cov2InChart z c x i j := by
  rfl

lemma coordDeriv_cov2InChart_sub (g z : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x)
    (hz : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart z c y i j) x)
    (a i j : Fin 4) :
    coordDeriv (fun y => cov2InChart (g - z) c y i j) a x =
      coordDeriv (fun y => cov2InChart g c y i j) a x -
      coordDeriv (fun y => cov2InChart z c y i j) a x := by
  simp only [cov2InChart_sub, coordDeriv, fderiv_fun_sub (hg i j) (hz i j),
    sub_apply]

lemma symmetric_sub (g z : RawCov2 M)
    (hg : IsSymmetricCov2 g) (hz : IsSymmetricCov2 z) :
    IsSymmetricCov2 (g - z) := by
  intro p v w
  change g p v w - z p v w = g p w v - z p w v
  rw [hg p v w, hz p v w]

lemma nabla_symm_combo (z u : RawCov2 M)
    (hz : IsSymmetricCov2 z) (hu : IsSymmetricCov2 u)
    (c : M) (x : FourSpace) (i j l : Fin 4) :
    nablaTensorInChart z u c x i j l + nablaTensorInChart z u c x j i l -
        nablaTensorInChart z u c x l i j =
      coordDeriv (fun y => cov2InChart u c y j l) i x +
      coordDeriv (fun y => cov2InChart u c y i l) j x -
      coordDeriv (fun y => cov2InChart u c y i j) l x -
      2 * ∑ p, christoffelInChart z c x p i j * cov2InChart u c x p l := by
  have h3 : (∑ p, christoffelInChart z c x p j i * cov2InChart u c x p l) =
      ∑ p, christoffelInChart z c x p i j * cov2InChart u c x p l := by
    apply Finset.sum_congr rfl
    intro p _
    rw [christoffel_symm z hz c x p j i]
  have h5 : (∑ p, christoffelInChart z c x p l i * cov2InChart u c x p j) =
      ∑ p, christoffelInChart z c x p i l * cov2InChart u c x j p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [christoffel_symm z hz c x p l i, cov2InChart_symm u hu c x p j]
  have h6 : (∑ p, christoffelInChart z c x p l j * cov2InChart u c x i p) =
      ∑ p, christoffelInChart z c x p j l * cov2InChart u c x i p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [christoffel_symm z hz c x p l j]
  unfold nablaTensorInChart
  rw [h3, h5, h6]
  ring

/-- The symmetric covariant first derivative of the actual metric difference. -/
lemma nabla_difference_combo (g z : RawCov2 M)
    (hs_g : IsSymmetricCov2 g) (hs_z : IsSymmetricCov2 z)
    (c : M) (x : FourSpace) (hd_z : (cov2InChart z c x).det ≠ 0)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x)
    (hz : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart z c y i j) x)
    (i j l : Fin 4) :
    nablaTensorInChart z (g - z) c x i j l +
      nablaTensorInChart z (g - z) c x j i l -
      nablaTensorInChart z (g - z) c x l i j =
    coordDeriv (fun y => cov2InChart g c y j l) i x +
      coordDeriv (fun y => cov2InChart g c y i l) j x -
      coordDeriv (fun y => cov2InChart g c y i j) l x -
      2 * ∑ p, christoffelInChart z c x p i j * cov2InChart g c x p l := by
  rw [nabla_symm_combo z (g - z) hs_z (symmetric_sub g z hs_g hs_z)]
  simp_rw [coordDeriv_cov2InChart_sub g z c x hg hz, cov2InChart_sub,
    mul_sub, Finset.sum_sub_distrib]
  rw [christoffel_lower z hs_z c x hd_z]
  ring

/-- Exact native connection change formula, using genuine coefficient derivatives. -/
theorem connectionDifference_eq_expansion (g z : RawCov2 M)
    (hs_g : IsSymmetricCov2 g) (hs_z : IsSymmetricCov2 z)
    (c : M) (x : FourSpace)
    (hd_g : (cov2InChart g c x).det ≠ 0)
    (hd_z : (cov2InChart z c x).det ≠ 0)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x)
    (hz : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart z c y i j) x)
    (k i j : Fin 4) :
    connectionDifferenceInChart g z c x k i j =
      connectionDifferenceExpansion g z c x k i j := by
  unfold connectionDifferenceInChart connectionDifferenceExpansion
  simp_rw [nabla_difference_combo g z hs_g hs_z c x hd_z hg hz]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_sub]
  have hraise : (∑ l, inverseMetricInChart g c x k l *
      (2 * ∑ p, christoffelInChart z c x p i j * cov2InChart g c x p l)) =
      2 * christoffelInChart z c x k i j := by
    calc
      _ = 2 * ∑ l, inverseMetricInChart g c x k l *
          ∑ p, christoffelInChart z c x p i j * cov2InChart g c x p l := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by
        unfold inverseMetricInChart
        rw [raise_lower_sum _ (cov2InChart_symm g hs_g c x) hd_g]
  rw [hraise]
  unfold christoffelInChart
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

section Manifold

variable [IsManifold I4 ∞ M]

/-- A positive actual metric has an invertible matrix in every valid canonical chart. -/
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

/-- The native formula with positivity supplying both coordinate inverses. -/
theorem metric_connectionDifference_eq_expansion (g z : RawCov2 M)
    (hmetric_g : IsMetric g) (hmetric_z : IsMetric z)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x)
    (hz : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart z c y i j) x)
    (k i j : Fin 4) :
    connectionDifferenceInChart g z c x k i j =
      connectionDifferenceExpansion g z c x k i j :=
  connectionDifference_eq_expansion g z hmetric_g.1 hmetric_z.1 c x
    (metric_chart_det_ne_zero g hmetric_g c x hx)
    (metric_chart_det_ne_zero z hmetric_z c x hx) hg hz k i j

end Manifold


end K24.Global.K24OPConnection





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.K24OP

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- Differentiating the actual scalar coordinate functions requires genuine differentiability. -/
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

/-- A triple contraction is unchanged by exchanging its first and third dummy indices. -/
theorem sum_swap_outer_inner (F : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ p, F a b p) = ∑ a, ∑ b, ∑ p, F p b a := by
  calc
    (∑ a, ∑ b, ∑ p, F a b p) = ∑ b, ∑ a, ∑ p, F a b p :=
      Finset.sum_comm
    _ = ∑ b, ∑ p, ∑ a, F a b p := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ p, ∑ b, ∑ a, F a b p := Finset.sum_comm

/-- The two covariant correction pairs cancel in a contraction. -/
theorem contraction_correction_cancel
    (P U : Mat4) (G : Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ p, (G a p * P p b) * U a b) +
      (∑ a, ∑ b, ∑ p, (G b p * P a p) * U a b) =
    (∑ a, ∑ b, ∑ p, P a b * (G p a * U p b)) +
      (∑ a, ∑ b, ∑ p, P a b * (G p b * U a p)) := by
  congr 1
  · rw [sum_swap_outer_inner]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    ring
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    ring

/-- Trace differentiation for the actual inverse metric and actual tensor coefficients. -/
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

/-- Leibniz contraction written with the native covariant derivatives. -/
theorem covariant_contraction_split (z u : RawCov2 M)
    (P : M → FourSpace → Mat4) (c : M) (x : FourSpace) (j : Fin 4) :
    (∑ a, ∑ b,
      (P c x a b * coordDeriv (fun y => cov2InChart u c y a b) j x +
       coordDeriv (fun y => P c y a b) j x * cov2InChart u c x a b)) =
    (∑ a, ∑ b, P c x a b * nablaTensorInChart z u c x j a b) +
    (∑ a, ∑ b, nablaContravariantInChart z P c x j a b *
      cov2InChart u c x a b) := by
  have hc := contraction_correction_cancel (P c x) (cov2InChart u c x)
    (fun a p => christoffelInChart z c x a j p)
  simp only [nablaTensorInChart, nablaContravariantInChart, mul_sub, add_mul,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith

/-- Subtracting the divergence parts uses the actual connection difference. -/
theorem bianchi_divergence_difference (ghat z u : RawCov2 M)
    (c : M) (x : FourSpace) (j : Fin 4) :
    -(∑ a, ∑ b, inverseMetricInChart ghat c x a b *
      nablaTensorInChart ghat u c x a b j) +
      (∑ a, ∑ b, inverseMetricInChart z c x a b *
        nablaTensorInChart z u c x a b j) =
    -(∑ a, ∑ b, inverseDifferenceInChart ghat z c x a b *
      nablaTensorInChart z u c x a b j) +
    (∑ a, ∑ b, ∑ p, inverseMetricInChart ghat c x a b *
      connectionDifferenceInChart ghat z c x p a b * cov2InChart u c x p j) +
    (∑ a, ∑ b, ∑ p, inverseMetricInChart ghat c x a b *
      connectionDifferenceInChart ghat z c x p a j * cov2InChart u c x b p) := by
  simp only [nablaTensorInChart, inverseDifferenceInChart, connectionDifferenceInChart,
    Matrix.sub_apply, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
  ring

/-- The native trace difference is the covariant contraction of the inverse difference. -/
theorem bianchi_trace_difference (ghat z u : RawCov2 M) (c : M) (x : FourSpace)
    (hh : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart ghat c y a b) x)
    (hz : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart z c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x)
    (j : Fin 4) :
    coordDeriv (metricTraceInChart ghat u c) j x -
      coordDeriv (metricTraceInChart z u c) j x =
    (∑ a, ∑ b, inverseDifferenceInChart ghat z c x a b *
      nablaTensorInChart z u c x j a b) +
    (∑ a, ∑ b, nablaContravariantInChart z (inverseDifferenceInChart ghat z)
      c x j a b * cov2InChart u c x a b) := by
  rw [← covariant_contraction_split]
  rw [coordDeriv_metricTrace ghat u c x hh hu,
      coordDeriv_metricTrace z u c x hz hu]
  simp only [inverseDifferenceInChart, Matrix.sub_apply]
  simp_rw [coordDeriv_sub _ _ x (hh _ _) (hz _ _)]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Full source coefficient identity, with genuine first derivative hypotheses. -/
theorem bianchi_difference_formula (ghat z u : RawCov2 M) (c : M) (x : FourSpace)
    (hh : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart ghat c y a b) x)
    (hz : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart z c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x)
    (j : Fin 4) :
    bianchiInChart ghat u c x j - bianchiInChart z u c x j =
      bianchiDifferenceExpansion ghat z u c x j := by
  unfold bianchiInChart
  calc
    _ = (-(∑ a, ∑ b, inverseMetricInChart ghat c x a b *
            nablaTensorInChart ghat u c x a b j) +
           (∑ a, ∑ b, inverseMetricInChart z c x a b *
            nablaTensorInChart z u c x a b j)) +
         (1 / 2 : ℝ) * (coordDeriv (metricTraceInChart ghat u c) j x -
            coordDeriv (metricTraceInChart z u c) j x) := by ring
    _ = bianchiDifferenceExpansion ghat z u c x j := by
      rw [bianchi_divergence_difference, bianchi_trace_difference ghat z u c x hh hz hu]
      unfold bianchiDifferenceExpansion
      ring

/-- The determinant is a polynomial in the genuine matrix coefficients. -/
theorem matrix_det_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ a b, DifferentiableAt ℝ (fun y => A y a b) x) :
    DifferentiableAt ℝ (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  exact (HasFDerivAt.finsetProd (fun i _ => (hA (σ i) i).hasFDerivAt)).differentiableAt

/-- Matrix inversion differentiability is derived from the polynomial adjugate formula. -/
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

/-- Native Bianchi identity from differentiable metric coefficients and nonsingularity. -/
theorem bianchi_difference_formula_of_nonsingular
    (ghat z u : RawCov2 M) (c : M) (x : FourSpace)
    (hh : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart ghat c y a b) x)
    (hz : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart z c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x)
    (hdet_h : (cov2InChart ghat c x).det ≠ 0)
    (hdet_z : (cov2InChart z c x).det ≠ 0) (j : Fin 4) :
    bianchiInChart ghat u c x j - bianchiInChart z u c x j =
      bianchiDifferenceExpansion ghat z u c x j := by
  exact bianchi_difference_formula ghat z u c x
    (matrix_inv_coefficient_differentiableAt _ x hh hdet_h)
    (matrix_inv_coefficient_differentiableAt _ x hz hdet_z) hu j

/-- Native chart regularity yields ordinary derivatives at every chart-interior point. -/
theorem cov2_coefficients_differentiableAt (u : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x := by
  have hmatrix : DifferentiableAt ℝ (cov2InChart u c) x :=
    ((hu c).differentiableOn_one x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  exact (differentiableAt_apply b _).comp x ((differentiableAt_apply a _).comp x hmatrix)

/-- The Bianchi formula under native chart regularity and coordinate nonsingularity. -/
theorem bianchi_difference_formula_of_contDiff
    (ghat z u : RawCov2 M)
    (hh : Cov2ContDiff 1 ghat) (hz : Cov2ContDiff 1 z) (hu : Cov2ContDiff 1 u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hdet_h : (cov2InChart ghat c x).det ≠ 0)
    (hdet_z : (cov2InChart z c x).det ≠ 0) (j : Fin 4) :
    bianchiInChart ghat u c x j - bianchiInChart z u c x j =
      bianchiDifferenceExpansion ghat z u c x j := by
  exact bianchi_difference_formula_of_nonsingular ghat z u c x
    (cov2_coefficients_differentiableAt ghat hh c x hx)
    (cov2_coefficients_differentiableAt z hz c x hx)
    (cov2_coefficients_differentiableAt u hu c x hx) hdet_h hdet_z j


end K24.Global.K24OP


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.K24OP
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

@[simp] theorem cov2InChart_sub (u v : RawCov2 M) (c : M) (x : FourSpace) (a b : Fin 4) :
    cov2InChart (u - v) c x a b = cov2InChart u c x a b - cov2InChart v c x a b := by
  simp [cov2InChart]

theorem covectorFromCoordinates_sub
    (a b : M → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (fun c x i => a c x i - b c x i) =
      covectorFromCoordinates a - covectorFromCoordinates b := by
  ext p v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    sub_mul, Finset.sum_sub_distrib]

theorem cov2FromCoordinates_sub (a b : M → FourSpace → Mat4) :
    cov2FromCoordinates (fun c x i j => a c x i j - b c x i j) =
      cov2FromCoordinates a - cov2FromCoordinates b := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear,
    sub_mul, mul_sub, Finset.sum_sub_distrib]

theorem lieTensorInChart_sub (Y : RawVector M) (u v : RawCov2 M)
    (c : M) (x : FourSpace)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x)
    (hv : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart v c y a b) x)
    (i j : Fin 4) :
    lieTensorInChart Y (u - v) c x i j =
      lieTensorInChart Y u c x i j - lieTensorInChart Y v c x i j := by
  simp only [lieTensorInChart, cov2InChart_sub]
  simp_rw [coordDeriv_sub _ _ x (hu _ _) (hv _ _)]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Actual Lie derivative is additive in its tensor argument at genuine differentiability. -/
theorem lieTensor_sub (Y : RawVector M) (u v : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v) :
    lieTensor Y (u - v) = lieTensor Y u - lieTensor Y v := by
  unfold lieTensor
  rw [← cov2FromCoordinates_sub]
  funext p
  change cov2FromChartAt p p _ = cov2FromChartAt p p _
  apply congrArg (cov2FromChartAt p p)
  ext i j
  exact lieTensorInChart_sub Y u v p (chartAt FourSpace p p)
    (cov2_coefficients_differentiableAt u hu p _ (mem_chart_target FourSpace p))
    (cov2_coefficients_differentiableAt v hv p _ (mem_chart_target FourSpace p)) i j

theorem metricTraceInChart_sub (g u v : RawCov2 M) (c : M) :
    metricTraceInChart g (u - v) c =
      fun x => metricTraceInChart g u c x - metricTraceInChart g v c x := by
  funext x
  simp [metricTraceInChart, cov2InChart_sub, mul_sub, Finset.sum_sub_distrib]

theorem metricTraceInChart_differentiableAt (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.fun_sum
  intro b _
  exact (hg a b).mul (hu a b)

theorem bianchiInChart_sub (g u v : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x)
    (hv : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart v c y a b) x)
    (j : Fin 4) :
    bianchiInChart g (u - v) c x j = bianchiInChart g u c x j - bianchiInChart g v c x j := by
  unfold bianchiInChart
  rw [metricTraceInChart_sub,
    coordDeriv_sub _ _ x (metricTraceInChart_differentiableAt g u c x hg hu)
      (metricTraceInChart_differentiableAt g v c x hg hv)]
  simp only [nablaTensorInChart, cov2InChart_sub]
  simp_rw [coordDeriv_sub _ _ x (hu _ _) (hv _ _)]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Global Bianchi subtraction, retaining the actual chart derivatives. -/
theorem bianchi_sub (g u v : RawCov2 M)
    (hg : Cov2ContDiff 1 g) (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v)
    (hdet : ∀ p : M, (cov2InChart g p (chartAt FourSpace p p)).det ≠ 0) :
    bianchi g (u - v) = bianchi g u - bianchi g v := by
  unfold bianchi
  rw [← covectorFromCoordinates_sub]
  funext p
  change covectorFromChartAt p p _ = covectorFromChartAt p p _
  apply congrArg (covectorFromChartAt p p)
  ext j
  exact bianchiInChart_sub g u v p (chartAt FourSpace p p)
    (matrix_inv_coefficient_differentiableAt _ _
      (cov2_coefficients_differentiableAt g hg p _ (mem_chart_target FourSpace p)) (hdet p))
    (cov2_coefficients_differentiableAt u hu p _ (mem_chart_target FourSpace p))
    (cov2_coefficients_differentiableAt v hv p _ (mem_chart_target FourSpace p)) j

/-- The actual metric creates both error terms, before Haar projection. -/
theorem actual_metric_vector_difference (ghat z g : RawCov2 M) (Y : RawVector M)
    (hh : Cov2ContDiff 1 ghat) (hz : Cov2ContDiff 1 z) (hg : Cov2ContDiff 1 g)
    (hLg : Cov2ContDiff 1 (lieTensor Y g)) (hLz : Cov2ContDiff 1 (lieTensor Y z))
    (hdet : ∀ p : M, (cov2InChart ghat p (chartAt FourSpace p p)).det ≠ 0) :
    vectorOperator ghat g Y - vectorOperator z z Y =
      actualMetricVectorDefect ghat z g Y := by
  unfold actualMetricVectorDefect vectorOperator killing
  rw [lieTensor_sub Y g z hg hz,
    bianchi_sub ghat (lieTensor Y g) (lieTensor Y z) hh hLg hLz hdet]
  abel


end K24.Global.K24OP


set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace K24.Global.K24OP
universe u

/-- Exact native operator bundle; the original FullK24Statement is a separate target. -/
theorem native_operator_candidate :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ ghat z : RawCov2 M, IsMetric ghat → IsMetric z →
      Cov2ContDiff 1 ghat → Cov2ContDiff 1 z →
      (∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ k i j : Fin 4,
          connectionDifferenceInChart ghat z c x k i j =
            connectionDifferenceExpansion ghat z c x k i j) ∧
      (∀ u : RawCov2 M, Cov2ContDiff 1 u →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ j : Fin 4, bianchiInChart ghat u c x j - bianchiInChart z u c x j =
            bianchiDifferenceExpansion ghat z u c x j) ∧
      (∀ (g : RawCov2 M) (Y : RawVector M),
        Cov2ContDiff 1 g → Cov2ContDiff 1 (lieTensor Y g) →
        Cov2ContDiff 1 (lieTensor Y z) →
        vectorOperator ghat g Y - vectorOperator z z Y =
          actualMetricVectorDefect ghat z g Y) := by
  intro M _ _ _ ghat z hmh hmz hdh hdz
  refine ⟨?_, ?_, ?_⟩
  · intro c x hx k i j
    exact K24OPConnection.metric_connectionDifference_eq_expansion ghat z hmh hmz c x hx
      (cov2_coefficients_differentiableAt ghat hdh c x hx)
      (cov2_coefficients_differentiableAt z hdz c x hx) k i j
  · intro u hu c x hx j
    exact bianchi_difference_formula_of_contDiff ghat z u hdh hdz hu c x hx
      (K24OPConnection.metric_chart_det_ne_zero ghat hmh c x hx)
      (K24OPConnection.metric_chart_det_ne_zero z hmz c x hx) j
  · intro g Y hg hLg hLz
    exact actual_metric_vector_difference ghat z g Y hdh hdz hg hLg hLz
      (fun p => K24OPConnection.metric_chart_det_ne_zero ghat hmh p _
        (mem_chart_target FourSpace p))

/-- Independent elaboration against the frozen candidate proposition. -/
theorem exact_type_wrapper :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ ghat z : RawCov2 M, IsMetric ghat → IsMetric z →
      Cov2ContDiff 1 ghat → Cov2ContDiff 1 z →
      (∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ k i j : Fin 4,
          connectionDifferenceInChart ghat z c x k i j =
            connectionDifferenceExpansion ghat z c x k i j) ∧
      (∀ u : RawCov2 M, Cov2ContDiff 1 u →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ j : Fin 4, bianchiInChart ghat u c x j - bianchiInChart z u c x j =
            bianchiDifferenceExpansion ghat z u c x j) ∧
      (∀ (g : RawCov2 M) (Y : RawVector M),
        Cov2ContDiff 1 g → Cov2ContDiff 1 (lieTensor Y g) →
        Cov2ContDiff 1 (lieTensor Y z) →
        vectorOperator ghat g Y - vectorOperator z z Y =
          actualMetricVectorDefect ghat z g Y) := native_operator_candidate

#print native_operator_candidate
#print axioms native_operator_candidate
#print axioms exact_type_wrapper

end K24.Global.K24OP


universe u
open K24.Global
theorem solution :
∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ ghat z : RawCov2 M, IsMetric ghat → IsMetric z →
      Cov2ContDiff 1 ghat → Cov2ContDiff 1 z →
      (∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
        ∀ k i j : Fin 4,
          connectionDifferenceInChart ghat z c x k i j =
            connectionDifferenceExpansion ghat z c x k i j) ∧
      (∀ u : RawCov2 M, Cov2ContDiff 1 u →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ j : Fin 4, bianchiInChart ghat u c x j - bianchiInChart z u c x j =
            bianchiDifferenceExpansion ghat z u c x j) ∧
      (∀ (g : RawCov2 M) (Y : RawVector M),
        Cov2ContDiff 1 g → Cov2ContDiff 1 (lieTensor Y g) →
        Cov2ContDiff 1 (lieTensor Y z) →
        vectorOperator ghat g Y - vectorOperator z z Y =
          actualMetricVectorDefect ghat z g Y) :=
  K24.Global.K24OP.native_operator_candidate

#print axioms solution
