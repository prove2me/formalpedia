-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.theorem_3_6_scalar_cofactor_laplace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:44:57.136956+00:00
-- url     : https://prove2.me/submissions/afe9bcfd-4069-4ede-a501-c57063e1b63a

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
import Theorems.Thm_GinibrePermanent977_Anticoncentration_proposition_3_5_fourier_compression

-- Solutions/GaussianWeighted.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma weighted_gaussian_pdf (q : ℝ) (hq : 0 ≤ q) (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (-q*x^2/2) =
      (Real.sqrt (1+q))⁻¹ * gaussianPDFReal 0 (NNReal.mk ((1+q)⁻¹) (by positivity)) x := by
  have hq' : 0 < 1+q := by linarith
  have hnorm : Real.sqrt (2*Real.pi*(1+q)⁻¹) * Real.sqrt (1+q) =
      Real.sqrt (2*Real.pi) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*(1+q)⁻¹)]
    congr 1
    field_simp
  have hs1 := (Real.sqrt_pos.mpr hq').ne'
  have hs2 := (Real.sqrt_pos.mpr (show 0 < 2*Real.pi*(1+q)⁻¹ by positivity)).ne'
  have hs3 := (Real.sqrt_pos.mpr (show 0 < 2*Real.pi by positivity)).ne'
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_mk, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  have he : -(x^2)/(2*1) + -q*x^2/2 = -(x^2)/(2*(1+q)⁻¹) := by field_simp; ring
  norm_num only [mul_one] at he
  rw [he]
  have hc : (Real.sqrt (2*Real.pi))⁻¹ =
      (Real.sqrt (1+q))⁻¹ * (Real.sqrt (2*Real.pi*(1+q)⁻¹))⁻¹ := by
    rw [← mul_inv, mul_comm (Real.sqrt (1+q)), hnorm]
  rw [hc]
  ring

lemma weighted_gaussian_fourier (q : ℝ) (hq : 0 ≤ q) (h : ℝ) :
    (∫ x : ℝ, (Real.exp (-q*x^2/2) : ℂ) * Complex.exp (Complex.I * (h*x : ℝ))
      ∂gaussianReal 0 1) =
    ((Real.sqrt (1+q))⁻¹ : ℂ) * Complex.exp (-(h^2 / (2*(1+q)) : ℝ)) := by
  let v : ℝ≥0 := (NNReal.mk ((1+q)⁻¹) (by positivity))
  have hv : v ≠ 0 := by apply NNReal.coe_ne_zero.mp; dsimp [v]; positivity
  have he : (∫ x : ℝ, Complex.exp (Complex.I * (h*x : ℝ)) ∂gaussianReal 0 v) =
      Complex.exp (-(h^2/(2*(1+q)) : ℝ)) := by
    have hc := charFun_gaussianReal (μ := 0) (v := v) h
    rw [charFun_apply_real] at hc
    simpa [v, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hc
  calc
    _ = ∫ x : ℝ, (gaussianPDFReal 0 1 x : ℂ) * (Real.exp (-q*x^2/2) : ℂ) *
        Complex.exp (Complex.I * (h*x : ℝ)) := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
      simp [Complex.real_smul, mul_assoc]
    _ = ∫ x : ℝ, ((Real.sqrt (1+q))⁻¹ : ℂ) * (gaussianPDFReal 0 v x : ℂ) *
        Complex.exp (Complex.I * (h*x : ℝ)) := by
      congr 1
      ext x
      rw [← Complex.ofReal_mul, weighted_gaussian_pdf q hq x, Complex.ofReal_mul]
      simp only [Complex.ofReal_inv, v]
    _ = ((Real.sqrt (1+q))⁻¹ : ℂ) *
        ∫ x : ℝ, (gaussianPDFReal 0 v x : ℂ) * Complex.exp (Complex.I * (h*x : ℝ)) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ = ((Real.sqrt (1+q))⁻¹ : ℂ) *
        ∫ x : ℝ, Complex.exp (Complex.I * (h*x : ℝ)) ∂gaussianReal 0 v := by
      rw [integral_gaussianReal_eq_integral_smul hv]
      simp [Complex.real_smul]
    _ = _ := by rw [he]

lemma quadratic_in_eigenbasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (v : Fin d → ℝ) :
    inner ℝ (∑ i, v i • hA.eigenvectorBasis i)
      (A.toEuclideanLin (∑ i, v i • hA.eigenvectorBasis i)) =
      ∑ i, hA.eigenvalues i * (v i)^2 := by
  have heig (i : Fin d) : A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  simp_rw [map_sum, map_smul, heig, smul_smul]
  have he := hA.eigenvectorBasis.orthonormal.inner_sum v
    (fun i => v i * hA.eigenvalues i) Finset.univ
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [starRingEnd_apply, star_trivial]
  ring

lemma weighted_gaussian_fourier_matrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (h : EuclideanSpace ℝ (Fin d)) :
    (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ h y : ℝ)) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+hA.1.eigenvalues i))⁻¹ : ℂ)) *
        Complex.exp (-(∑ i, (inner ℝ h (hA.1.eigenvectorBasis i))^2 /
          (2*(1+hA.1.eigenvalues i)) : ℝ)) := by
  let q : Fin d → ℝ := hA.1.eigenvalues
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := hA.1.eigenvectorBasis
  have hquad (v : Fin d → ℝ) :
      inner ℝ (∑ i, v i • b i) (A.toEuclideanLin (∑ i, v i • b i)) =
        ∑ i, q i * (v i)^2 := quadratic_in_eigenbasis A hA.1 v
  change (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ h y : ℝ)) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+q i))⁻¹ : ℂ)) *
        Complex.exp (-(∑ i, (inner ℝ h (b i))^2 / (2*(1+q i)) : ℝ))

  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map (Measurable.aemeasurable (by fun_prop)) (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [hquad, inner_sum, real_inner_smul_right]
  have hfactor (v : Fin d → ℝ) :
      (Real.exp (-(∑ i, q i * v i ^2)/2) : ℂ) *
          Complex.exp (Complex.I * (∑ i, v i * inner ℝ h (b i) : ℝ)) =
      ∏ i, (Real.exp (-q i * (v i)^2/2) : ℂ) *
        Complex.exp (Complex.I * ((inner ℝ h (b i))*v i : ℝ)) := by
    rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum, ← Complex.exp_sum]
    congr 1
    · congr 2
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      simp only [neg_mul]
    · congr 1
      simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [show (∫ v : Fin d → ℝ,
        (Real.exp (-(∑ i, q i * v i ^2)/2) : ℂ) *
          Complex.exp (Complex.I * (∑ i, v i * inner ℝ h (b i) : ℝ))
          ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ v : Fin d → ℝ, ∏ i,
        (Real.exp (-q i * (v i)^2/2) : ℂ) *
        Complex.exp (Complex.I * ((inner ℝ h (b i))*v i : ℝ))
          ∂Measure.pi (fun _ => gaussianReal 0 1) from
      integral_congr_ae (Filter.Eventually.of_forall hfactor)]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) =>
    (Real.exp (-q i*x^2/2) : ℂ) * Complex.exp (Complex.I * (inner ℝ h (b i)*x : ℝ)))]
  have hw (i : Fin d) := weighted_gaussian_fourier (q i)
    (show 0 ≤ q i from hA.eigenvalues_nonneg i) (inner ℝ h (b i))
  simp_rw [hw]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  congr 1
  simp [Complex.ofReal_sum, Finset.sum_neg_distrib]

end GinibrePermanent977.Anticoncentration

-- Solutions/ScalarGaussian.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal Quaternion ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma real_gaussian_characteristic (v : ℝ≥0) (z : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * (x*z : ℝ)) ∂gaussianReal 0 v) =
      (Real.exp (-(v : ℝ)*z^2/2) : ℂ) := by
  simpa [charFun_apply_real, mul_comm, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow, neg_div] using charFun_gaussianReal (μ := 0) (v := v) z

lemma vector_gaussian_characteristic {d : ℕ} (v : ℝ≥0) (z : Fin d → ℝ) :
    (∫ x : Fin d → ℝ, Complex.exp (Complex.I * (x ⬝ᵥ z : ℝ))
      ∂Measure.pi (fun _ => gaussianReal 0 v)) =
      (Real.exp (-(v : ℝ)*(∑ i, z i^2)/2) : ℂ) := by
  have hfactor (x : Fin d → ℝ) : Complex.exp (Complex.I * (x ⬝ᵥ z : ℝ)) =
      ∏ i, Complex.exp (Complex.I * (x i*z i : ℝ)) := by
    simp [dotProduct, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hfactor]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Complex.exp (Complex.I * (x*z i : ℝ)))]
  simp_rw [real_gaussian_characteristic]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 3
  rw [← Finset.sum_div, ← Finset.mul_sum]

lemma scalar_gaussian_characteristic (F : Scalar) (z : F.K) :
    (∫ x : F.K, Complex.exp (Complex.I * ((inner ℝ z x : ℝ) : ℂ)) ∂gaussian F) =
      (Real.exp (-‖z‖^2/(2*(F.beta : ℝ))) : ℂ) := by
  cases F
  · dsimp only [Scalar.K] at z ⊢
    have hz : ‖z‖^2 = (show ℝ from z)^2 := by
      rw [← real_inner_self_eq_norm_sq]
      change (show ℝ from z)*(show ℝ from z) = (show ℝ from z)^2
      ring
    rw [hz]
    simpa only [gaussian, Scalar.beta, Nat.cast_one, mul_one, Scalar.instNormedRing,
      Scalar.instInnerProductSpace, Real.norm_eq_abs, sq_abs, RCLike.inner_apply,
      starRingEnd_apply, star_trivial, NNReal.coe_one, neg_mul, one_mul] using
      real_gaussian_characteristic 1 (show ℝ from z)
  · have hmk : Measurable (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ)) :=
      Complex.equivRealProdCLM.symm.continuous.measurable
    change (∫ x : ℂ, Complex.exp (Complex.I * ((inner ℝ z x : ℝ) : ℂ))
      ∂((gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))).map
        (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ))) = _
    rw [integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop))]
    rw [← (measurePreserving_finTwoArrow (gaussianReal 0 (1/2))).map_eq,
      integral_map (Measurable.aemeasurable (by fun_prop))
        (Measurable.aestronglyMeasurable (by fun_prop))]
    let e := Complex.orthonormalBasisOneI.repr
    let w : Fin 2 → ℝ := e z
    have hi (x : Fin 2 → ℝ) : inner ℝ z (⟨x 0,x 1⟩ : ℂ) = x ⬝ᵥ w := by
      have hx : e (⟨x 0,x 1⟩ : ℂ) = WithLp.toLp 2 x := by
        ext i
        fin_cases i <;> rfl
      calc
        inner ℝ z (⟨x 0,x 1⟩ : ℂ) = inner ℝ (e z) (e (⟨x 0,x 1⟩ : ℂ)) :=
          (e.inner_map_map z (⟨x 0,x 1⟩ : ℂ)).symm
        _ = inner ℝ (e z) (WithLp.toLp 2 x) := by rw [hx]
        _ = x ⬝ᵥ w := by simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, w]
    change (∫ x : Fin 2 → ℝ, Complex.exp (Complex.I * ((inner ℝ z (⟨x 0,x 1⟩ : ℂ) : ℝ) : ℂ))
      ∂Measure.pi (fun _ => gaussianReal 0 (1/2))) = _
    simp_rw [hi]
    rw [vector_gaussian_characteristic]
    have hn : ∑ i, w i^2 = ‖z‖^2 := by
      rw [← EuclideanSpace.real_norm_sq_eq (e z), e.norm_map]
    rw [hn]
    congr 2
    norm_num [Scalar.beta]
    ring
  · letI : MeasureSpace ℍ := Scalar.instMeasureSpace .quaternion
    haveI : BorelSpace ℍ := Scalar.instBorelSpace .quaternion
    have hmap : Measurable quatOfCoords := quatOfCoords.continuous_of_finiteDimensional.measurable
    change (∫ x : ℍ, Complex.exp (Complex.I * ((inner ℝ z x : ℝ) : ℂ))
      ∂(Measure.pi (fun _ : Fin 4 => gaussianReal 0 (1/4))).map quatOfCoords) = _
    rw [integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop))]
    let e := Quaternion.linearIsometryEquivTuple
    let w : Fin 4 → ℝ := e z
    have hi (x : Fin 4 → ℝ) : inner ℝ z (quatOfCoords x) = x ⬝ᵥ w := by
      have hx : e (quatOfCoords x) = WithLp.toLp 2 x := by
        ext i
        fin_cases i <;> rfl
      have he := (e.inner_map_map z (quatOfCoords x)).symm
      rw [hx] at he
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, w] using he
    simp_rw [hi]
    rw [vector_gaussian_characteristic]
    have hn : ∑ i, w i^2 = ‖z‖^2 := by
      rw [← EuclideanSpace.real_norm_sq_eq (e z), e.norm_map]
    rw [hn]
    congr 2
    norm_num [Scalar.beta]
    ring

lemma vector_scalar_gaussian_characteristic (F : Scalar) {m : ℕ} (z : Fin m → F.K) :
    (∫ x : Fin m → F.K, Complex.exp (Complex.I * ((realInner z x : ℝ) : ℂ)) ∂gaussVec F m) =
      (Real.exp (-(∑ i, ‖z i‖^2)/(2*(F.beta : ℝ))) : ℂ) := by
  have hfactor (x : Fin m → F.K) : Complex.exp (Complex.I * ((realInner z x : ℝ) : ℂ)) =
      ∏ i, Complex.exp (Complex.I * ((inner ℝ (z i) (x i) : ℝ) : ℂ)) := by
    simp [realInner, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hfactor]
  unfold gaussVec
  rw [integral_fintype_prod_eq_prod (fun i (x : F.K) =>
    Complex.exp (Complex.I * ((inner ℝ (z i) x : ℝ) : ℂ)))]
  simp_rw [scalar_gaussian_characteristic]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 3
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

lemma vector_scalar_gaussian_linear_nonneg (F : Scalar) {m : ℕ}
    (l : (Fin m → F.K) →ₗ[ℝ] ℝ) :
    0 ≤ (∫ x, Complex.exp (Complex.I * ((l x : ℝ) : ℂ)) ∂gaussVec F m) := by
  haveI : FiniteDimensional ℝ F.K := by
    cases F
    · exact inferInstanceAs (FiniteDimensional ℝ ℝ)
    · exact inferInstanceAs (FiniteDimensional ℝ ℂ)
    · exact inferInstanceAs (FiniteDimensional ℝ ℍ)
  haveI : CompleteSpace F.K := by cases F <;> infer_instance
  let lj (j : Fin m) : F.K →L[ℝ] ℝ :=
    (l.comp (LinearMap.single ℝ (fun _ : Fin m => F.K) j)).toContinuousLinearMap
  let z (j : Fin m) : F.K := (InnerProductSpace.toDual ℝ F.K).symm (lj j)
  have hl (x : Fin m → F.K) : l x = realInner z x := by
    calc
      l x = l (∑ j, Pi.single j (x j)) := congrArg l (Finset.univ_sum_single x).symm
      _ = ∑ j, l (Pi.single j (x j)) := by rw [map_sum]
      _ = realInner z x := by
        unfold realInner
        apply Finset.sum_congr rfl
        intro j _
        exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := lj j) (x := x j)).symm
  simp_rw [hl]
  rw [vector_scalar_gaussian_characteristic]
  apply Complex.nonneg_iff.mpr
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨(Real.exp_pos _).le, trivial⟩

end GinibrePermanent977.Anticoncentration


-- Solutions/GaussianCoordinates.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

instance scalar_finiteDimensional (F : Scalar) : FiniteDimensional ℝ F.K := by
  cases F
  · exact inferInstanceAs (FiniteDimensional ℝ ℝ)
  · exact inferInstanceAs (FiniteDimensional ℝ ℂ)
  · exact inferInstanceAs (FiniteDimensional ℝ ℍ)

instance scalar_completeSpace (F : Scalar) : CompleteSpace F.K := by cases F <;> infer_instance
instance scalar_secondCountable (F : Scalar) : SecondCountableTopology F.K := by
  cases F
  · exact inferInstanceAs (SecondCountableTopology ℝ)
  · exact inferInstanceAs (SecondCountableTopology ℂ)
  · exact inferInstanceAs (SecondCountableTopology ℍ)


lemma scalar_smul_mul (F : Scalar) (r : ℝ) (x y : F.K) : (r • x)*y = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)

lemma scalar_mul_smul (F : Scalar) (r : ℝ) (x y : F.K) : x*(r • y) = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)

lemma gaussian_vector_stdGaussian (F : Scalar) (m : ℕ) :
    (stdGaussian (PiLp 2 (fun _ : Fin m => F.K))).map
      (fun x => (Real.sqrt (F.beta : ℝ))⁻¹ • x) =
    (gaussVec F m).map (WithLp.toLp 2) := by
  let E := PiLp 2 (fun _ : Fin m => F.K)
  haveI : IsProbabilityMeasure (gaussVec F m) := by unfold gaussVec; infer_instance
  have hto : Measurable (WithLp.toLp 2 : (Fin m → F.K) → E) :=
    (PiLp.continuous_toLp 2 _).measurable
  haveI : IsProbabilityMeasure ((gaussVec F m).map (WithLp.toLp 2)) :=
    Measure.isProbabilityMeasure_map hto.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_smul, charFun_stdGaussian, charFun_apply,
    integral_map hto.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))]
  have heq (x : Fin m → F.K) :
      Complex.exp (((inner ℝ (WithLp.toLp 2 x : E) t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((realInner t.ofLp x : ℝ) : ℂ)) := by
    rw [real_inner_comm, PiLp.inner_apply]
    simp only [WithLp.ofLp_toLp, realInner, mul_comm]
  simp_rw [heq]
  rw [vector_scalar_gaussian_characteristic]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_div]
  rw [← Complex.ofReal_exp]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    inv_pow, Real.sq_sqrt (beta_pos F).le, PiLp.norm_sq_eq_of_L2]
  congr 2
  field_simp

lemma gaussian_vector_coordinates (F : Scalar) (m : ℕ) (hm : 0 < m) :
    ∃ d : ℕ, 0 < d ∧ ∃ Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin m → F.K),
      MeasurePreserving Φ (SmoothBerr.stdGaussianVec d) (gaussVec F m) := by
  let E := PiLp 2 (fun _ : Fin m => F.K)
  let d := Module.finrank ℝ E
  let c := (Real.sqrt (F.beta : ℝ))⁻¹
  let b := stdOrthonormalBasis ℝ E
  let Ψ : (Fin d → ℝ) →ₗ[ℝ] E :=
    ∑ a : Fin d, (LinearMap.proj a).smulRight (b a)
  let Φ : (Fin d → ℝ) →ₗ[ℝ] (Fin m → F.K) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => F.K)).toLinearMap.comp (c • Ψ)
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  haveI : Nontrivial F.K := by
    cases F
    · exact inferInstanceAs (Nontrivial ℝ)
    · exact inferInstanceAs (Nontrivial ℂ)
    · exact inferInstanceAs (Nontrivial ℍ[ℝ])
  refine ⟨d, Module.finrank_pos, Φ, ?_⟩
  have hΦ : Measurable Φ := Φ.continuous_of_finiteDimensional.measurable
  refine ⟨hΦ, ?_⟩
  apply (MeasurableEquiv.toLp 2 (Fin m → F.K)).measurableEmbedding.map_injective
  change Measure.map (WithLp.toLp 2) (Measure.map Φ _) = Measure.map (WithLp.toLp 2) _
  rw [Measure.map_map (PiLp.continuous_toLp 2 _).measurable hΦ]
  have hg := gaussian_vector_stdGaussian F m
  rw [stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)] at hg
  convert hg using 1
  congr 1
  funext x
  change WithLp.toLp 2 ((c • Ψ x).ofLp) = c • ∑ i, x i • b i
  rw [WithLp.toLp_ofLp]
  congr 1
  simp [Ψ, _root_.sum_apply]

end GinibrePermanent977.Anticoncentration
-- Solutions/GaussianNormLaplace.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators NNReal Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma standard_gaussian_quadratic_laplace (q : ℝ) (hq : 0 ≤ q) :
    (∫ x : ℝ, Real.exp (-q*x^2/2) ∂gaussianReal 0 1) = (Real.sqrt (1+q))⁻¹ := by
  have h := weighted_gaussian_fourier q hq 0
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    zero_pow (by decide : 2 ≠ 0), zero_div, neg_zero] at h
  have hr := integral_ofReal (𝕜 := ℂ) (μ := gaussianReal 0 1)
    (f := fun x : ℝ => Real.exp (-q*x^2/2))
  have hh := hr.symm.trans h
  simpa using congrArg Complex.re hh

lemma gaussian_quadratic_laplace (v : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : ℝ, Real.exp (-s*x^2) ∂gaussianReal 0 v) =
      (Real.sqrt (1+2*(v : ℝ)*s))⁻¹ := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v : ℝ)*x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  have heq (x : ℝ) : -s*(Real.sqrt (v : ℝ)*x)^2 = -(2*(v : ℝ)*s)*x^2/2 := by
    rw [mul_pow, Real.sq_sqrt v.coe_nonneg]
    ring
  simp_rw [heq]
  exact standard_gaussian_quadratic_laplace _ (by positivity)

lemma standard_vector_quadratic_laplace {d : ℕ} (q : ℝ) (hq : 0 ≤ q) :
    (∫ x : Fin d → ℝ, Real.exp (-q*(∑ i, x i^2)/2) ∂SmoothBerr.stdGaussianVec d) =
      (Real.sqrt (1+q))⁻¹ ^ d := by
  have hpoint (x : Fin d → ℝ) : Real.exp (-q*(∑ i, x i^2)/2) =
      ∏ i, Real.exp (-q*x i^2/2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_div, ← Finset.mul_sum]
  simp_rw [hpoint]
  unfold SmoothBerr.stdGaussianVec
  rw [integral_fintype_prod_eq_prod (fun _ (x : ℝ) => Real.exp (-q*x^2/2))]
  simp_rw [standard_gaussian_quadratic_laplace q hq]
  simp

lemma scalar_finrank (F : Scalar) : Module.finrank ℝ F.K = F.beta := by
  cases F
  · exact (show Module.finrank ℝ ℝ = 1 by simp)
  · exact Complex.finrank_real_complex
  · exact Quaternion.finrank_eq_four

lemma stdGaussian_norm_laplace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : E, Real.exp (-s*‖x‖^2) ∂stdGaussian E) =
      (Real.sqrt (1+2*s))⁻¹ ^ Module.finrank ℝ E := by
  rw [stdGaussian, integral_map (Measurable.aemeasurable (by fun_prop)) (Measurable.aestronglyMeasurable (by fun_prop))]
  have hn (x : Fin (Module.finrank ℝ E) → ℝ) :
      ‖∑ i, x i • stdOrthonormalBasis ℝ E i‖^2 = ∑ i, x i^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [starRingEnd_apply, star_trivial, ← pow_two] using
      (stdOrthonormalBasis ℝ E).orthonormal.inner_sum x x Finset.univ
  simp_rw [hn]
  have hp (x : Fin (Module.finrank ℝ E) → ℝ) :
      -s*(∑ i, x i^2) = -(2*s)*(∑ i, x i^2)/2 := by ring
  simp_rw [hp]
  exact standard_vector_quadratic_laplace (2*s) (by positivity)

lemma gaussVec_norm_laplace (F : Scalar) (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : Fin m → F.K, Real.exp (-s*(∑ i, ‖x i‖^2)) ∂gaussVec F m) =
      (Real.sqrt (1+2*s/(F.beta : ℝ)))⁻¹ ^ (m*F.beta) := by
  let E := PiLp 2 (fun _ : Fin m => F.K)
  have hg := gaussian_vector_stdGaussian F m
  have hdim : Module.finrank ℝ E = m*F.beta := by
    calc
      _ = Module.finrank ℝ (Fin m → F.K) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => F.K)).toLinearEquiv.finrank_eq
      _ = _ := by simp [Module.finrank_pi_fintype, scalar_finrank]
  have hto : Measurable (WithLp.toLp 2 : (Fin m → F.K) → E) :=
    (PiLp.continuous_toLp 2 _).measurable
  calc
    _ = ∫ x : E, Real.exp (-s*‖x‖^2) ∂(gaussVec F m).map (WithLp.toLp 2) := by
      rw [integral_map hto.aemeasurable (by fun_prop)]
      congr 1
      funext x
      rw [PiLp.norm_sq_eq_of_L2]
    _ = ∫ x : E, Real.exp (-s*‖(Real.sqrt (F.beta : ℝ))⁻¹ • x‖^2) ∂stdGaussian E := by
      rw [← hg, integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x : E, Real.exp (-(s/(F.beta : ℝ))*‖x‖^2) ∂stdGaussian E := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change Real.exp (-s*‖(Real.sqrt (F.beta : ℝ))⁻¹ • x‖^2) = _
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
        Real.sq_sqrt (beta_pos F).le]
      congr 1
      ring
    _ = _ := by
      rw [stdGaussian_norm_laplace _ (by positivity), hdim]
      congr 4
      ring

end GinibrePermanent977.Anticoncentration
-- Solutions/GammaLaplace.lean
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma integral_gammaMeasure_real (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂gammaMeasure a r) = ∫ x, gammaPDFReal a r x * f x := by
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  · exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)
  · exact Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)

lemma integral_gammaPDFReal (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∫ x, gammaPDFReal a r x = 1 := by
  haveI : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  have h := integral_gammaMeasure_real a r ha hr (fun _ => 1)
  simpa using h.symm

lemma gamma_laplace_transform (a r s : ℝ) (ha : 0 < a) (hr : 0 < r) (hs : 0 ≤ s) :
    (∫ x, Real.exp (-s*x) ∂gammaMeasure a r) = (r/(r+s))^a := by
  have hrs : 0 < r+s := by linarith
  have hpoint (x : ℝ) : gammaPDFReal a r x * Real.exp (-s*x) =
      (r/(r+s))^a * gammaPDFReal a (r+s) x := by
    unfold gammaPDFReal
    split_ifs with hx
    · rw [mul_assoc, ← Real.exp_add]
      have hex : -(r*x)+ -s*x = -((r+s)*x) := by ring
      rw [hex, Real.div_rpow hr.le hrs.le]
      field_simp
    · simp
  rw [integral_gammaMeasure_real a r ha hr]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_gammaPDFReal a (r+s) ha hrs, mul_one]

lemma gammaMeasure_ae_nonneg (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change gammaMeasure a r (Set.Iio 0) = 0
  unfold gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma gammaPi_ae_nonneg (F : Scalar) (m : ℕ) : ∀ᵐ γ ∂gammaVec F m, 0 ≤ gammaPi γ := by
  have h (i : Fin m) : ∀ᵐ γ ∂gammaVec F m, 0 ≤ γ i := by
    exact (measurePreserving_eval (fun k : Fin m => gammaLaw F (k.val+1)) i).quasiMeasurePreserving.ae
      (gammaMeasure_ae_nonneg _ _)
  filter_upwards [ae_all_iff.mpr h] with γ hγ
  exact Finset.prod_nonneg (fun i _ => hγ i)

lemma gammaPi_succ {m : ℕ} (γ : Fin (m+2) → ℝ) :
    gammaPi γ = gammaPi (fun i : Fin (m+1) => γ i.castSucc) * γ (Fin.last (m+1)) := by
  unfold gammaPi
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last]
  rw [if_pos (by omega)]

end GinibrePermanent977.Anticoncentration
-- Solutions/GaussianGammaLaplace.lean
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma gaussVec_norm_gamma_laplace (F : Scalar) (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : Fin m → F.K, Real.exp (-s*(∑ i, ‖x i‖^2)) ∂gaussVec F m) =
      ∫ γ : ℝ, Real.exp (-s*γ) ∂gammaLaw F m := by
  have hb := beta_pos F
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hr : 0 < (F.beta : ℝ)/2 := by positivity
  have hshape : 0 < (F.beta : ℝ)*(m : ℝ)/2 := by positivity
  have hA : 0 < 1+2*s/(F.beta : ℝ) := by positivity
  rw [gaussVec_norm_laplace F m s hs, gammaLaw,
    gamma_laplace_transform _ _ s hshape hr hs]
  have hratio : ((F.beta : ℝ)/2)/((F.beta : ℝ)/2+s) = (1+2*s/(F.beta : ℝ))⁻¹ := by
    field_simp
  rw [hratio, Real.inv_rpow hA.le]
  rw [← Real.rpow_natCast, Real.inv_rpow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hA.le]
  congr 2
  push_cast
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/GammaProduct.lean
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma measurable_gammaPi (m : ℕ) : Measurable (gammaPi : (Fin m → ℝ) → ℝ) := by
  unfold gammaPi
  fun_prop

instance gammaVec_probability (F : Scalar) (m : ℕ) : IsProbabilityMeasure (gammaVec F m) := by
  unfold gammaVec
  infer_instance
instance gaussVec_probability (F : Scalar) (m : ℕ) : IsProbabilityMeasure (gaussVec F m) := by
  unfold gaussVec
  infer_instance
instance ginibre_probability (F : Scalar) (m n : ℕ) : IsProbabilityMeasure (ginibre F m n) := by
  unfold ginibre
  infer_instance

lemma gammaPi_nonneg_prod {A : Type*} [MeasurableSpace A] (F : Scalar) (m : ℕ)
    (ν : Measure A) [IsProbabilityMeasure ν] :
    ∀ᵐ p ∂(gammaVec F m).prod ν, 0 ≤ gammaPi p.1 :=
  (measurePreserving_fst (μ := gammaVec F m) (ν := ν)).quasiMeasurePreserving.ae (gammaPi_ae_nonneg F m)

lemma gammaVec_split_last (F : Scalar) (m : ℕ) :
    MeasurePreserving
      (fun γ : Fin (m+2) → ℝ => (γ (Fin.last (m+1)), fun i : Fin (m+1) => γ i.castSucc))
      (gammaVec F (m+2)) ((gammaLaw F (m+2)).prod (gammaVec F (m+1))) := by
  have h := measurePreserving_piFinSuccAbove
    (fun k : Fin (m+2) => gammaLaw F (k.val+1)) (Fin.last (m+1))
  convert h using 1
  · funext γ
    apply Prod.ext
    · rfl
    · funext i
      change γ i.castSucc = γ ((Fin.last (m+1)).succAbove i)
      rw [Fin.succAbove_last]
  · rfl
  · congr 1
    simp [gammaVec, Fin.succAbove_last]

lemma gammaPi_integral_split_last (F : Scalar) (m : ℕ) (s : ℝ) :
    (∫ γ, Real.exp (-s*gammaPi γ) ∂gammaVec F (m+2)) =
    ∫ p : ℝ × (Fin (m+1) → ℝ), Real.exp (-s*gammaPi p.2*p.1)
      ∂(gammaLaw F (m+2)).prod (gammaVec F (m+1)) := by
  have h := gammaVec_split_last F m
  let g := fun p : ℝ × (Fin (m+1) → ℝ) => Real.exp (-s*gammaPi p.2*p.1)
  have hg : Measurable g := by
    have hp := measurable_gammaPi (m+1)
    dsimp [g]; fun_prop
  have he := integral_map h.aemeasurable hg.aestronglyMeasurable
  rw [h.map_eq] at he
  rw [he]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro γ
  change Real.exp (-s*gammaPi γ) = Real.exp (-s*gammaPi (fun i => γ i.castSucc)*γ (Fin.last (m+1)))
  rw [gammaPi_succ]
  congr 1
  ring

end GinibrePermanent977.Anticoncentration
-- Solutions/IsotropicFourierLaplace.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma realInner_smul_exchange (F : Scalar) {m : ℕ} (c : ℝ) (x y : Fin m → F.K) :
    realInner (c • x) y = realInner (c • y) x := by
  unfold realInner
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, real_inner_smul_left]
  rw [real_inner_comm]

lemma charFunK_re_integral {Ω : Type*} [MeasurableSpace Ω] (F : Scalar) {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Fin m → F.K) (hX : Measurable X)
    (z : Fin m → F.K) :
    (charFunK μ X z).re = ∫ ω, Real.cos (realInner z (X ω)) ∂μ := by
  have hi : Integrable (fun ω => Complex.exp (Complex.I * ((realInner z (X ω) : ℝ) : ℂ))) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.aestronglyMeasurable (by unfold realInner; fun_prop))
    exact Eventually.of_forall (fun ω => by simp [Complex.norm_exp])
  have hr : (charFunK μ X z).re = ∫ ω,
      (Complex.exp (Complex.I * ((realInner z (X ω) : ℝ) : ℂ))).re ∂μ := (integral_re hi).symm
  rw [hr]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => by simp [Complex.exp_re, mul_comm Complex.I])

lemma gaussian_cos_norm_kernel (F : Scalar) {m : ℕ} (s : ℝ) (hs : 0 ≤ s) (x : Fin m → F.K) :
    (∫ t : Fin m → F.K,
      Real.cos (realInner (Real.sqrt (2*(F.beta : ℝ)*s) • t) x) ∂gaussVec F m) =
      Real.exp (-s*(∑ i, ‖x i‖^2)) := by
  haveI : IsProbabilityMeasure (gaussVec F m) := by unfold gaussVec; infer_instance
  simp_rw [realInner_smul_exchange F]
  have hrepr := charFunK_re_integral F (gaussVec F m) id measurable_id
    (Real.sqrt (2*(F.beta : ℝ)*s) • x)
  change _ = (∫ t : Fin m → F.K, Real.cos (realInner (Real.sqrt (2*(F.beta : ℝ)*s) • x) t) ∂gaussVec F m) at hrepr
  rw [← hrepr]
  have hc := congrArg Complex.re (vector_scalar_gaussian_characteristic F
    (Real.sqrt (2*(F.beta : ℝ)*s) • x))
  change (charFunK (gaussVec F m) id (Real.sqrt (2*(F.beta : ℝ)*s) • x)).re = _ at hc
  rw [hc, Complex.ofReal_re]
  have hn : (∑ i, ‖(Real.sqrt (2*(F.beta : ℝ)*s) • x) i‖^2) =
      (2*(F.beta : ℝ)*s)*(∑ i, ‖x i‖^2) := by
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (by positivity : 0 ≤ 2*(F.beta : ℝ)*s), ← Finset.mul_sum]
  rw [hn]
  congr 1
  field_simp [(beta_pos F).ne']

lemma isotropic_fourier_laplace {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Scalar) {m : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin m → F.K) (Y : Ω' → Fin m → F.K)
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ z, (charFunK μ X z).re ≤ (charFunK ν Y z).re)
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ ω, Real.exp (-s*(∑ i, ‖X ω i‖^2)) ∂μ) ≤
      ∫ ω, Real.exp (-s*(∑ i, ‖Y ω i‖^2)) ∂ν := by
  haveI : IsProbabilityMeasure (gaussVec F m) := by unfold gaussVec; infer_instance
  let c := Real.sqrt (2*(F.beta : ℝ)*s)
  have hI {A : Type} [MeasurableSpace A] (η : Measure A) [IsProbabilityMeasure η]
      (Z : A → Fin m → F.K) (hZ : Measurable Z) :
      Integrable (fun p : (Fin m → F.K) × A => Real.cos (realInner (c • p.1) (Z p.2)))
        ((gaussVec F m).prod η) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.aestronglyMeasurable (by unfold realInner; fun_prop))
    exact Eventually.of_forall (fun p => by simpa using Real.abs_cos_le_one (realInner (c • p.1) (Z p.2)))
  have hiX := hI μ X hX
  have hiY := hI ν Y hY
  have hineq := integral_mono hiX.integral_prod_left hiY.integral_prod_left
    (fun t => by
      change (∫ ω, Real.cos (realInner (c • t) (X ω)) ∂μ) ≤
        ∫ ω, Real.cos (realInner (c • t) (Y ω)) ∂ν
      exact (charFunK_re_integral F μ X hX (c • t)) ▸
        (charFunK_re_integral F ν Y hY (c • t)) ▸ h (c • t))
  have hswapX := integral_integral_swap (f := fun t ω => Real.cos (realInner (c • t) (X ω))) hiX
  have hswapY := integral_integral_swap (f := fun t ω => Real.cos (realInner (c • t) (Y ω))) hiY
  change (∫ t, ∫ ω, Real.cos (realInner (c • t) (X ω)) ∂μ ∂gaussVec F m) = _ at hswapX
  change (∫ t, ∫ ω, Real.cos (realInner (c • t) (Y ω)) ∂ν ∂gaussVec F m) = _ at hswapY
  rw [hswapX, hswapY] at hineq
  simpa only [c, gaussian_cos_norm_kernel F s hs] using hineq

end GinibrePermanent977.Anticoncentration
-- Solutions/BenchmarkTransforms.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma norm_smul_sum_sq (F : Scalar) {m : ℕ} (c : ℝ) (x : Fin m → F.K) :
    (∑ i, ‖(c • x) i‖^2) = c^2*(∑ i, ‖x i‖^2) := by
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum]

lemma realInner_smul_move (F : Scalar) {m : ℕ} (c : ℝ) (x y : Fin m → F.K) :
    realInner x (c • y) = realInner (c • x) y := by
  unfold realInner
  simp only [Pi.smul_apply, real_inner_smul_left, real_inner_smul_right]

lemma benchVec_measurable (F : Scalar) (n : ℕ) :
    Measurable (benchVec (F := F) (n := n)) := by
  have h := measurable_gammaPi (n-1)
  unfold benchVec
  fun_prop

lemma bench_characteristic (F : Scalar) (n : ℕ) (z : Fin (n+1) → F.K) :
    charFunK (benchLaw F (n+1)) benchVec z =
      ∫ γ : Fin n → ℝ, (Real.exp (-gammaPi γ*(∑ i, ‖z i‖^2)/(2*(F.beta : ℝ))) : ℂ)
        ∂gammaVec F n := by
  let g := fun p : (Fin n → ℝ) × (Fin (n+1) → F.K) =>
    Complex.exp (Complex.I * ((realInner z (Real.sqrt (gammaPi p.1) • p.2) : ℝ) : ℂ))
  have hm : Measurable g := by
    have h := measurable_gammaPi n
    unfold g realInner
    fun_prop
  have hi : Integrable g ((gammaVec F n).prod (gaussVec F (n+1))) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by simp [g, Complex.norm_exp])
  change (∫ p, g p ∂(gammaVec F n).prod (gaussVec F (n+1))) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [gammaPi_ae_nonneg F n] with γ hγ
  dsimp [g]
  simp_rw [realInner_smul_move F]
  rw [vector_scalar_gaussian_characteristic, norm_smul_sum_sq, Real.sq_sqrt hγ]
  simp only [neg_mul]

lemma re_integral_ofReal {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : A → ℝ) :
    (∫ x, (f x : ℂ) ∂μ).re = ∫ x, f x ∂μ := by
  have h := integral_ofReal (𝕜 := ℂ) (μ := μ) (f := f)
  simpa using congrArg Complex.re h

lemma bench_characteristic_re (F : Scalar) (n : ℕ) (z : Fin (n+1) → F.K) :
    (charFunK (benchLaw F (n+1)) benchVec z).re =
      ∫ γ : Fin n → ℝ, Real.exp (-gammaPi γ*(∑ i, ‖z i‖^2)/(2*(F.beta : ℝ)))
        ∂gammaVec F n := by
  rw [bench_characteristic, re_integral_ofReal]

lemma integrable_exp_gamma_product (F : Scalar) (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p : ℝ × (Fin (m+1) → ℝ) => Real.exp (-s*gammaPi p.2*p.1))
      ((gammaLaw F (m+2)).prod (gammaVec F (m+1))) := by
  have hγ : ∀ᵐ p ∂(gammaLaw F (m+2)).prod (gammaVec F (m+1)), 0 ≤ gammaPi p.2 :=
    (measurePreserving_snd (μ := gammaLaw F (m+2)) (ν := gammaVec F (m+1))).quasiMeasurePreserving.ae
      (gammaPi_ae_nonneg F (m+1))
  have hx : ∀ᵐ p ∂(gammaLaw F (m+2)).prod (gammaVec F (m+1)), 0 ≤ p.1 :=
    (measurePreserving_fst (μ := gammaLaw F (m+2)) (ν := gammaVec F (m+1))).quasiMeasurePreserving.ae
      (gammaMeasure_ae_nonneg _ _)
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · have h := measurable_gammaPi (m+1)
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [hγ, hx] with p hγ hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hγ) hx

lemma bench_norm_laplace (F : Scalar) (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ p, Real.exp (-s*(∑ i, ‖(benchVec (F := F) (n := m+2) p) i‖^2))
      ∂benchLaw F (m+2)) =
    ∫ γ, Real.exp (-s*gammaPi γ) ∂gammaVec F (m+2) := by
  let g := fun p : (Fin (m+1) → ℝ) × (Fin (m+2) → F.K) =>
    Real.exp (-s*gammaPi p.1*(∑ i, ‖p.2 i‖^2))
  have hg : Measurable g := by
    have h := measurable_gammaPi (m+1)
    unfold g
    fun_prop
  have hi : Integrable g ((gammaVec F (m+1)).prod (gaussVec F (m+2))) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hg.aestronglyMeasurable
    filter_upwards [gammaPi_nonneg_prod F (m+1) (gaussVec F (m+2))] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hp) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  calc
    _ = ∫ p, g p ∂(gammaVec F (m+1)).prod (gaussVec F (m+2)) := by
      apply integral_congr_ae
      filter_upwards [gammaPi_nonneg_prod F (m+1) (gaussVec F (m+2))] with p hp
      unfold benchVec
      rw [norm_smul_sum_sq, Real.sq_sqrt hp]
      dsimp [g]
      congr 1
      ring
    _ = ∫ γ, ∫ x : Fin (m+2) → F.K, Real.exp (-(s*gammaPi γ)*(∑ i, ‖x i‖^2))
        ∂gaussVec F (m+2) ∂gammaVec F (m+1) := by simpa only [g, neg_mul] using integral_prod g hi
    _ = ∫ γ, ∫ x : ℝ, Real.exp (-(s*gammaPi γ)*x)
        ∂gammaLaw F (m+2) ∂gammaVec F (m+1) := by
      apply integral_congr_ae
      filter_upwards [gammaPi_ae_nonneg F (m+1)] with γ hγ
      exact gaussVec_norm_gamma_laplace F (m+2) (by omega) (s*gammaPi γ) (mul_nonneg hs hγ)
    _ = _ := by
      rw [gammaPi_integral_split_last]
      simpa only [neg_mul] using (integral_prod_symm _ (integrable_exp_gamma_product F m s hs)).symm

end GinibrePermanent977.Anticoncentration
-- Solutions/PermanentAlgebra.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma perK_columns_perm {K : Type*} [Ring K] {n : ℕ}
    (A : Fin n → Fin n → K) (τ : Equiv.Perm (Fin n)) :
    perK (fun i j => A i (τ j)) = perK A := by
  unfold perK
  simpa only [Equiv.Perm.mul_apply] using
    (Group.mulLeft_bijective τ).sum_comp (fun σ : Equiv.Perm (Fin n) =>
      (List.ofFn fun i => A i (σ i)).prod)

lemma continuous_ordered_product {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [Monoid K] [ContinuousMul K] {n : ℕ} (f : Fin n → X → K)
    (hf : ∀ i, Continuous (f i)) : Continuous (fun x => (List.ofFn fun i => f i x).prod) := by
  induction n with
  | zero => simpa using (continuous_const : Continuous (fun _ : X => (1 : K)))
  | succ n ih =>
    simp_rw [List.ofFn_succ, List.prod_cons]
    exact (hf 0).mul (ih (fun i => f i.succ) (fun i => hf i.succ))

lemma continuous_perK {K : Type*} [NormedRing K] {n : ℕ} :
    Continuous (perK : (Fin n → Fin n → K) → K) := by
  unfold perK
  apply continuous_finset_sum
  intro σ _
  exact continuous_ordered_product (fun i (A : Fin n → Fin n → K) => A i (σ i)) (by intro i; fun_prop)

lemma perK_succ_first_row {K : Type*} [Ring K] {n : ℕ}
    (A : Fin (n+1) → Fin (n+1) → K) :
    perK A = ∑ j : Fin (n+1), A 0 j * perK (fun i k => A i.succ (j.succAbove k)) := by
  unfold perK
  rw [Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  simp only [List.ofFn_succ, List.prod_cons,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  rw [← Finset.mul_sum]
  congr 1
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Equiv.swap_self, Equiv.coe_refl, Fin.succAbove_zero, id_eq]
  · have h := perK_columns_perm (fun i k : Fin n => A i.succ (j.succ.succAbove k)) (Fin.cycleRange j)
    unfold perK at h
    rw [← h]
    simp only [Fin.succAbove_cycleRange]

lemma skipCol_succAbove {n : ℕ} (j : Fin (n+1)) (k : Fin n) :
    skipCol j k = j.succAbove k := by
  apply Fin.ext
  simp only [skipCol, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

lemma perK_cons_row {K : Type*} [Ring K] {n : ℕ}
    (w : Fin (n+1) → K) (B : Fin n → Fin (n+1) → K) :
    perK (Fin.cons w B) = ∑ j, w j * perCofactor (n := n+1) B j := by
  rw [perK_succ_first_row]
  simp only [Fin.cons_zero, Fin.cons_succ]
  change (∑ j, w j * perK (fun i k => B i (j.succAbove k))) =
    ∑ j, w j * perK (fun i k => B i (skipCol j k))
  simp_rw [skipCol_succAbove]

lemma perCofactor_columns_perm {K : Type*} [Ring K] {n : ℕ}
    (B : Fin n → Fin (n+1) → K) (τ : Equiv.Perm (Fin (n+1))) (j : Fin (n+1)) :
    perCofactor (n := n+1) (fun i k => B i (τ k)) j = perCofactor (n := n+1) B (τ j) := by
  classical
  have h := perK_columns_perm (Fin.cons (Pi.single (τ j) (1 : K)) B) τ
  have hf : (fun (i k : Fin (n+1)) => (Fin.cons (Pi.single (τ j) (1 : K)) B : Fin (n+1) → Fin (n+1) → K) i (τ k)) =
      Fin.cons (Pi.single j (1 : K)) (fun i k => B i (τ k)) := by
    funext i k
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Pi.single_apply, τ.injective.eq_iff]
    · rfl
  rw [hf, perK_cons_row, perK_cons_row] at h
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  convert h using 1
  rfl

lemma perK_columns_multilinear {R K : Type*} [CommSemiring R] [Ring K] [Algebra R K] (n : ℕ) :
    ∃ P : MultilinearMap R (fun _ : Fin n => Fin n → K) K,
      ∀ cols : Fin n → Fin n → K, P cols = perK (fun i j => cols j i) := by
  let P : MultilinearMap R (fun _ : Fin n => Fin n → K) K :=
    ∑ σ : Equiv.Perm (Fin n),
      ((MultilinearMap.mkPiAlgebraFin R n K).domDomCongr σ).compLinearMap
        (fun j => LinearMap.proj (σ.symm j))
  refine ⟨P, fun cols => ?_⟩
  simp [P, perK, MultilinearMap.domDomCongr_apply]

lemma perK_rows_multilinear {R K : Type*} [CommSemiring R] [Ring K] [Algebra R K] (n : ℕ) :
    ∃ P : MultilinearMap R (fun _ : Fin n => Fin n → K) K,
      ∀ rows : Fin n → Fin n → K, P rows = perK rows := by
  let P : MultilinearMap R (fun _ : Fin n => Fin n → K) K :=
    ∑ σ : Equiv.Perm (Fin n),
      (MultilinearMap.mkPiAlgebraFin R n K).compLinearMap
        (fun i => LinearMap.proj (σ i))
  refine ⟨P, fun rows => ?_⟩
  simp [P, perK]

lemma perCofactor_rows_multilinear {K : Type*} [Ring K] [Algebra ℝ K] (n : ℕ)
    (l : Fin n → K →ₗ[ℝ] ℝ) :
    ∃ H : MultilinearMap ℝ (fun _ : Fin (n-1) => Fin n → K) ℝ,
      ∀ B : Fin (n-1) → Fin n → K, H B = ∑ j, l j (perCofactor B j) := by
  obtain ⟨P, hP⟩ := perK_rows_multilinear (R := ℝ) (K := K) (n-1)
  let r (j : Fin n) : (Fin n → K) →ₗ[ℝ] (Fin (n-1) → K) :=
    LinearMap.pi (fun k => LinearMap.proj (skipCol j k))
  let H : MultilinearMap ℝ (fun _ : Fin (n-1) => Fin n → K) ℝ :=
    ∑ j, (l j).compMultilinearMap (P.compLinearMap (fun _ => r j))
  refine ⟨H, fun B => ?_⟩
  simp only [H, _root_.sum_apply, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
  simp_rw [hP]
  rfl

lemma perK_cons_column_linear {K : Type*} [Ring K] [Algebra ℝ K] {n : ℕ}
    (R : Fin (n+1) → Fin n → K) :
    ∃ L : (Fin (n+1) → K) →ₗ[ℝ] K,
      ∀ X, L X = perK (fun i => Fin.cons (X i) (R i)) := by
  obtain ⟨P, hP⟩ := perK_columns_multilinear (R := ℝ) (K := K) (n+1)
  let L : (Fin (n+1) → K) →ₗ[ℝ] K :=
    { toFun := fun X => P (Fin.cons X (fun j i => R i j))
      map_add' := by intro X Y; exact MultilinearMap.cons_add P _ X Y
      map_smul' := by intro r X; exact MultilinearMap.cons_smul P _ r X }
  refine ⟨L, fun X => ?_⟩
  rw [show L X = P (Fin.cons X (fun j i => R i j)) from rfl, hP]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

lemma perK_cons_two_columns_bilinear {K : Type*} [Ring K] [Algebra ℝ K] {n : ℕ}
    (R : Fin (n+2) → Fin n → K) :
    ∃ Q : (Fin (n+2) → K) →ₗ[ℝ] (Fin (n+2) → K) →ₗ[ℝ] K,
      ∀ X Y, Q X Y = perK (fun i => Fin.cons (X i) (Fin.cons (Y i) (R i))) := by
  obtain ⟨P, hP⟩ := perK_columns_multilinear (R := ℝ) (K := K) (n+2)
  let Q := LinearMap.mk₂ ℝ
    (fun X Y => P (Fin.cons X (Fin.cons Y (fun j i => R i j))))
    (fun X X' Y => MultilinearMap.cons_add P _ X X')
    (fun r X Y => MultilinearMap.cons_smul P _ r X)
    (fun X Y Y' => MultilinearMap.cons_add (P.curryLeft X) _ Y Y')
    (fun r X Y => MultilinearMap.cons_smul (P.curryLeft X) _ r Y)
  refine ⟨Q, fun X Y => ?_⟩
  rw [show Q X Y = P (Fin.cons X (Fin.cons Y (fun j i => R i j))) from rfl, hP]
  congr 1
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl

end GinibrePermanent977.Anticoncentration


-- Solutions/CofactorPositivity.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GinibrePermanent977.Anticoncentration

lemma gaussian_multilinear_characteristic_nonneg (F : Scalar) {m n : ℕ}
    (P : MultilinearMap ℝ (fun _ : Fin (m+1) => Fin n → F.K) ℝ) (hP : Continuous P) :
    0 ≤ (∫ B, Complex.exp (Complex.I * ((P B : ℝ) : ℂ)) ∂ginibre F (m+1) n) := by
  haveI : SecondCountableTopology F.K := by
    cases F
    · exact inferInstanceAs (SecondCountableTopology ℝ)
    · exact inferInstanceAs (SecondCountableTopology ℂ)
    · exact inferInstanceAs (SecondCountableTopology ℍ[ℝ])
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  change 0 ≤ (∫ B, Complex.exp (Complex.I * ((P B : ℝ) : ℂ))
    ∂Measure.pi (fun _ : Fin (m+1) => gaussVec F n))
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => gaussVec F n) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Fin.zero_succAbove, Function.comp_def]
  have hPm : Measurable P := hP.measurable
  have hcons : Measurable (fun p : (Fin n → F.K) × (Fin m → Fin n → F.K) => (Fin.cons p.1 p.2 : Fin (m+1) → Fin n → F.K)) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd
  let f := fun p : (Fin n → F.K) × (Fin m → Fin n → F.K) =>
    Complex.exp (Complex.I * ((P (Fin.cons p.1 p.2) : ℝ) : ℂ))
  have hi : Integrable f ((gaussVec F n).prod (Measure.pi fun _ : Fin m => gaussVec F n)) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.aestronglyMeasurable (by dsimp [f]; fun_prop))
    exact Filter.Eventually.of_forall (fun p => by simp [f, Complex.norm_exp])
  change 0 ≤ ∫ p, f p ∂(gaussVec F n).prod (Measure.pi fun _ : Fin m => gaussVec F n)
  rw [integral_prod_symm _ hi]
  have hnn (R : Fin m → Fin n → F.K) : 0 ≤ ∫ x, f (x,R) ∂gaussVec F n := by
    let l := P.toLinearMap (Fin.cons 0 R) 0
    have he (x : Fin n → F.K) : P (Fin.cons x R) = l x := by
      change P (Fin.cons x R) = P (Function.update (Fin.cons 0 R) 0 x)
      congr 1
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    simpa only [f, he] using vector_scalar_gaussian_linear_nonneg F l
  have ho := hi.integral_prod_right
  have hr : (∫ R, ∫ x, f (x,R) ∂gaussVec F n ∂Measure.pi (fun _ : Fin m => gaussVec F n)).re =
      ∫ R, (∫ x, f (x,R) ∂gaussVec F n).re ∂Measure.pi (fun _ : Fin m => gaussVec F n) :=
    (integral_re ho).symm
  have him : (∫ R, ∫ x, f (x,R) ∂gaussVec F n ∂Measure.pi (fun _ : Fin m => gaussVec F n)).im =
      ∫ R, (∫ x, f (x,R) ∂gaussVec F n).im ∂Measure.pi (fun _ : Fin m => gaussVec F n) :=
    (integral_im ho).symm
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [hr]
    apply integral_nonneg
    intro R
    exact (Complex.nonneg_iff.mp (hnn R)).1
  · rw [him]
    have hzero (R : Fin m → Fin n → F.K) : (∫ x, f (x,R) ∂gaussVec F n).im = 0 :=
      (Complex.nonneg_iff.mp (hnn R)).2.symm
    simp only [hzero, integral_zero]

lemma continuous_perCofactor {K : Type*} [NormedRing K] {n : ℕ} :
    Continuous (perCofactor : (Fin (n-1) → Fin n → K) → Fin n → K) := by
  apply continuous_pi
  intro j
  exact continuous_perK.comp (by unfold minor; fun_prop)

lemma perCofactor_characteristic_nonnegative (F : Scalar) {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → F.K) : 0 ≤ charFunK (ginibre F (n-1) n) perCofactor z := by
  have hsmul₁ (r : ℝ) (x y : F.K) : (r • x)*y = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        smul_mul_assoc r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)
  have hsmul₂ (r : ℝ) (x y : F.K) : x*(r • y) = r • (x*y) := by
    cases F
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℝ from x) (show ℝ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℂ from x) (show ℂ from y)
    · simpa only [Scalar.K, Scalar.instNormedRing, Scalar.instInnerProductSpace] using
        mul_smul_comm r (show ℍ[ℝ] from x) (show ℍ[ℝ] from y)
  letI : Algebra ℝ F.K := Algebra.ofModule hsmul₁ hsmul₂
  obtain ⟨H,hH⟩ := perCofactor_rows_multilinear (K := F.K) n
    (fun j => (innerSL ℝ (z j)).toLinearMap)
  have hHeq (B : Fin (n-1) → Fin n → F.K) : H B = realInner z (perCofactor B) := hH B
  have hcont : Continuous H := by
    have heq : (H : (Fin (n-1) → Fin n → F.K) → ℝ) = fun B => realInner z (perCofactor B) :=
      funext hHeq
    rw [heq]
    unfold realInner
    apply continuous_finsetSum
    intro j _
    exact continuous_const.inner (continuous_apply j |>.comp continuous_perCofactor)
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  have hHpoint (B : Fin (m+1) → Fin (m+2) → F.K) :
      H B = realInner z (perCofactor (n := m+2) B) := hHeq B
  have hp := gaussian_multilinear_characteristic_nonneg F H hcont
  have heq : (∫ B : Fin (m+1) → Fin (m+2) → F.K,
      Complex.exp (Complex.I * ((H B : ℝ) : ℂ)) ∂ginibre F (m+1) (m+2)) =
      charFunK (ginibre F (m+2-1) (m+2)) perCofactor z := by
    unfold charFunK
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro B
    exact congrArg (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) (hHpoint B)
  exact hp.trans_eq heq

end GinibrePermanent977.Anticoncentration
-- Solutions/GaussianRow.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma scalar_inner_mul_right (F : Scalar) (z x c : F.K) :
    inner ℝ z (x*c) = inner ℝ (z*star c) x := by
  cases F
  · dsimp only [Scalar.K] at z x c ⊢
    simp [RCLike.inner_apply, mul_assoc, mul_comm, mul_left_comm]
  · dsimp only [Scalar.K] at z x c ⊢
    simp [real_inner_eq_re_inner, RCLike.inner_apply, star_mul, mul_assoc,
      mul_comm, mul_left_comm]
  · dsimp only [Scalar.K] at z x c ⊢
    simp [Quaternion.inner_def, star_mul, mul_assoc]

lemma scalar_norm_mul_star (F : Scalar) (z c : F.K) : ‖z*star c‖ = ‖z‖*‖c‖ := by
  cases F <;> dsimp only [Scalar.K] at z c ⊢
  · exact (norm_mul z (star c)).trans (congrArg (fun r : ℝ => ‖z‖*r) (norm_star c))
  · exact (norm_mul z (star c)).trans (congrArg (fun r : ℝ => ‖z‖*r) (norm_star c))
  · exact (norm_mul z (star c)).trans (congrArg (fun r : ℝ => ‖z‖*r) (norm_star c))

lemma gaussian_row_characteristic (F : Scalar) {n : ℕ} (C : Fin n → F.K) (z : F.K) :
    (∫ g : Fin n → F.K, Complex.exp (Complex.I * ((inner ℝ z (∑ j, g j*C j) : ℝ) : ℂ))
      ∂gaussVec F n) =
    (Real.exp (-‖z‖^2*(∑ j, ‖C j‖^2)/(2*(F.beta : ℝ))) : ℂ) := by
  have he (g : Fin n → F.K) : inner ℝ z (∑ j, g j*C j) =
      realInner (fun j => z*star (C j)) g := by
    simp only [inner_sum, realInner, scalar_inner_mul_right]
  simp_rw [he]
  rw [vector_scalar_gaussian_characteristic]
  congr 3
  simp only [scalar_norm_mul_star, mul_pow]
  rw [← Finset.mul_sum]
  ring

lemma permanent_characteristic_first_row (F : Scalar) {n : ℕ} (z : F.K) :
    (∫ G : Fin (n+1) → Fin (n+1) → F.K,
      Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ)) ∂ginibre F (n+1) (n+1)) =
    ∫ B : Fin n → Fin (n+1) → F.K,
      (Real.exp (-‖z‖^2*(∑ j, ‖perCofactor (n := n+1) B j‖^2)/(2*(F.beta : ℝ))) : ℂ)
      ∂ginibre F n (n+1) := by
  haveI : SecondCountableTopology F.K := by
    cases F
    · exact inferInstanceAs (SecondCountableTopology ℝ)
    · exact inferInstanceAs (SecondCountableTopology ℂ)
    · exact inferInstanceAs (SecondCountableTopology ℍ[ℝ])
  haveI : IsProbabilityMeasure (gaussVec F (n+1)) := by unfold gaussVec; infer_instance
  change (∫ G, Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ))
      ∂Measure.pi (fun _ : Fin (n+1) => gaussVec F (n+1))) = _
  have hsplit := (measurePreserving_piFinSuccAbove (n := n)
    (α := fun _ : Fin (n+1) => Fin (n+1) → F.K)
    (fun _ : Fin (n+1) => gaussVec F (n+1)) 0).symm
  have hsplitIntegral := hsplit.integral_comp'
    (fun G : Fin (n+1) → Fin (n+1) → F.K =>
      Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ)))
  rw [← hsplitIntegral]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero,
    Fin.zero_succAbove]
  have hcons : Measurable (fun p : (Fin (n+1) → F.K) × (Fin n → Fin (n+1) → F.K) =>
      (Fin.cons p.1 p.2 : Fin (n+1) → Fin (n+1) → F.K)) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd
  have hPm : Measurable (perK : (Fin (n+1) → Fin (n+1) → F.K) → F.K) := continuous_perK.measurable
  let f := fun p : (Fin (n+1) → F.K) × (Fin n → Fin (n+1) → F.K) =>
    Complex.exp (Complex.I * ((inner ℝ z (perK (Fin.cons p.1 p.2)) : ℝ) : ℂ))
  have hi : Integrable f ((gaussVec F (n+1)).prod (Measure.pi fun _ : Fin n => gaussVec F (n+1))) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.aestronglyMeasurable (by dsimp [f]; fun_prop))
    exact Filter.Eventually.of_forall (fun p => by simp [f, Complex.norm_exp])
  change (∫ p, f p ∂(gaussVec F (n+1)).prod (Measure.pi fun _ : Fin n => gaussVec F (n+1))) = _
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro B
  dsimp only [f]
  simp_rw [perK_cons_row]
  exact gaussian_row_characteristic F (perCofactor (n := n+1) B) z

end GinibrePermanent977.Anticoncentration

-- Solutions/GinibreMaps.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
set_option autoImplicit false
namespace GinibrePermanent977.Anticoncentration

lemma measurePreserving_delete_coordinate (F : Scalar) {n : ℕ} (j : Fin (n+1)) :
    MeasurePreserving (fun x : Fin (n+1) → F.K => fun k : Fin n => x (skipCol j k))
      (gaussVec F (n+1)) (gaussVec F n) := by
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussian F) j
  have hsnd := (measurePreserving_snd (μ := gaussian F)
    (ν := Measure.pi (fun _ : Fin n => gaussian F))).comp hsplit
  change MeasurePreserving _ (Measure.pi (fun _ : Fin (n+1) => gaussian F))
    (Measure.pi (fun _ : Fin n => gaussian F))
  convert hsnd using 1
  ext x k
  rw [skipCol_succAbove]
  rfl

lemma measurePreserving_minor (F : Scalar) {n : ℕ} (j : Fin (n+1)) :
    MeasurePreserving (fun B : Fin n → Fin (n+1) → F.K => minor (n := n+1) B j)
      (ginibre F n (n+1)) (ginibre F n n) := by
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  have h := measurePreserving_pi (fun _ : Fin n => gaussVec F (n+1))
    (fun _ : Fin n => gaussVec F n) (fun _ => measurePreserving_delete_coordinate F j)
  exact h

lemma measurePreserving_ginibre_columns_perm (F : Scalar) {m n : ℕ}
    (τ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun B : Fin m → Fin n → F.K => fun i j => B i (τ j))
      (ginibre F m n) (ginibre F m n) := by
  haveI : IsProbabilityMeasure (gaussVec F n) := by unfold gaussVec; infer_instance
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => gaussian F) τ.symm
  have hrow : MeasurePreserving (fun x : Fin n → F.K => fun j => x (τ j))
      (gaussVec F n) (gaussVec F n) := by
    change MeasurePreserving _ (Measure.pi (fun _ : Fin n => gaussian F))
      (Measure.pi (fun _ : Fin n => gaussian F))
    convert h using 1
    ext x j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  exact measurePreserving_pi (fun _ : Fin m => gaussVec F n)
    (fun _ : Fin m => gaussVec F n) (fun _ => hrow)

end GinibrePermanent977.Anticoncentration
-- Solutions/CofactorEndpoint.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder Quaternion RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma cofactor_characteristic_single (F : Scalar) {n : ℕ} (j : Fin (n+1)) (z : F.K) :
    charFunK (ginibre F n (n+1)) (perCofactor (n := n+1)) (Pi.single j z) =
    ∫ G : Fin n → Fin n → F.K,
      Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ)) ∂ginibre F n n := by
  haveI : SecondCountableTopology F.K := by
    cases F
    · exact inferInstanceAs (SecondCountableTopology ℝ)
    · exact inferInstanceAs (SecondCountableTopology ℂ)
    · exact inferInstanceAs (SecondCountableTopology ℍ[ℝ])
  have h := measurePreserving_minor F j
  let g := fun G : Fin n → Fin n → F.K =>
    Complex.exp (Complex.I * ((inner ℝ z (perK G) : ℝ) : ℂ))
  have hPm : Measurable (perK : (Fin n → Fin n → F.K) → F.K) := continuous_perK.measurable
  have hg : Measurable g := by dsimp [g]; fun_prop
  have he := (integral_map h.aemeasurable hg.aestronglyMeasurable).symm
  rw [h.map_eq] at he
  unfold charFunK
  have hsingle (B : Fin n → Fin (n+1) → F.K) :
      realInner (Pi.single j z) (perCofactor B) = inner ℝ z (perK (minor (n := n+1) B j)) := by
    unfold realInner
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
      rfl
    · intro k hk hkj
      rw [Pi.single_eq_of_ne hkj]
      exact inner_zero_left _
    · simp
  simp_rw [hsingle]
  exact he

lemma cofactor_characteristic_single_recurrence (F : Scalar) {n : ℕ}
    (j : Fin (n+2)) (z : F.K) :
    charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2)) (Pi.single j z) =
    ∫ B : Fin n → Fin (n+1) → F.K,
      (Real.exp (-‖z‖^2*(∑ k, ‖perCofactor (n := n+1) B k‖^2)/(2*(F.beta : ℝ))) : ℂ)
      ∂ginibre F n (n+1) := by
  rw [cofactor_characteristic_single]
  exact permanent_characteristic_first_row F z

end GinibrePermanent977.Anticoncentration
-- Solutions/ScalarInduction.lean
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace ComplexOrder Quaternion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma norm2_sq (F : Scalar) {n : ℕ} (x : Fin n → F.K) :
    norm2 x ^ 2 = ∑ i, ‖x i‖^2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))

lemma scalar_norm_unit (F : Scalar) : ‖(1 : F.K)‖ = 1 := by
  cases F
  · exact (norm_one : ‖(1 : ℝ)‖ = 1)
  · exact (norm_one : ‖(1 : ℂ)‖ = 1)
  · exact (norm_one : ‖(1 : ℍ[ℝ])‖ = 1)

lemma cofactor_one_norm_sq (F : Scalar) (B : Fin 0 → Fin 1 → F.K) :
    norm2 (perCofactor (n := 1) B) ^ 2 = 1 := by
  rw [norm2_sq]
  simp [perCofactor, perK, List.ofFn_zero, scalar_norm_unit]

lemma cofactor_fourier_of_scalar_laplace (F : Scalar) (n : ℕ)
    (ih : StochasticOrders.LaplaceTransform.LaplaceOrder (gammaVec F (n+1))
      (ginibre F n (n+1)) gammaPi (fun B => norm2 (perCofactor (n := n+1) B)^2))
    (z : Fin (n+2) → F.K) :
    (charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2)) z).re ≤
      (charFunK (benchLaw F (n+2)) benchVec z).re := by
  let t := (∑ i, ‖z i‖^2)/(2*(F.beta : ℝ))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hih : (∫ B, Real.exp (-t*(∑ i, ‖perCofactor (n := n+1) B i‖^2)) ∂ginibre F n (n+1)) ≤
      ∫ γ, Real.exp (-t*gammaPi γ) ∂gammaVec F (n+1) := by
    by_cases hzero : t = 0
    · simp [hzero]
    · have h := ih t (lt_of_le_of_ne ht (Ne.symm hzero))
      simpa only [norm2_sq, neg_mul] using h
  have hc := (Complex.le_def.mp (proposition_3_5_fourier_compression F (by omega) z).2).1
  apply hc.trans
  change (charFunK (ginibre F (n+1) (n+2)) (perCofactor (n := n+2))
    (Pi.single 0 (norm2 z • (1 : F.K)))).re ≤ _
  rw [cofactor_characteristic_single_recurrence, re_integral_ofReal, bench_characteristic_re]
  have hnorm : ‖norm2 z • (1 : F.K)‖^2 = ∑ i, ‖z i‖^2 := by
    rw [norm_smul, scalar_norm_unit, mul_one, Real.norm_eq_abs, sq_abs, norm2_sq]
  rw [hnorm]
  convert hih using 1 <;> congr 1 <;> funext x <;> congr 1 <;> dsimp [t] <;> ring

lemma cofactor_scalar_laplace (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    StochasticOrders.LaplaceTransform.LaplaceOrder (gammaVec F n) (ginibre F (n-1) n)
      gammaPi (fun B => norm2 (perCofactor (n := n) B)^2) := by
  refine Nat.le_induction ?_ ?_ n hn
  · intro s hs
    have hp (γ : Fin 1 → ℝ) : gammaPi γ = 1 := by simp [gammaPi]
    simp only [cofactor_one_norm_sq, hp]
    simp
  · intro k hk ih
    obtain ⟨m,rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
    intro s hs
    haveI : IsProbabilityMeasure (benchLaw F (m+2)) := by unfold benchLaw; infer_instance
    have hC : Measurable (perCofactor (n := m+2) :
      (Fin (m+1) → Fin (m+2) → F.K) → Fin (m+2) → F.K) := continuous_perCofactor.measurable
    have h := isotropic_fourier_laplace F (ginibre F (m+1) (m+2)) (benchLaw F (m+2))
      (perCofactor (n := m+2)) benchVec hC (benchVec_measurable F (m+2))
      (cofactor_fourier_of_scalar_laplace F m ih) s hs.le
    rw [bench_norm_laplace F m s hs.le] at h
    change (∫ B : Fin (m+1) → Fin (m+2) → F.K, Real.exp (-(s*norm2 (perCofactor (n := m+2) B)^2))
      ∂ginibre F (m+1) (m+2)) ≤ ∫ γ : Fin (m+2) → ℝ, Real.exp (-(s*gammaPi γ)) ∂gammaVec F (m+2)
    simpa only [norm2_sq, neg_mul] using h

end GinibrePermanent977.Anticoncentration
-- Solutions/ScalarComparisonSolution.lean
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal
open GinibrePermanent977.Anticoncentration

theorem solution (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    StochasticOrders.LaplaceTransform.LaplaceOrder (gammaVec F n) (ginibre F (n-1) n)
      gammaPi (fun B => norm2 (perCofactor (n := n) B)^2) :=
  cofactor_scalar_laplace F n hn
