-- Prove2me | solution 1 for OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:48:10.175711+00:00
-- url     : https://prove2.me/submissions/b38cff41-d9ea-4ecc-a35a-4e64e1467938

import Mathlib
import Definitions.Def_OAIQ6El001

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal smooth polynomial amplitudes in boundary coordinates, including
actual Frechet derivatives and polynomial growth. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace ElasticityBoundaryMVCalculus

lemma differential_mul_X (p : MP) (j : Fin 3) (y : Y) :
    differential (p*X j) y = value p y • complexCoord j + (y j : ℂ) • differential p y := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [differential, pderiv_mul, value_add, value_mul, pderiv_X, Pi.single_apply,
    sum_apply, add_apply,
    smul_apply, complexCoord_apply, smul_eq_mul]
  simp only [value_X, add_mul, Finset.sum_add_distrib]
  have h (i : Fin 3) : value (if j=i then 1 else 0 : MP) y = if j=i then 1 else 0 := by
    split_ifs <;> simp
  simp only [h, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The evaluated formal partial derivatives are the actual Frechet derivative. -/
theorem hasFDerivAt_value (p : MP) (y : Y) : HasFDerivAt (value p) (differential p y) y := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [value_C_fn, differential_C]; exact hasFDerivAt_const c y
  | add p q hp hq => rw [value_add_fn, differential_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [value_mul_fn, value_X_fn, differential_mul_X]
      exact hp.mul ((complexCoord i).hasFDerivAt (x := y))

lemma differential_basis (p : MP) (y : Y) (i : Fin 3) :
    differential p y (Pi.single i 1) = value (pderiv i p) y := by
  simp [differential, Pi.single_apply, apply_ite Complex.ofReal, mul_ite]

end ElasticityBoundaryMVCalculus

end
end
section
/-! Exact anisotropic boundary scaling, retaining the physical dimension-three
Jacobian δ⁴. No asymptotic change-of-variable formula is postulated. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryScaling

lemma scale_comp (δ ε : ℝ) (y : Y) : scale δ (scale ε y) = scale (δ*ε) y := by
  ext i
  simp only [scale_apply, scaleFactor]
  split_ifs <;> ring

end ElasticityBoundaryScaling

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundarySymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal anisotropic oscillatory Gaussian boundary profiles, with actual
Frechet derivatives.  The small parameter is never assigned a symbolic DN map. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryProfile
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights

lemma conjugateDerivative_apply (δ : ℝ) (j : Fin 3) (p : MP) :
    conjugateDerivative δ j p=pderiv j p+pderiv j (phase δ)*p := rfl

/-- Each formal conjugated partial is exactly the Frechet derivative of the
actual function in a coordinate direction. -/
theorem fderiv_profile_basis (δ : ℝ) (p : MP) (y : Y) (j : Fin 3) :
    fderiv ℝ (profile δ p) y (Pi.single j 1)=profile δ (conjugateDerivative δ j p) y := by
  have h := ((hasFDerivAt_value (phase δ) y).cexp).mul (hasFDerivAt_value p y)
  change HasFDerivAt (profile δ p) _ y at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, differential_basis]
  simp only [profile, envelope, conjugateDerivative_apply, value_add, value_mul]
  ring

lemma phase_partial (δ : ℝ) (j : Fin 3) : pderiv j (phase δ) =
    ![C (Complex.I/(δ:ℂ))-(2:ℂ) • X 0, -(2:ℂ) • X 1, -1] j := by
  fin_cases j <;>
    simp [phase, smul_eq_C_mul] <;> ring_nf <;> exact (map_natCast C 2).symm

lemma conjugate_zero (δ : ℝ) (p : MP) :
    conjugateDerivative δ 0 p = (Complex.I/(δ:ℂ)) • p +
      (pderiv 0 p-(2:ℂ) • (X 0*p)) := by
  simp [conjugateDerivative_apply, phase_partial, smul_eq_C_mul]
  ring

lemma conjugate_one (δ : ℝ) (p : MP) :
    conjugateDerivative δ 1 p = pderiv 1 p-(2:ℂ) • (X 1*p) := by
  simp [conjugateDerivative_apply, phase_partial, smul_eq_C_mul]
  ring

lemma conjugate_two (δ : ℝ) (p : MP) :
    conjugateDerivative δ 2 p = pderiv 2 p-p := by
  simp [conjugateDerivative_apply, phase_partial, sub_eq_add_neg]

lemma D_eq_scaled {δ : ℝ} (hδ : δ≠0) (j : Fin 3) (p : MP) :
    D δ j p = ((δ^2*scaleFactor δ⁻¹ j : ℝ):ℂ) • conjugateDerivative δ j p := by
  have hs : δ^2*scaleFactor δ⁻¹ j = if j=2 then 1 else δ := by
    unfold scaleFactor
    split_ifs <;> field_simp
  rw [hs]
  have hc : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  have hid : (δ:ℂ)*(Complex.I/(δ:ℂ))=Complex.I := by field_simp
  fin_cases j <;> simp [D, conjugate_zero, conjugate_one, conjugate_two,
    smul_add, smul_smul, hid]

lemma scale_basis (δ : ℝ) (j : Fin 3) :
    scale δ (Pi.single j 1)=scaleFactor δ j • (Pi.single j 1) := by
  ext i
  by_cases hi : i=j
  · subst i; simp
  · simp [hi]

/-- The true derivative in unscaled boundary coordinates. -/
theorem fderiv_physicalProfile_basis {δ : ℝ} (hδ : δ≠0) (p : MP) (z : Y) (j : Fin 3) :
    fderiv ℝ (physicalProfile δ p) z (Pi.single j 1) =
      ((δ^2)⁻¹:ℝ) • physicalProfile δ (D δ j p) z := by
  change fderiv ℝ (profile δ p ∘ scale δ⁻¹) z _=_
  rw [fderiv_comp z ((smooth_profile δ p).differentiable (by simp)).differentiableAt
    (scale δ⁻¹).differentiableAt, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply, scale_basis, map_smul,
    fderiv_profile_basis, D_eq_scaled hδ]
  simp only [physicalProfile, profile, value_smul, Complex.real_smul]
  have hc : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  push_cast
  field_simp

end ElasticityBoundaryProfile

end
end
section
/-! Coefficientwise linear differential operators in a genuine finite
parameter polynomial. Used to construct, not postulate, Taylor transport
coefficients of the physical boundary layer. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryParameter
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

lemma eval_coeffMap (T : A →ₗ[ℂ] B) (q : Polynomial A) (c : ℂ) :
    (coeffMap T q).eval (algebraMap ℂ B c)=T (q.eval (algebraMap ℂ A c)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial n a =>
      rw [coeffMap_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
      simp only [← map_pow]
      rw [mul_comm, ← Algebra.smul_def, mul_comm a, ← Algebra.smul_def, T.map_smul]

lemma D_expansion (δ : ℝ) (j : Fin 3) : D δ j = E₀ j+(δ:ℂ) • E₁ j := by
  fin_cases j <;> simp [D,E₀,E₁]

lemma PD_apply (j : Fin 3) (q : Polynomial MP) :
    PD j q=coeffMap (E₀ j) q+Polynomial.X*coeffMap (E₁ j) q := rfl

lemma eval_PD (j : Fin 3) (q : Polynomial MP) (δ : ℝ) :
    (PD j q).eval (C (δ:ℂ)) = D δ j (q.eval (C (δ:ℂ))) := by
  rw [PD_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  have hC : C (δ:ℂ) = algebraMap ℂ MP (δ:ℂ) := rfl
  rw [hC, eval_coeffMap, eval_coeffMap, D_expansion]
  change _ = E₀ j (q.eval (algebraMap ℂ MP (δ:ℂ))) +
    (δ:ℂ) • E₁ j (q.eval (algebraMap ℂ MP (δ:ℂ)))
  rw [Algebra.smul_def]

end ElasticityBoundaryParameter

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Honest L2 bounds and exact change of variables for physical boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryProfileBounds
open ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
  ElasticityBoundaryProfile

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma physicalProfile_scale {δ : ℝ} (hδ : δ≠0) (p : MP) (y : Y) :
    physicalProfile δ p (scale δ y)=profile δ p y := by
  simp only [physicalProfile, scale_comp, inv_mul_cancel₀ hδ, scale_one]

end ElasticityBoundaryProfileBounds

end
end
section
/-! Literal unscaled differential residuals of the constructed boundary fields.
The estimates are in the actual half-space L2 norm, not a formal series norm. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryStrongLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights

lemma D_atParameter (δ : ℝ) (j : Fin 3) (p : Polynomial MP) :
    D δ j (atParameter p δ)=atParameter (PD j p) δ := (eval_PD j p δ).symm

lemma partial_layer {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (j β : Fin 3) (z : Y) :
    dpart (layer q δ j) β z = ((δ^2)⁻¹:ℝ) •
      physicalProfile δ (atParameter (PD β (unpack j q)) δ) z := by
  rw [dpart, layer, fderiv_physicalProfile_basis hδ, D_atParameter]

end ElasticityBoundaryStrongLayer

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Cut off actual boundary fields. The complete product-rule residual is
retained; its derivatives are flat at the concentration point. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound

lemma dpart_mul {f g : Y → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 3) (y : Y) :
    dpart (fun z => f z*g z) j y=dpart f j y*g y+f y*dpart g j y := by
  rw [dpart, fderiv_fun_mul (hf y) (hg y)]
  simp only [add_apply, smul_apply, smul_eq_mul, dpart]
  ring

lemma first_cutoff {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (j β : Fin 3) (y : Y) :
    dpart (cutoffLayer χ q δ j) β y =
      dpart χ β y*layer q δ j y+χ y*dpart (layer q δ j) β y :=
  dpart_mul (hχ.differentiable (by simp)) ((smooth_physicalProfile δ _).differentiable (by simp)) β y

end ElasticityBoundaryCutoffLayer

end
end
section
/-! Compactly supported actual half-space quasimodes with arbitrary strong
residual order and uniform H1 bounds. All scalings are those of the physical
boundary layer, not a formal symbol expansion. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffParametrix
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound ElasticityBoundaryCutoffLayer

lemma first_scaled_identity_oai {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : δ≠0) (q : Polynomial W) (j β : Fin 3) (y : Y) :
    dpart (cutoffLayer χ q δ j) β (scale δ y)=
      ((δ^2)⁻¹:ℝ) • (envelope δ y*firstScaled χ q δ j β y) := by
  rw [first_cutoff hχ, partial_layer hδ]
  simp only [layer, physicalProfile_scale hδ, profile, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_pow, firstScaled]
  have hd : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  field_simp
  ring

end ElasticityBoundaryCutoffParametrix

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity_oai := @OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity_oai
