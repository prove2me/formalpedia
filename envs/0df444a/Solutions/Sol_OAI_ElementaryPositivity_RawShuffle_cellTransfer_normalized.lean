-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:17.246428+00:00
-- url     : https://prove2.me/submissions/798455d7-7edd-4b69-af0a-51124ed6f3df

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom036
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourGrid_normalized_algebra
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourTensorKernel_cancellation

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentScalarNaturality
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
lemma rat_smul_series (r : ℚ) (x : LaurentSeries R) :
    r • x=C (algebraMap ℚ R r)*x := by
  apply HahnSeries.ext
  funext k
  simp only [HahnSeries.coeff_smul,HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul]
  exact Algebra.smul_def r (x.coeff k)
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentSigns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
variable {R : Type*} [CommRing R]
lemma unit_neg_one_inv : (-1 : Rˣ)⁻¹=(-1 : Rˣ) := by
  apply Units.ext
  simp

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentUnitSigns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]
lemma negative_unit_rat (n : ℤ) :
    ((-1 : (LaurentSeries R)ˣ)^n).val=C (algebraMap ℚ R ((-1 : ℚ)^n)) := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast,zpow_natCast,Units.val_pow_eq_pow_val,Units.val_neg,
      Units.val_one,map_pow,map_neg,map_one]
  | negSucc n =>
    rw [zpow_negSucc,←inv_pow,ElementaryPositivity.unit_neg_one_inv]
    simp only [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,zpow_negSucc,
      ←inv_pow,inv_neg,inv_one,map_pow,map_neg,map_one]
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourAffineKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped TensorProduct

lemma tensor_map_projection {K A B A' B' : Type*} [CommSemiring K]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra K A] [Algebra K B] [Algebra K A'] [Algebra K B']
    (T : A →ₗ[K] B) (U : A' →ₗ[K] B') (ι : B →ₐ[K] A) (κ : B' →ₐ[K] A')
    (hT : ∀ b x,T (ι b*x)=b*T x) (hU : ∀ b x,U (κ b*x)=b*U x)
    (b : B⊗[K]B') (x : A⊗[K]A') :
    TensorProduct.map T U (Algebra.TensorProduct.map ι κ b*x)=
      b*TensorProduct.map T U x := by
  induction b using OAI.tensorInductionOn with
  | add b c hb hc => simp only [map_add,add_mul,hb,hc]
  | tmul b c =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [mul_add,map_add,hx,hy]
    | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        TensorProduct.map_tmul,hT,hU]

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourColumns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorPolynomials
open scoped TensorProduct
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

lemma tensorPolynomial_tmul (f : A →ₐ[ℚ] Polynomial A) (g : B →ₐ[ℚ] Polynomial B)
    (x : A) (y : B) :
    tensorPolynomial f g (x⊗ₜ[ℚ]y)=
      Polynomial.map (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ]B).toRingHom (f x)*
      Polynomial.map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A⊗[ℚ]B).toRingHom (g y) := by
  rfl

lemma eval_map {C D : Type*} [Semiring C] [Semiring D] [Algebra ℚ C] [Algebra ℚ D]
    (φ : C →ₐ[ℚ] D) (p : Polynomial C) (t : ℚ) :
    (Polynomial.map φ.toRingHom p).eval (algebraMap ℚ D t)=φ (p.eval (algebraMap ℚ C t)) := by
  rw [Polynomial.eval_map]
  calc
    _ = Polynomial.eval₂ φ.toRingHom (φ (algebraMap ℚ C t)) p :=
      congrArg (fun x=>Polynomial.eval₂ φ.toRingHom x p) (φ.commutes t).symm
    _ = _ := Polynomial.eval₂_at_apply φ.toRingHom (algebraMap ℚ C t)

lemma tensorPolynomial_eval (f : A →ₐ[ℚ] Polynomial A) (g : B →ₐ[ℚ] Polynomial B)
    (t : ℚ) (F : A →ₗ[ℚ] A) (G : B →ₗ[ℚ] B)
    (hf : ∀ x,(f x).eval (algebraMap ℚ A t)=F x)
    (hg : ∀ y,(g y).eval (algebraMap ℚ B t)=G y) (x : A⊗[ℚ]B) :
    (tensorPolynomial f g x).eval (algebraMap ℚ (A⊗[ℚ]B) t)=TensorProduct.map F G x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,Polynomial.eval_add,hx,hy]
  | tmul x y =>
    rw [tensorPolynomial_tmul,Polynomial.eval_mul,eval_map,eval_map,hf,hg]
    simp

end ElementaryPositivity.TensorPolynomials

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation ElementaryPositivity.TensorPolynomials
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.taylorTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.taylorTensorAlgebra
noncomputable local instance taylorFourRing_r4c1573_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra
noncomputable local instance taylorTensorNonUnital_r4c1573_1 (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (taylorTensorRing d e).toNonUnitalNonAssocSemiring
omit [Fintype I] [DecidableEq I] in
lemma commonTaylorTensor_eval (d e : I → ℕ) (t : ℚ) (x : S d⊗[ℚ]S e) :
    (commonTaylorTensor d e x).eval (algebraMap ℚ (S d⊗[ℚ]S e) t)=
      TensorProduct.map (translationS d t) (translationS e t) x :=
  tensorPolynomial_eval _ _ t _ _ (fun x=>taylorS_eval d x t) (fun y=>taylorS_eval e y t) x

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeTaylor_eval (d₁ e₁ d₂ e₂ : I → ℕ) (t : ℚ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    (fourRelativeTaylor d₁ e₁ d₂ e₂ x).eval (algebraMap ℚ _ t)=
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t))
        (LinearMap.id : (S d₂⊗[ℚ]S e₂) →ₗ[ℚ] (S d₂⊗[ℚ]S e₂)) x :=
  tensorPolynomial_eval _ _ t _ _ (commonTaylorTensor_eval d₁ e₁ t)
    (fun _=>Polynomial.eval_C) x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentProjectionFormula
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {K A B : Type*} [CommSemiring K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

lemma mapLinear_projection (T : A →ₗ[K] B) (ι : B →+* A)
    (hT : ∀ b x,T (ι b*x)=b*T x) (P : LaurentSeries B) (X : LaurentSeries A) :
    mapLinear T (mapRing ι P * X)=P*mapLinear T X := by
  apply HahnSeries.ext
  funext k
  have hP : (mapRing ι P).support⊆P.support := HahnSeries.support_map_subset P ι.toZeroHom
  have hX : (mapLinear T X).support⊆X.support := HahnSeries.support_map_subset X ⟨T,T.map_zero⟩
  rw [mapLinear_coeff,coeff_mul_left' P.isPWO_support hP,
    coeff_mul_right' X.isPWO_support hX,map_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  exact hT _ _

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ShuffleProjection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.projectionTensorSCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.projectionTensorSAlgebra
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.projectionFourSCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.projectionFourSAlgebra
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.projectionTensorSNonUnitalNonAssocSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.projectionFourSNonUnitalNonAssocSemiring
lemma shuffleTensor_projection (a : I → I → ℕ) {d e : I → ℕ}
    (A : Cut d e) (f : S (d+e)) (x : S d⊗[ℚ]S e) :
    shuffleTensorLinear a d e (restrictTensorAlg A f*x)=
      f*shuffleTensorLinear a d e x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [mul_add,map_add,hx,hy]
  | tmul x y =>
    apply localizeS_injective
    rw [←tensorShuffle_tensorValue,tensorValue_mul]
    change tensorShuffle a (tensorValue d e (restrictTensor A f)*tensorValue d e (x⊗ₜ[ℚ]y))=_
    rw [tensorValue_restrictTensor,tensorValue_tmul,tensorShuffle_restricted_mul]
    rw [←shufflePolynomial_eq,shuffleTensorLinear_tmul]
    exact (map_mul (algebraMap (MvPolynomial (Σi,Fin (d i+e i)) ℚ)
      (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))) f.val (shufflePolynomial a x y).val).symm

lemma twoTarget_projection (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂)
    (f : S (d₁+e₁)⊗[ℚ]S (d₂+e₂))
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    twoTargetTransfer a d₁ e₁ d₂ e₂ (restrictRows d₁ e₁ d₂ e₂ A B f*x)=
      f*twoTargetTransfer a d₁ e₁ d₂ e₂ x :=
  tensor_map_projection _ _ _ _ (shuffleTensor_projection a A) (shuffleTensor_projection a B) f x

lemma twoTarget_Laurent_projection (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂)
    (f : LaurentSeries (S (d₁+e₁)⊗[ℚ]S (d₂+e₂)))
    (x : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂)
      (mapRing (restrictRows d₁ e₁ d₂ e₂ A B).toRingHom f*x)=
      f*mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) x :=
  mapLinear_projection _ _ (twoTarget_projection a d₁ e₁ d₂ e₂ A B) f x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ColumnTaylor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTaylorTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTaylorTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTaylorFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.naturalTaylorFourAlg
lemma shuffleTensor_translation (a : I → I → ℕ) (d e : I → ℕ) (t : ℚ)
    (x : S d⊗[ℚ]S e) :
    shuffleTensorLinear a d e (TensorProduct.map (translationS d t) (translationS e t) x)=
      translationS (d+e) t (shuffleTensorLinear a d e x) := by
  have h : shuffleTensorLinear a d e ∘ₗ TensorProduct.map (translationS d t) (translationS e t)=
      translationS (d+e) t ∘ₗ shuffleTensorLinear a d e := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.comp_apply,TensorProduct.map_tmul,shuffleTensorLinear_tmul]
    exact (translation_shufflePolynomial a t u v).symm
  exact LinearMap.congr_fun h x

lemma twoTarget_relativeTaylor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    polynomialMapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (fourRelativeTaylor d₁ e₁ d₂ e₂ x)=
      relativeTaylor (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [polynomialMapLinear_eval_rat,fourRelativeTaylor_eval,relativeTaylor_eval]
  have h : twoTargetTransfer a d₁ e₁ d₂ e₂ ∘ₗ
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t)) LinearMap.id=
      TensorProduct.map (translationS (d₁+e₁) t) LinearMap.id ∘ₗ
        twoTargetTransfer a d₁ e₁ d₂ e₂ := by
    apply TensorProduct.ext'
    intro u v
    change shuffleTensorLinear a d₁ e₁ (TensorProduct.map (translationS d₁ t) (translationS e₁ t) u)⊗ₜ[ℚ]
        shuffleTensorLinear a d₂ e₂ v=
      translationS (d₁+e₁) t (shuffleTensorLinear a d₁ e₁ u)⊗ₜ[ℚ]shuffleTensorLinear a d₂ e₂ v
    rw [shuffleTensor_translation]
  exact LinearMap.congr_fun h x

lemma twoTarget_polynomial_relativeTaylor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ x))=
      polynomial (relativeTaylor (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ x)) := by
  rw [polynomial_mapLinear,twoTarget_relativeTaylor]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourModule
lemma fourTensorKernelRHS_scalar (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val=
      HahnSeries.C (algebraMap ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) ((-1 : ℚ)^eulerForm a d₂ e₁)) *
        ((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
          (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
          (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
            (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val) := by
  unfold fourTensorKernelRHS
  rw [Units.val_mul, negative_unit_rat]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma four_rat_smul_series (d₁ e₁ d₂ e₂ : I → ℕ) (r : ℚ)
    (x : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    r • x=HahnSeries.C (algebraMap ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) r)*x :=
  @rat_smul_series ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))
    (cancelFourRing d₁ e₁ d₂ e₂) (cancelFourAlg d₁ e₁ d₂ e₂) r x

lemma fourGrid_normalized (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    (mappedInverseKernel a (d₁+e₁) (d₂+e₂) (restrictRows d₁ e₁ d₂ e₂ A B)).val *
      ((mappedInverseKernel (fun _ _ : I=>0) (d₁+e₁) (d₂+e₂) (restrictRows d₁ e₁ d₂ e₂ A B))⁻¹).val *
      polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
        (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) • fourInputSeries a d₁ e₁ d₂ e₂ f g := by
  apply (fourGrid_normalized_algebra a d₁ e₁ d₂ e₂ f g _ _ _
    ((fourTensorKernel_cancellation a d₁ e₁ d₂ e₂ A B).trans
      (fourTensorKernelRHS_scalar a d₁ e₁ d₂ e₂))).trans
  exact (four_rat_smul_series d₁ e₁ d₂ e₂ _ _).symm

end ElementaryPositivity.RawShuffle

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellTransferSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule

lemma mappedInverseKernel_ratio {R : Type*} [CommRing R] [Algebra ℚ R]
    (a b : I → I → ℕ) (d e : I → ℕ) (f : S d⊗[ℚ]S e →ₐ[ℚ]R) :
    mapRing f.toRingHom ((inverseKernelUnit a d e)*(inverseKernelUnit b d e)⁻¹).val=
    (mappedInverseKernel a d e f).val * ((mappedInverseKernel b d e f)⁻¹).val := by
  rw [Units.val_mul,map_mul]
  rfl

lemma cellTransfer_normalized_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    ((inverseKernelUnit a (d₁+e₁) (d₂+e₂))*
      (inverseKernelUnit (fun _ _ : I=>0) (d₁+e₁) (d₂+e₂))⁻¹).val *
      polynomial (relativeTaylor (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (fourInputSeries a d₁ e₁ d₂ e₂ f g) := by
  rw [cellTransfer,LinearMap.comp_apply,←twoTarget_polynomial_relativeTaylor,
    ←twoTarget_Laurent_projection a d₁ e₁ d₂ e₂ (firstCut d₁ e₁) (firstCut d₂ e₂),
    mappedInverseKernel_ratio,fourGrid_normalized]
  exact (mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂)).map_smul _ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized_oai.{u_1}
