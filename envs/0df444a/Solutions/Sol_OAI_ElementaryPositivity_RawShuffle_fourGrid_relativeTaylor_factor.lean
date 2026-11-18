-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:07.874428+00:00
-- url     : https://prove2.me/submissions/133cb6dc-6f20-4ecd-aa71-b817941d7e60

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourColumns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.columnTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.columnTensorAlgebra
noncomputable local instance columnFourRing_r467e3c_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.columnFourAlgebra
omit [Fintype I] [DecidableEq I] in
lemma fourValue_firstColumn (d₁ e₁ d₂ e₂ : I → ℕ) (x : S d₁⊗[ℚ]S d₂) :
    fourValueAlg d₁ e₁ d₂ e₂ (firstColumnAlg d₁ e₁ d₂ e₂ x)=
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ x) := by
  have h : ((fourValueAlg d₁ e₁ d₂ e₂).comp (firstColumnAlg d₁ e₁ d₂ e₂)).toLinearMap=
      ((rename (firstColumnVars d₁ e₁ d₂ e₂)).comp (tensorValueAlg d₁ d₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change fourValue d₁ e₁ d₂ e₂ ((u⊗ₜ[ℚ]1)⊗ₜ[ℚ](v⊗ₜ[ℚ]1))=
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ (u⊗ₜ[ℚ]v))
    simp only [fourValue_tmul,tensorValue_tmul,OneMemClass.coe_one,map_one,mul_one,
      map_mul,rename_rename]
    rfl
  exact LinearMap.congr_fun h x

omit [Fintype I] [DecidableEq I] in
lemma fourValue_secondColumn (d₁ e₁ d₂ e₂ : I → ℕ) (x : S e₁⊗[ℚ]S e₂) :
    fourValueAlg d₁ e₁ d₂ e₂ (secondColumnAlg d₁ e₁ d₂ e₂ x)=
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ x) := by
  have h : ((fourValueAlg d₁ e₁ d₂ e₂).comp (secondColumnAlg d₁ e₁ d₂ e₂)).toLinearMap=
      ((rename (secondColumnVars d₁ e₁ d₂ e₂)).comp (tensorValueAlg e₁ e₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change fourValue d₁ e₁ d₂ e₂ ((1⊗ₜ[ℚ]u)⊗ₜ[ℚ](1⊗ₜ[ℚ]v))=
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ (u⊗ₜ[ℚ]v))
    simp only [fourValue_tmul,tensorValue_tmul,OneMemClass.coe_one,map_one,one_mul,
      map_mul,rename_rename]
    rfl
  exact LinearMap.congr_fun h x

lemma fourColumns_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁⊗[ℚ]S d₂) (g : S e₁⊗[ℚ]S e₂) :
    firstColumnAlg d₁ e₁ d₂ e₂ f * secondColumnAlg d₁ e₁ d₂ e₂ g=
      fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g) := by
  apply fourValue_injective
  change fourValueAlg d₁ e₁ d₂ e₂ (_*_)=_
  rw [map_mul,fourValue_firstColumn,fourValue_secondColumn,fourValue_interchange]

end ElementaryPositivity.RawShuffle

end
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
noncomputable local instance taylorFourRing_r467e3c_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra
noncomputable local instance taylorTensorNonUnital_r467e3c_1 (d e : I → ℕ) :
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ColumnTaylor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.colTaylorTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.colTaylorTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.colTaylorFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.colTaylorFourAlg
omit [Fintype I] [DecidableEq I] in
lemma translationS_one (d : I → ℕ) (t : ℚ) : translationS d t (1 : S d)=1 := by
  apply Subtype.ext
  exact map_one (translation t)

omit [Fintype I] [DecidableEq I] in
lemma firstColumn_relativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ) (x : S d₁⊗[ℚ]S d₂) :
    Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (relativeTaylor d₁ d₂ x)=
      fourRelativeTaylor d₁ e₁ d₂ e₂ (firstColumnAlg d₁ e₁ d₂ e₂ x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,relativeTaylor_eval,fourRelativeTaylor_eval]
  have h : (firstColumnAlg d₁ e₁ d₂ e₂).toLinearMap ∘ₗ
      TensorProduct.map (translationS d₁ t) LinearMap.id=
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t)) LinearMap.id ∘ₗ
        (firstColumnAlg d₁ e₁ d₂ e₂).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change ((translationS d₁ t u)⊗ₜ[ℚ](1 : S e₁))⊗ₜ[ℚ](v⊗ₜ[ℚ](1 : S e₂))=
      ((translationS d₁ t u)⊗ₜ[ℚ](translationS e₁ t 1))⊗ₜ[ℚ](v⊗ₜ[ℚ](1 : S e₂))
    rw [translationS_one]
  exact LinearMap.congr_fun h x

omit [Fintype I] [DecidableEq I] in
lemma secondColumn_relativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ) (x : S e₁⊗[ℚ]S e₂) :
    Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (relativeTaylor e₁ e₂ x)=
      fourRelativeTaylor d₁ e₁ d₂ e₂ (secondColumnAlg d₁ e₁ d₂ e₂ x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,relativeTaylor_eval,fourRelativeTaylor_eval]
  have h : (secondColumnAlg d₁ e₁ d₂ e₂).toLinearMap ∘ₗ
      TensorProduct.map (translationS e₁ t) LinearMap.id=
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t)) LinearMap.id ∘ₗ
        (secondColumnAlg d₁ e₁ d₂ e₂).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change ((1 : S d₁)⊗ₜ[ℚ](translationS e₁ t u))⊗ₜ[ℚ]((1 : S d₂)⊗ₜ[ℚ]v)=
      ((translationS d₁ t 1)⊗ₜ[ℚ](translationS e₁ t u))⊗ₜ[ℚ]((1 : S d₂)⊗ₜ[ℚ]v)
    rw [translationS_one]
  exact LinearMap.congr_fun h x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
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
lemma fourGrid_relativeTaylor_factor_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))=
    Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f)) *
    Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g)) *
    fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂) := by
  rw [separateFour_grid_factor a d₁ e₁ d₂ e₂ (firstCut d₁ d₂) (firstCut e₁ e₂)]
  rw [←fourColumns_product d₁ e₁ d₂ e₂]
  simp only [map_mul,←firstColumn_relativeTaylor,←secondColumn_relativeTaylor]

end ElementaryPositivity.RawShuffle

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor_oai.{u_1}
