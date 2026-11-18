-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:09.655203+00:00
-- url     : https://prove2.me/submissions/7d559698-e2ba-4f11-b0aa-db16b7f45797

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRectangularKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I]
variable {G : Type*} [CommGroup G]

lemma rectangular_diagonal [DecidableEq I] {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (v : ∀ i j,L i → R j → G) :
    rectangular (fun i j=>if i=j then 1 else 0) v=
      ∏ i,∏ x:L i,∏ y:R i,v i i x y := by
  unfold rectangular
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · simp

end ElementaryPositivity.RectangularKernel

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossKernelExplicit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_left _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma sameDen_reverse_eq (s t : Pack (A:=A)) :
    sameDen t s = (-1 : MvPolynomial (Σi,A i) ℚ) ^ (∑ i,(s i).card*(t i).card) * sameDen s t := by
  unfold sameDen
  calc
    _ = ∏ i,∏ x∈s i,∏ y∈t i,
        (-1 : MvPolynomial (Σi,A i) ℚ)*diagonal ⟨i,x⟩ ⟨i,y⟩ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro x hx
      apply Finset.prod_congr rfl
      intro y hy
      unfold diagonal
      ring
    _ = _ := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,←pow_mul]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.mul_comm _ _

omit [∀ i,Fintype (A i)] in
lemma crossKernelPolynomial_explicit (a : I → I → ℕ) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (q : PackConvolution.Cut (left p))
    (r : PackConvolution.Cut (right p)) :
    crossKernelPolynomial a p q r =
      (-1 : MvPolynomial (Σi,A i) ℚ) ^ (∑ i,(right q i).card*(left r i).card) *
        sameDen (left q) (left r) * sameDen (right q) (right r) *
          arrowNum a (left q) (right r) * arrowNum a (left r) (right q) := by
  apply (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ)
    (FractionRing (MvPolynomial (Σi,A i) ℚ)))
  rw [←crossKernelPolynomial_spec,kernel_polynomial_ratio,kernel_polynomial_ratio]
  have hq : (fun i=>left q i ∪ right q i)=left p := funext fun i=>(q i).property.2
  have hr : (fun i=>left r i ∪ right r i)=right p := funext fun i=>(r i).property.2
  have hd : sameDen (left p) (right p)=
      sameDen (left q) (left r)*sameDen (left q) (right r)*
        ((-1 : MvPolynomial (Σi,A i) ℚ) ^ (∑ i,(right q i).card*(left r i).card)*
          sameDen (left r) (right q))*sameDen (right q) (right r) := by
    conv_lhs => rw [←hq,←hr]
    rw [sameDen_union_left (left q) (right q) (fun i=>left r i ∪ right r i) (fun i=>(q i).property.1),
      sameDen_union_right (left q) (left r) (right r) (fun i=>(r i).property.1),
      sameDen_union_right (right q) (left r) (right r) (fun i=>(r i).property.1)]
    rw [sameDen_reverse_eq (left r) (right q)]
    have he : (∑ i,(left r i).card*(right q i).card)=∑ i,(right q i).card*(left r i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.mul_comm _ _
    rw [he]
    ring
  have hne := crossDen_ne_zero p q r
  have h₁ : algebraMap (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left q) (right r))≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne
        (mul_ne_zero_iff.mp hne).1
  have h₂ : algebraMap (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))
      (sameDen (left r) (right q))≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (MvPolynomial (Σi,A i) ℚ) (FractionRing (MvPolynomial (Σi,A i) ℚ))).ne
        (mul_ne_zero_iff.mp hne).2
  rw [hd]
  simp only [map_mul,map_pow,map_neg,map_one]
  field_simp

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma fourSameDen11 (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (sameDen (left (canonicalLeftCut d₁ e₁ d₂ e₂)) (left (canonicalRightCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ x:Fin (d₁ i),∏ y:Fin (d₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inl x) (.inl y) := by
  simp only [sameDen,map_prod,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map,ShufflePolynomiality.diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] in
lemma fourSameDen22 (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (sameDen (right (canonicalLeftCut d₁ e₁ d₂ e₂)) (right (canonicalRightCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ x:Fin (e₁ i),∏ y:Fin (e₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inr x) (.inr y) := by
  simp only [sameDen,map_prod,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map,ShufflePolynomiality.diagonal,map_sub,rename_X]
  rfl

omit [DecidableEq I] in
lemma fourArrow12 (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (arrowNum a (left (canonicalLeftCut d₁ e₁ d₂ e₂)) (right (canonicalRightCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ j,∏ x:Fin (d₁ i),∏ y:Fin (e₂ j),fourForwardDifference d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)^a i j := by
  simp only [arrowNum,map_prod,map_pow,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map,ShufflePolynomiality.diagonal,map_sub,rename_X]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma fourReverseDifference (d₁ e₁ d₂ e₂ : I → ℕ) (i j : I)
    (x : Fin (d₂ i)) (y : Fin (e₁ j)) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂)
      (ShufflePolynomiality.diagonal ⟨i,Sum.inr (Sum.inl x)⟩ ⟨j,Sum.inl (Sum.inr y)⟩)=
      -fourForwardDifference d₁ e₁ d₂ e₂ j i (.inr y) (.inl x) := by
  simp only [ShufflePolynomiality.diagonal,map_sub,rename_X]
  unfold fourForwardDifference
  rw [neg_sub]
  rfl

omit [DecidableEq I] in
lemma fourArrow21 (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    rename (fourPackEquiv d₁ e₁ d₂ e₂) (arrowNum a (left (canonicalRightCut d₁ e₁ d₂ e₂)) (right (canonicalLeftCut d₁ e₁ d₂ e₂)))=
      ∏ i,∏ j,∏ x:Fin (d₂ i),∏ y:Fin (e₁ j),(-fourForwardDifference d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))^a i j := by
  simp only [arrowNum,map_prod,map_pow,canonicalLeftCut,canonicalRightCut,embedPackCut,
    sumPackCut,left,right,Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro y hy
  congr 1
  exact fourReverseDifference d₁ e₁ d₂ e₂ i j x y

lemma fourCrossPolynomial_explicit (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourCrossPolynomial a d₁ e₁ d₂ e₂ =
      (-1 : MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) ^ (∑ i,e₁ i*d₂ i) *
      (∏ i,∏ x:Fin (d₁ i),∏ y:Fin (d₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inl x) (.inl y)) *
      (∏ i,∏ x:Fin (e₁ i),∏ y:Fin (e₂ i),fourForwardDifference d₁ e₁ d₂ e₂ i i (.inr x) (.inr y)) *
      (∏ i,∏ j,∏ x:Fin (d₁ i),∏ y:Fin (e₂ j),fourForwardDifference d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)^a i j) *
      (∏ i,∏ j,∏ x:Fin (d₂ i),∏ y:Fin (e₁ j),(-fourForwardDifference d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))^a i j) := by
  rw [fourCrossPolynomial,crossKernelPolynomial_explicit]
  simp only [map_mul,map_pow,map_neg,map_one,fourSameDen11,fourSameDen22,fourArrow12,fourArrow21]
  congr 5
  simp only [canonicalLeftCut,canonicalRightCut,embedPackCut,sumPackCut,left,right,
    Finset.card_map,Finset.card_univ,Fintype.card_fin]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourAffineKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma polynomial_fourRelative_difference (d₁ e₁ d₂ e₂ : I → ℕ)
    (i j : I) (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :
    polynomial (fourRelativeRaw d₁ e₁ d₂ e₂ (fourForwardDifference d₁ e₁ d₂ e₂ i j x y))=
      (fourAffine d₁ e₁ d₂ e₂ i j x y).val := by
  simp only [fourAffine,affineUnit_val,fourForwardDifference,fourRelativeRaw,
    map_sub,aeval_X,Sum.elim_inl,Sum.elim_inr,map_add,polynomial_C,polynomial_X]
  ring

lemma polynomial_fourRelative_cross (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    polynomial (fourRelativeRaw d₁ e₁ d₂ e₂ (fourCrossPolynomial a d₁ e₁ d₂ e₂))=
      (fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := by
  rw [fourCrossPolynomial_explicit]
  simp only [map_mul,map_pow,map_neg,map_one,map_prod,polynomial_fourRelative_difference]
  unfold fourCrossAffineUnit
  rw [rectangular_diagonal,rectangular_diagonal]
  simp only [rectangular,zpow_natCast,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_neg,
    Units.val_one,Units.coe_prod]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourColumns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
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
noncomputable local instance taylorFourRing_r64dfa6_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra
noncomputable local instance taylorTensorNonUnital_r64dfa6_1 (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (taylorTensorRing d e).toNonUnitalNonAssocSemiring
omit [Fintype I] [DecidableEq I] in
lemma commonTaylorTensor_eval (d e : I → ℕ) (t : ℚ) (x : S d⊗[ℚ]S e) :
    (commonTaylorTensor d e x).eval (algebraMap ℚ (S d⊗[ℚ]S e) t)=
      TensorProduct.map (translationS d t) (translationS e t) x :=
  tensorPolynomial_eval _ _ t _ _ (fun x=>taylorS_eval d x t) (fun y=>taylorS_eval e y t) x

omit [Fintype I] [DecidableEq I] in
lemma map_commonTaylorTensor (d e : I → ℕ) (x : S d⊗[ℚ] S e) :
    Polynomial.map (tensorValueAlg d e).toRingHom (commonTaylorTensor d e x)=
      taylor (tensorValue d e x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,commonTaylorTensor_eval]
  change tensorValue d e (TensorProduct.map (translationS d t) (translationS e t) x)=
    (taylor (tensorValue d e x)).eval (C t)
  rw [tensorValue_translation,taylor_eval]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeTaylor_tmul (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S d₁⊗[ℚ]S e₁) (y : S d₂⊗[ℚ]S e₂) :
    fourRelativeTaylor d₁ e₁ d₂ e₂ (x⊗ₜ[ℚ]y)=
      Polynomial.map (Algebra.TensorProduct.includeLeft : (S d₁⊗[ℚ]S e₁) →ₐ[ℚ]
        (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)).toRingHom (commonTaylorTensor d₁ e₁ x)*
      Polynomial.C ((1 : S d₁⊗[ℚ]S e₁)⊗ₜ[ℚ]y) := by
  change tensorPolynomial (commonTaylorTensor d₁ e₁) Polynomial.CAlgHom (x⊗ₜ[ℚ]y)=_
  rw [tensorPolynomial_tmul]
  congr 1
  change Polynomial.map _ (Polynomial.C y)=Polynomial.C _
  rw [Polynomial.map_C]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeRaw_left (d₁ e₁ d₂ e₂ : I → ℕ) (f : MvPolynomial (CellVars d₁ e₁) ℚ) :
    fourRelativeRaw d₁ e₁ d₂ e₂ (rename Sum.inl f)=
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [fourRelativeRaw]
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,taylor_X,Polynomial.map_mul,hf]
    congr 1
    simp [fourRelativeRaw]

omit [Fintype I] [DecidableEq I] in
lemma fourRelativeRaw_right (d₁ e₁ d₂ e₂ : I → ℕ) (f : MvPolynomial (CellVars d₂ e₂) ℚ) :
    fourRelativeRaw d₁ e₁ d₂ e₂ (rename Sum.inr f)=Polynomial.C (rename Sum.inr f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [fourRelativeRaw]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,hf]
    congr 1
    simp [fourRelativeRaw]

omit [Fintype I] [DecidableEq I] in
lemma map_commonTaylorTensor_left (d₁ e₁ d₂ e₂ : I → ℕ) (x : S d₁⊗[ℚ]S e₁) :
    Polynomial.map (fourValueAlg d₁ e₁ d₂ e₂).toRingHom
      (Polynomial.map (Algebra.TensorProduct.includeLeft : (S d₁⊗[ℚ]S e₁) →ₐ[ℚ]
        (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)).toRingHom (commonTaylorTensor d₁ e₁ x))=
      Polynomial.map (rename (R:=ℚ) Sum.inl).toRingHom (taylor (tensorValue d₁ e₁ x)) := by
  rw [←map_commonTaylorTensor d₁ e₁ x,Polynomial.map_map,Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro g
  change fourValue d₁ e₁ d₂ e₂ (g⊗ₜ[ℚ]1)=rename Sum.inl (tensorValue d₁ e₁ g)
  rw [fourValue_tmul]
  change _*rename Sum.inr (tensorValueAlg d₂ e₂ 1)=_
  rw [map_one,map_one,mul_one]

omit [Fintype I] [DecidableEq I] in
lemma map_fourRelativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    Polynomial.map (fourValueAlg d₁ e₁ d₂ e₂).toRingHom (fourRelativeTaylor d₁ e₁ d₂ e₂ x)=
      fourRelativeRaw d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ x) := by
  have H : ((Polynomial.mapAlgHom (fourValueAlg d₁ e₁ d₂ e₂)).comp
      (fourRelativeTaylor d₁ e₁ d₂ e₂)).toLinearMap=
      ((fourRelativeRaw d₁ e₁ d₂ e₂).comp (fourValueAlg d₁ e₁ d₂ e₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change Polynomial.map (fourValueAlg d₁ e₁ d₂ e₂).toRingHom
      (fourRelativeTaylor d₁ e₁ d₂ e₂ (u⊗ₜ[ℚ]v))=
      fourRelativeRaw d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ (u⊗ₜ[ℚ]v))
    rw [fourRelativeTaylor_tmul,Polynomial.map_mul,map_commonTaylorTensor_left,
      Polynomial.map_C,fourValue_tmul,map_mul,fourRelativeRaw_left,fourRelativeRaw_right]
    congr 1
    change Polynomial.C (fourValue d₁ e₁ d₂ e₂ (1⊗ₜ[ℚ]v))=_
    rw [fourValue_tmul]
    change Polynomial.C (rename Sum.inl (tensorValueAlg d₁ e₁ 1)*_)=_
    rw [map_one,map_one,one_mul]
  exact LinearMap.congr_fun H x

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourTensorKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelTensorRing
noncomputable local instance kernelTensorDistrib_r64dfa6_1 (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourAlg
noncomputable local instance kernelTensorSelf_r64dfa6_1 (d e : I → ℕ) :
    Module (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) := Semiring.toModule
noncomputable local instance kernelTensorNonUnital_r64dfa6_1 (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (kernelTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance kernelFourNonUnital_r64dfa6_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (kernelFourRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring
lemma fourTensor_cross_realize (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom
      (polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)))=
      (fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := by
  rw [polynomial_map,map_fourRelativeTaylor,fourValue_fourCrossTensor,polynomial_fourRelative_cross]

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorDistrib
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorSelf
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelSeriesRing
lemma fourSeriesValue_cross_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourSeriesValue d₁ e₁ d₂ e₂
      (polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)))=
      (fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := fourTensor_cross_realize a d₁ e₁ d₂ e₂

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross_oai.{u_1}
