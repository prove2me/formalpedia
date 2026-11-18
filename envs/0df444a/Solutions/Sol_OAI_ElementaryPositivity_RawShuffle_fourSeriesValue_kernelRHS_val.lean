-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:10.678577+00:00
-- url     : https://prove2.me/submissions/ffc79ff8-d8d1-422f-b6d4-af34c2177598

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourSeriesValue_second

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRectangularKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I]
variable {G : Type*} [CommGroup G]

lemma rectangular_add {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b c : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (b+c) v=rectangular b v*rectangular c v := by
  simp only [rectangular,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]

lemma rectangular_neg {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (-b) v=(rectangular b v)⁻¹ := by
  simp only [rectangular,Pi.neg_apply,zpow_neg,Finset.prod_inv_distrib]

lemma rectangular_sub {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b c : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (b-c) v=rectangular b v*(rectangular c v)⁻¹ := by
  rw [sub_eq_add_neg,rectangular_add,rectangular_neg]

lemma rectangular_transpose {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (fun i j=>b j i) (fun i j (x:R i) (y:L j)=>v j i y x)=
      rectangular b v := by
  unfold rectangular
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  exact Finset.prod_comm

lemma rectangular_sum {L₁ L₂ R₁ R₂ : I → Type*}
    [∀ i,Fintype (L₁ i)] [∀ i,Fintype (L₂ i)]
    [∀ i,Fintype (R₁ i)] [∀ i,Fintype (R₂ i)]
    (b : I → I → ℤ) (v : ∀ i j,(L₁ i⊕L₂ i) → (R₁ j⊕R₂ j) → G) :
    rectangular b v=
      rectangular b (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))*
      rectangular b (fun i j x y=>v i j (Sum.inl x) (Sum.inr y))*
      rectangular b (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))*
      rectangular b (fun i j x y=>v i j (Sum.inr x) (Sum.inr y)) := by
  simp only [rectangular,Fintype.prod_sum_type,Finset.prod_mul_distrib]
  ac_rfl

lemma four_rectangle_cancellation {L₁ L₂ R₁ R₂ : I → Type*}
    [∀ i,Fintype (L₁ i)] [∀ i,Fintype (L₂ i)]
    [∀ i,Fintype (R₁ i)] [∀ i,Fintype (R₂ i)]
    (δ a : I → I → ℤ) (v : ∀ i j,(L₁ i⊕L₂ i) → (R₁ j⊕R₂ j) → G) :
    rectangular (δ-a) v * (rectangular δ v)⁻¹ *
      (rectangular δ (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))*
       rectangular δ (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))*
       rectangular a (fun i j x y=>v i j (Sum.inl x) (Sum.inr y))*
       rectangular (fun i j=>a j i) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))) =
    rectangular (δ-a) (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))*
    rectangular (δ-a) (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))*
      (rectangular (δ-a) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))*
       (rectangular (δ-(fun i j=>a j i)) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y)))⁻¹) := by
  rw [rectangular_sub δ a v,rectangular_sum a v]
  rw [rectangular_sub,rectangular_sub,rectangular_sub,rectangular_sub]
  generalize rectangular δ v=K
  generalize rectangular a (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))=A
  generalize rectangular a (fun i j x y=>v i j (Sum.inl x) (Sum.inr y))=B
  generalize rectangular a (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))=C
  generalize rectangular a (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))=D
  generalize rectangular δ (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))=P
  generalize rectangular δ (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))=Q
  generalize rectangular δ (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))=R
  generalize rectangular (fun i j=>a j i) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))=S
  simp [mul_comm,mul_left_comm,mul_assoc]
  rw [mul_left_comm B P,mul_left_comm B Q,mul_left_comm B S,mul_left_comm B A⁻¹,
    mul_inv_cancel_left]

end ElementaryPositivity.RectangularKernel

end
section
namespace ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I]
variable {G : Type*} [CommGroup G]

lemma rectangular_mul {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v w : ∀ i j,L i → R j → G) :
    rectangular b (fun i j x y=>v i j x y*w i j x y)=rectangular b v*rectangular b w := by
  simp only [rectangular,mul_zpow,Finset.prod_mul_distrib]

lemma prod_zpow_sum {α : Type*} (s : Finset α) (b : α → ℤ) (g : G) :
    (∏ x∈s,g^b x)=g^(∑ x∈s,b x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => rw [Finset.prod_insert hx,Finset.sum_insert hx,ih,zpow_add]

lemma rectangular_constant {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (g : G) :
    rectangular (L:=L) (R:=R) b (fun _ _ _ _=>g)=
      g^(∑ i,∑ j,b i j*(Fintype.card (L i):ℤ)*(Fintype.card (R j):ℤ)) := by
  simp only [rectangular,Finset.prod_const,Finset.card_univ,←zpow_natCast,←zpow_mul]
  rw [←prod_zpow_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [←prod_zpow_sum]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring

lemma rectangular_scalar_mul {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (g : G) (v : ∀ i j,L i → R j → G) :
    rectangular b (fun i j x y=>g*v i j x y)=
      g^(∑ i,∑ j,b i j*(Fintype.card (L i):ℤ)*(Fintype.card (R j):ℤ))*rectangular b v := by
  rw [rectangular_mul,rectangular_constant]

end ElementaryPositivity.RectangularKernel

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentSigns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
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

lemma unit_neg_one_zpow_sub (n m : ℤ) :
    (-1 : Rˣ)^n*(-1 : Rˣ)^m=(-1 : Rˣ)^(n-m) := by
  rw [zpow_sub,←inv_zpow,unit_neg_one_inv]

end ElementaryPositivity

lemma mul_sign_collect {G : Type*} [CommMonoid G] (s t p q r u : G) :
    s*p*q*r*(t*u)=(s*t)*(p*q*r*u) := by ac_rfl

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourColumns
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
noncomputable local instance columnFourRing_r4ca2a2_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
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
lemma fourValue_crossingColumn (d₁ e₁ d₂ e₂ : I → ℕ) (x : S e₁⊗[ℚ]S d₂) :
    fourValueAlg d₁ e₁ d₂ e₂ (crossingColumnAlg d₁ e₁ d₂ e₂ x)=
      rename (crossingColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ d₂ x) := by
  have h : ((fourValueAlg d₁ e₁ d₂ e₂).comp (crossingColumnAlg d₁ e₁ d₂ e₂)).toLinearMap=
      ((rename (crossingColumnVars d₁ e₁ d₂ e₂)).comp (tensorValueAlg e₁ d₂)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change fourValue d₁ e₁ d₂ e₂ ((1⊗ₜ[ℚ]u)⊗ₜ[ℚ](v⊗ₜ[ℚ]1))=
      rename (crossingColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ d₂ (u⊗ₜ[ℚ]v))
    simp only [fourValue_tmul,tensorValue_tmul,OneMemClass.coe_one,map_one,one_mul,mul_one,
      map_mul,rename_rename]
    rfl
  exact LinearMap.congr_fun h x

lemma rawKernel_rename {σ : Type*} (a : I → I → ℕ) (d e : I → ℕ)
    (L : (Σ i,Fin (d i)) → σ) (R : (Σ i,Fin (e i)) → σ) :
    Units.map (mapRing (rename (Sum.elim L R)).toRingHom).toMonoidHom
      (SeparationInfinity.rawInverseKernelUnit a d e)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>affineUnit (X (R ⟨j,y⟩)-X (L ⟨i,x⟩))) := by
  simp only [SeparationInfinity.rawInverseKernelUnit,SeparationInfinity.rawFactor,
    rectangular,map_prod,map_zpow,affineUnit_map,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,
    map_sub,rename_X,Sum.elim_inl,Sum.elim_inr]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourKernelCancellation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma fourReverseRectangle (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    rectangular (fun i j=>(a i j:ℤ))
      (fun i j x y=>-fourAffine d₁ e₁ d₂ e₂ j i (.inr y) (.inl x))=
    (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^
      (∑ i,∑ j,(a i j:ℤ)*(d₂ i:ℤ)*(e₁ j:ℤ)) *
    rectangular (fun i j=>(a j i:ℤ))
      (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) := by
  conv_lhs => arg 2; ext i j x y; rw [←neg_one_mul]
  rw [rectangular_scalar_mul]
  simp only [Fintype.card_fin]
  congr 1
  exact rectangular_transpose (fun i j=>(a j i:ℤ)) _

lemma fourCrossAffineUnit_signed (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourCrossAffineUnit a d₁ e₁ d₂ e₂=
    (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^ eulerForm a d₂ e₁ *
      (rectangular (fun i j : I=>if i=j then 1 else 0)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) *
      rectangular (fun i j : I=>if i=j then 1 else 0)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) *
      rectangular (fun i j=>(a i j:ℤ))
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inr y)) *
      rectangular (fun i j=>(a j i:ℤ))
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y))) := by
  rw [fourCrossAffineUnit,fourReverseRectangle]
  have he : ((∑ i,e₁ i*d₂ i : ℕ):ℤ)-(∑ i,∑ j,(a i j:ℤ)*(d₂ i:ℤ)*(e₁ j:ℤ))=eulerForm a d₂ e₁ := by
    simp only [eulerForm,Nat.cast_sum,Nat.cast_mul]
    congr 1
    exact Finset.sum_congr rfl (fun i hi=>mul_comm _ _)
  rw [←he,←unit_neg_one_zpow_sub,zpow_natCast]
  exact mul_sign_collect (G := (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) _ _ _ _ _ _

lemma fourKernel_cancellation (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂=
    (-1 : (LaurentSeries (MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ))ˣ) ^ eulerForm a d₂ e₁ *
      (rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) *
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) *
      (rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) *
      (rectangular (SeparationInfinity.inverseExponent (fun i j=>a j i))
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)))⁻¹)) := by
  rw [fourCrossAffineUnit_signed]
  rw [mul_left_comm]
  apply congrArg (_ * ·)
  exact four_rectangle_cancellation (fun i j : I=>if i=j then 1 else 0)
    (fun i j=>(a i j:ℤ)) (fourAffine d₁ e₁ d₂ e₂)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourTensorKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
noncomputable local instance kernelTensorDistrib_r4ca2a2_1 (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourAlg
noncomputable local instance kernelTensorSelf_r4ca2a2_1 (d e : I → ℕ) :
    Module (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) := Semiring.toModule
noncomputable local instance kernelTensorNonUnital_r4ca2a2_1 (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (kernelTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance kernelFourNonUnital_r4ca2a2_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (kernelFourRing d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring
lemma fourKernel_lift_naturality (a : I → I → ℕ) (d e d₁ e₁ d₂ e₂ : I → ℕ)
    (F : S d⊗[ℚ]S e →ₐ[ℚ] (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))
    (r : CellVars d e → CellVars d₁ e₁⊕CellVars d₂ e₂)
    (h : ∀ x,fourValueAlg d₁ e₁ d₂ e₂ (F x)=rename r (tensorValue d e x)) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S d⊗[ℚ]S e) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) F.toRingHom).toMonoidHom (SeparationInfinity.inverseKernelUnit a d e))=
    Units.map (mapRing (rename r).toRingHom).toMonoidHom (SeparationInfinity.rawInverseKernelUnit a d e) := by
  apply Units.ext
  apply HahnSeries.ext
  funext k
  change fourValueAlg d₁ e₁ d₂ e₂ (F ((SeparationInfinity.inverseKernelUnit a d e).val.coeff k))=
    rename r ((SeparationInfinity.rawInverseKernelUnit a d e).val.coeff k)
  rw [h]
  have hr := congrArg (fun x : LaurentSeries (MvPolynomial (CellVars d e) ℚ)=>x.coeff k)
    (SeparationInfinity.realize_inverseKernelUnit a d e)
  exact congrArg (rename r) hr

lemma fourKernel_firstColumn (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S d₁⊗[ℚ]S d₂) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a d₁ d₂))=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) := by
  refine Eq.trans (fourKernel_lift_naturality a d₁ d₂ d₁ e₁ d₂ e₂
    ( firstColumnAlg d₁ e₁ d₂ e₂ ) _ (fourValue_firstColumn d₁ e₁ d₂ e₂)) ?_
  have he : firstColumnVars d₁ e₁ d₂ e₂ =
      Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl) := by
    funext x; cases x <;> rfl
  rw [he]
  have h := rawKernel_rename (σ:=CellVars d₁ e₁⊕CellVars d₂ e₂) a d₁ d₂
    (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
  simpa only [fourAffine,fourForwardDifference,Function.comp_apply,
    Equiv.sigmaSumDistrib_apply,Sum.map_inl,Sum.map_inr,firstColumnVars,secondColumnVars,crossingColumnVars] using h

lemma fourKernel_crossingColumn (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S e₁⊗[ℚ]S d₂) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (crossingColumnAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a e₁ d₂))=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) := by
  refine Eq.trans (fourKernel_lift_naturality a e₁ d₂ d₁ e₁ d₂ e₂
    ( crossingColumnAlg d₁ e₁ d₂ e₂ ) _ (fourValue_crossingColumn d₁ e₁ d₂ e₂)) ?_
  have h := rawKernel_rename (σ:=CellVars d₁ e₁⊕CellVars d₂ e₂) a e₁ d₂
    (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl)
  simpa only [fourAffine,fourForwardDifference,Function.comp_apply,
    Equiv.sigmaSumDistrib_apply,Sum.map_inl,Sum.map_inr,firstColumnVars,secondColumnVars,crossingColumnVars] using h

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
lemma fourSeriesValue_first (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourFirstInverseUnit a d₁ e₁ d₂ e₂)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inl x) (.inl y)) :=
  fourKernel_firstColumn a d₁ e₁ d₂ e₂

lemma fourSeriesValue_crossing (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourCrossingInverseUnit a d₁ e₁ d₂ e₂)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inl y)) :=
  fourKernel_crossingColumn a d₁ e₁ d₂ e₂

lemma units_map_neg_one {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Units.map f.toMonoidHom (-1 : Rˣ)=(-1 : Sˣ) := by
  apply Units.ext
  change f (-1) = -1
  rw [map_neg,map_one]

lemma ring_map_unit_val {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (u : Rˣ) :
    f u.val = (Units.map f.toMonoidHom u).val := rfl

lemma ring_map_signedUnits {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B C D : Rˣ) (w : ℤ) :
    f (((-1)^w*(A*B*(C*D⁻¹))).val)=
    ((-1)^w*(Units.map f.toMonoidHom A*Units.map f.toMonoidHom B*
      (Units.map f.toMonoidHom C*(Units.map f.toMonoidHom D)⁻¹))).val := by
  rw [ring_map_unit_val]
  simp only [map_mul,map_inv,map_zpow,units_map_neg_one]

lemma fourSeriesValue_kernelRHS (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom
      (fourTensorKernelRHS a d₁ e₁ d₂ e₂)=
    fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂ := by
  apply Units.ext
  change fourSeriesValue d₁ e₁ d₂ e₂ (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val = _
  unfold fourTensorKernelRHS
  rw [ring_map_signedUnits]
  apply congrArg Units.val
  refine Eq.trans ?_ (fourKernel_cancellation a d₁ e₁ d₂ e₂).symm
  apply congrArg ((-1)^eulerForm a d₂ e₁ * ·)
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (fourSeriesValue_first a d₁ e₁ d₂ e₂)
      (fourSeriesValue_second a d₁ e₁ d₂ e₂))
    (congrArg₂ (· * ·) (fourSeriesValue_crossing a d₁ e₁ d₂ e₂)
      (congrArg Inv.inv (fourSeriesValue_crossing (fun i j=>a j i) d₁ e₁ d₂ e₂)))

lemma fourSeriesValue_kernelRHS_val_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourSeriesValue d₁ e₁ d₂ e₂ (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val=
    (fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂).val :=
  congrArg Units.val (fourSeriesValue_kernelRHS a d₁ e₁ d₂ e₂)

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val_oai.{u_1}
