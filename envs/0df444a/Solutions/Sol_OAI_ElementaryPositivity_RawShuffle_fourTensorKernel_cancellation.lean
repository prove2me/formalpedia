-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:13.666634+00:00
-- url     : https://prove2.me/submissions/997c0bbb-f1df-4191-a070-280bd3849e6c

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourSeriesValue_cross
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourSeriesValue_kernelRHS_val

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ShuffleProjection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma cutSplit_pack {d e : I → ℕ} (A : Cut d e) (i : I)
    (x : Fin (d i)⊕Fin (e i)) :
    (cutSplit A).symm ⟨i,packSplit A i x⟩=(Equiv.sigmaSumDistrib _ _) ⟨i,x⟩ := by
  apply (cutSplit A).injective
  rw [Equiv.apply_symm_apply]
  cases x <;> rfl

omit [Fintype I] in
lemma rowSplit_rawFactor (a : I → I → ℕ) {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) (i j : I)
    (x : Fin (d₁ i)⊕Fin (e₁ i)) (y : Fin (d₂ j)⊕Fin (e₂ j)) :
    Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
      (SeparationInfinity.rawFactor a (d₁+e₁) (d₂+e₂) i j (packSplit A i x) (packSplit B j y))=
      fourAffine d₁ e₁ d₂ e₂ i j x y ^ SeparationInfinity.inverseExponent a i j := by
  unfold SeparationInfinity.rawFactor
  rw [map_zpow,affineUnit_map]
  congr 2
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,map_sub,rename_X,rowSplitEquiv,
    Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,cutSplit_pack]
  rfl

lemma rowSplit_inverseKernel (a : I → I → ℕ) {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
      (SeparationInfinity.rawInverseKernelUnit a (d₁+e₁) (d₂+e₂))=
      fourTotalInverseUnit a d₁ e₁ d₂ e₂ := by
  simp only [SeparationInfinity.rawInverseKernelUnit,map_prod,fourTotalInverseUnit,rectangular]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  calc
    _ = ∏ x : Fin (d₁ i)⊕Fin (e₁ i), ∏ y : Fin (d₂ j+e₂ j),
        Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
          (SeparationInfinity.rawFactor a (d₁+e₁) (d₂+e₂) i j (packSplit A i x) y) :=
      (Equiv.prod_comp (packSplit A i) _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro x hx
      calc
        _ = ∏ y : Fin (d₂ j)⊕Fin (e₂ j),
            Units.map (mapRing (rename (rowSplitEquiv A B)).toRingHom).toMonoidHom
              (SeparationInfinity.rawFactor a (d₁+e₁) (d₂+e₂) i j (packSplit A i x) (packSplit B j y)) :=
          (Equiv.prod_comp (packSplit B j) _).symm
        _ = _ := Finset.prod_congr rfl (fun y hy=>rowSplit_rawFactor a A B i j x y)

noncomputable local instance rowTensorRing_rd16985_1 (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance rowTensorAlgebra_rd16985_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance rowFourRing_rd16985_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance rowFourAlgebra_rd16985_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
lemma fourValue_restrictRows {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) (x : S (d₁+e₁)⊗[ℚ]S (d₂+e₂)) :
    fourValue d₁ e₁ d₂ e₂ (restrictRows d₁ e₁ d₂ e₂ A B x)=
      rename (rowSplitEquiv A B) (tensorValue (d₁+e₁) (d₂+e₂) x) := by
  change fourValue d₁ e₁ d₂ e₂ (TensorProduct.map (restrictTensor A) (restrictTensor B) x)=_
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    change fourValue d₁ e₁ d₂ e₂ (restrictTensor A x⊗ₜ[ℚ]restrictTensor B y)=_
    rw [fourValue_tmul,tensorValue_restrictTensor,tensorValue_restrictTensor,tensorValue_tmul]
    simp only [map_mul,rename_rename]
    rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourTensorKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
noncomputable local instance kernelTensorDistrib_rd16985_1 (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourAlg
noncomputable local instance kernelTensorSelf_rd16985_1 (d e : I → ℕ) :
    Module (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) := Semiring.toModule
noncomputable local instance kernelTensorNonUnital_rd16985_1 (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (kernelTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance kernelFourNonUnital_rd16985_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
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

lemma fourKernel_restrictRows (a : I → I → ℕ) {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S (d₁+e₁)⊗[ℚ]S (d₂+e₂)) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (restrictRows d₁ e₁ d₂ e₂ A B).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a (d₁+e₁) (d₂+e₂)))=
      fourTotalInverseUnit a d₁ e₁ d₂ e₂ := by
  rw [fourKernel_lift_naturality a _ _ _ _ _ _ _ _ (fourValue_restrictRows A B)]
  exact rowSplit_inverseKernel a A B

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma fourTotalInverseUnit_zero (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourTotalInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂=fourClearingUnit d₁ e₁ d₂ e₂ := by
  unfold fourTotalInverseUnit fourClearingUnit
  congr 1
  funext i j
  simp only [SeparationInfinity.inverseExponent,Nat.cast_zero,sub_zero]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorDistrib
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorSelf
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelSeriesRing
lemma fourSeriesValue_injective (d₁ e₁ d₂ e₂ : I → ℕ) :
    Function.Injective (fourSeriesValue d₁ e₁ d₂ e₂) :=
  mapRing_injective (fourValueAlg d₁ e₁ d₂ e₂).toRingHom (fourValue_injective d₁ e₁ d₂ e₂)

lemma fourSeriesValue_rows (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B)=
      fourTotalInverseUnit a d₁ e₁ d₂ e₂ := fourKernel_restrictRows a A B

lemma fourSeriesValue_rows_val (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    fourSeriesValue d₁ e₁ d₂ e₂ (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val=
      (fourTotalInverseUnit a d₁ e₁ d₂ e₂).val :=
  congrArg Units.val (fourSeriesValue_rows a d₁ e₁ d₂ e₂ A B)

lemma fourSeriesValue_rows_inv_val (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    fourSeriesValue d₁ e₁ d₂ e₂ ((fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B)⁻¹).val=
      ((fourTotalInverseUnit a d₁ e₁ d₂ e₂)⁻¹).val :=
  congrArg (fun u=> (u⁻¹).val) (fourSeriesValue_rows a d₁ e₁ d₂ e₂ A B)

lemma fourSeriesValue_kernelLHS (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    fourSeriesValue d₁ e₁ d₂ e₂
      ((fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val *
        ((fourRowsInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂ A B)⁻¹).val *
        polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)))=
    (fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := by
  rw [(fourSeriesValue d₁ e₁ d₂ e₂).map_mul,(fourSeriesValue d₁ e₁ d₂ e₂).map_mul,
    fourSeriesValue_rows_val,fourSeriesValue_rows_inv_val,fourTotalInverseUnit_zero,fourSeriesValue_cross]
  rfl

lemma fourTensorKernel_cancellation_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val *
      ((fourRowsInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂ A B)⁻¹).val *
      polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
    (((-1 : (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ)^eulerForm a d₂ e₁) *
      (fourFirstInverseUnit a d₁ e₁ d₂ e₂ *
        fourSecondInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹))).val := by
  apply fourSeriesValue_injective d₁ e₁ d₂ e₂
  exact (fourSeriesValue_kernelLHS a d₁ e₁ d₂ e₂ A B).trans
    (fourSeriesValue_kernelRHS_val a d₁ e₁ d₂ e₂).symm

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation_oai.{u_1}
