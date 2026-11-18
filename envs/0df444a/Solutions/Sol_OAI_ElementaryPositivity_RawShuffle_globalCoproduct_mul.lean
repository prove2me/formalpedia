-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:28.819483+00:00
-- url     : https://prove2.me/submissions/e5c48755-3a33-4540-be4a-33dfc04f8eb1

import Mathlib
import Definitions.Def_OAIQ368Chrom035
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_unitalSeparationConstant_shuffle_leading_all

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionGrid
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*}

open DimensionSplit

attribute [local instance] Classical.propDecidable

lemma sum_transposeDimensionGrid [Fintype I] [DecidableEq I] (d e α β : I → ℕ)
    {M : Type*} [AddCommMonoid M] (F : ColumnDimensionGrid d e α β → M) :
    ∑ s : RowDimensionGrid d e α β, F (transposeDimensionGrid d e α β s) =
      ∑ s : ColumnDimensionGrid d e α β, F s := by
  classical
  exact Equiv.sum_comp (transposeDimensionGrid d e α β) F

lemma sum_transposeDimensionGrid_congr [Fintype I] [DecidableEq I] (d e α β : I → ℕ)
    {M : Type*} [AddCommMonoid M] (F : RowDimensionGrid d e α β → M)
    (G : ColumnDimensionGrid d e α β → M)
    (h : ∀ s,F s=G (transposeDimensionGrid d e α β s)) :
    ∑ s : RowDimensionGrid d e α β,F s=∑ s : ColumnDimensionGrid d e α β,G s := by
  classical
  calc
    _=∑ s : RowDimensionGrid d e α β,G (transposeDimensionGrid d e α β s) := by
      apply Finset.sum_congr rfl
      intro s _
      exact h s
    _=_ := sum_transposeDimensionGrid d e α β G

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedCoproductGridGrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]
lemma mk_eq_mk_iff_sub_mem (F G : Submodule ℚ M) (x y : F) :
    mk F G x = mk F G y ↔ x.val-y.val∈G := by
  rw [←sub_eq_zero,←map_sub]
  exact Submodule.Quotient.mk_eq_zero _
end ElementaryPositivity.LinearFiltration

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)] in
lemma sum_cutShapeDimensionEquiv {d : I → ℕ} {s : Pack (A:=A)}
    (R : Realization d s) {M : Type*} [AddCommMonoid M] (F : DimensionSplit d → M) :
    ∑ u : CutShape s,F (cutShapeDimensionEquiv R u)=∑ u : DimensionSplit d,F u :=
  Equiv.sum_comp (cutShapeDimensionEquiv R) F

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma cast_cellLeadingB_congr (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {p q r s p' q' r' s' : I → ℕ}
    (hp : p=p') (hq : q=q') (hr : r=r') (hs : s=s')
    (h₁ : p+q=α) (h₂ : r+s=β) (h₁' : p'+q'=α) (h₂' : r'+s'=β)
    (hon : CellsOnSlope c η θ p q r s) (hon' : CellsOnSlope c η θ p' q' r' s') :
    castBTensor a (slope c η) h₁ h₂ (cellLeadingB a c η hc θ p q r s hon f g)=
      castBTensor a (slope c η) h₁' h₂' (cellLeadingB a c η hc θ p' q' r' s' hon' f g) := by
  subst p'; subst q'; subst r'; subst s'
  rfl

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [∀ index, Fintype (A index)] in
lemma gridLeadingB_eq_dimensionLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization α (PackConvolution.left p))
    (T : Realization β (PackConvolution.right p)) :
    gridLeadingB a c η hc θ f g p R T=dimensionLeadingB (α:=α) (β:=β) a c η hc θ f g := by
  unfold gridLeadingB dimensionLeadingB
  calc
    _=∑ u : CutShape (PackConvolution.left p),∑ v : CutShape (PackConvolution.right p),
      dimensionRowLeadingB a c η hc θ f g (cutShapeDimensionEquiv R u) (cutShapeDimensionEquiv T v) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        unfold dimensionRowLeadingB gridShapeLeadingB
        split_ifs with hon hon'
        · exact cast_cellLeadingB_congr a c η hc θ f g rfl
            (cutShapeDimensionEquiv_right R u).symm rfl
            (cutShapeDimensionEquiv_right T v).symm _ _ _ _ hon hon'
        · exact False.elim (hon' (by simpa only [cutShapeDimensionEquiv_left,
            cutShapeDimensionEquiv_right] using hon))
        · rename_i hon'
          exact False.elim (hon (by simpa only [cutShapeDimensionEquiv_left,
            cutShapeDimensionEquiv_right] using hon'))
        · rfl
    _=_ := by
      simp_rw [sum_cutShapeDimensionEquiv]
      exact sum_cutShapeDimensionEquiv R (fun u =>
        ∑ v : DimensionSplit β,dimensionRowLeadingB a c η hc θ f g u v)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DimensionColumnLeading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma sum_subtype_of_zero_off {X M : Type*} [Fintype X] [AddCommMonoid M]
    (p : X → Prop) [DecidablePred p] (f : X → M) (hf : ∀ x,¬p x → f x=0) :
    ∑ x,f x=∑ x : {x // p x},f x.val := by
  rw [←Fintype.sum_subtype_add_sum_subtype p f]
  have hzero : ∑ x : {x // ¬p x},f x.val=0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hf x.val x.property
  rw [hzero,add_zero]

lemma dimensionRowLeadingB_zero_of_mismatch (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (u : DimensionSplit α) (v : DimensionSplit β)
    (h : ¬(left u+left v=d ∧ right u+right v=e)) :
    dimensionRowLeadingB a c η hc θ f g u v=0 := by
  unfold dimensionRowLeadingB
  split_ifs with hon
  · rw [cellLeadingB,dite_eq_right h]
    exact (castBTensor a (slope c η) (left_add_right u) (left_add_right v)).map_zero
  · rfl

lemma dimensionColumnLeadingB_transpose (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    (s : RowDimensionGrid d e α β) :
    dimensionColumnLeadingB a c η hc θ f g (transposeDimensionGrid d e α β s)=
      dimensionRowLeadingB a c η hc θ f g s.val.1 s.val.2 := by
  unfold dimensionColumnLeadingB dimensionRowLeadingB
  split_ifs with hon hon'
  · exact cast_cellLeadingB_congr a c η hc θ f g rfl rfl
      (transposeDimensionGrid_first_right d e α β s)
      (transposeDimensionGrid_second_right d e α β s) _ _ _ _ hon hon'
  · exact False.elim (hon' (by simpa only [transposeDimensionGrid_first_left,
      transposeDimensionGrid_second_left,transposeDimensionGrid_first_right,
      transposeDimensionGrid_second_right] using hon))
  · rename_i hon'
    exact False.elim (hon (by simpa only [transposeDimensionGrid_first_left,
      transposeDimensionGrid_second_left,transposeDimensionGrid_first_right,
      transposeDimensionGrid_second_right] using hon'))
  · rfl

lemma double_sum_eq_column_grid {M : Type*} [AddCommMonoid M]
    (d e α β : I → ℕ) (F : DimensionSplit α → DimensionSplit β → M)
    (G : ColumnDimensionGrid d e α β → M)
    (hz : ∀ u v,¬(left u+left v=d ∧ right u+right v=e) → F u v=0)
    (hg : ∀ s : RowDimensionGrid d e α β,
      F s.val.1 s.val.2=G (transposeDimensionGrid d e α β s)) :
    ∑ u,∑ v,F u v=∑ s,G s := by
  rw [←Fintype.sum_prod_type' F]
  rw [sum_subtype_of_zero_off
    (fun s : DimensionSplit α × DimensionSplit β=>left s.1+left s.2=d ∧ right s.1+right s.2=e)
    (fun s=>F s.1 s.2) (fun s hs=>hz s.1 s.2 hs)]
  exact sum_transposeDimensionGrid_congr d e α β (fun s=>F s.val.1 s.val.2) G hg

theorem dimensionLeadingB_eq_column_sum (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e) :
    dimensionLeadingB (α:=α) (β:=β) a c η hc θ f g=
      ∑ s : ColumnDimensionGrid d e α β,dimensionColumnLeadingB a c η hc θ f g s := by
  exact double_sum_eq_column_grid d e α β
    (dimensionRowLeadingB a c η hc θ f g) (dimensionColumnLeadingB a c η hc θ f g)
    (fun u v h=>dimensionRowLeadingB_zero_of_mismatch a c η hc θ f g u v h)
    (fun s=>(dimensionColumnLeadingB_transpose a c η hc θ f g s).symm)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open ElementaryPositivity.LinearFiltration
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

theorem unitalSeparationConstant_shuffle_column (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc (hα.compatible hβ)
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0-
      ∑ s : ColumnDimensionGrid d e α β,dimensionColumnLeadingB a c η hc θ f g s∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  have hdiff:=unitalSeparationConstant_shuffle_leading_all a c η hc θ hχ h U V f g hf hg hα hβ hd R
  rw [gridLeadingB_eq_dimensionLeadingB,dimensionLeadingB_eq_column_sum] at hdiff
  exact hdiff
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
open ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma signedCellGradeMultiply_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (U V : ℤ)
    (x : unitalSourceTensorFiltration a c η hc θ d₁ d₂ U)
    (y : unitalSourceTensorFiltration a c η hc θ e₁ e₂ V) :
    signedCellGradeMultiply a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)=
      (Submodule.Quotient.mk ⟨signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon x.val y.val,
        signedCellMultiplyB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V x.val y.val x.property y.property⟩ :
        UnitalSourceTensorGrade a c η hc θ (d₁+e₁) (d₂+e₂) (U+V)) := rfl

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open DimensionSplit SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma unitalTensorFiltrationCast_val (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V)
    (x : unitalSourceTensorFiltration a c η hc θ d e U) :
    (unitalTensorFiltrationCast a c η hc θ h k w x).val=
      castBTensor a (slope c η) h k x.val := by
  subst d'; subst e'; subst V
  rfl

lemma unitalTensorGradeCast_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e d' e' : I → ℕ} {U V : ℤ}
    (h : d=d') (k : e=e') (w : U=V)
    (x : unitalSourceTensorFiltration a c η hc θ d e U) :
    unitalTensorGradeCast a c η hc θ h k w (Submodule.Quotient.mk x)=
      (Submodule.Quotient.mk (unitalTensorFiltrationCast a c η hc θ h k w x) :
        UnitalSourceTensorGrade a c η hc θ d' e' V) := by
  subst d'; subst e'; subst V
  rfl

lemma splitCoproductGrade_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ)
    (x : unitalSourceFiltration a c η hc θ d W) :
    splitCoproductGrade a c η hc θ p hp W (Submodule.Quotient.mk x)=
      (Submodule.Quotient.mk (splitCoproductFiltration a c η hc θ p hp W x) :
        UnitalSourceTensorGrade a c η hc θ (left p) (right p) W) := by
  exact congrArg (unitalGradeCoproduct a c η hc θ (left p) (right p) (hp.1.compatible hp.2) W)
    (unitalGradeCast_mk a c η hc θ (left_add_right p).symm rfl x)

lemma splitCoproductFiltration_val (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ)
    (x : unitalSourceFiltration a c η hc θ d W) :
    (splitCoproductFiltration a c η hc θ p hp W x).val=
      unitalSeparationConstant a c η hc (left p) (right p) (hp.1.compatible hp.2)
        (castB a (slope c η) (left_add_right p).symm x.val) := by
  change unitalSeparationConstant a c η hc _ _ _
    (unitalFiltrationCast a c η hc θ (left_add_right p).symm rfl x).val=_
  rw [unitalFiltrationCast_val]

lemma splitCoproductFiltration_val_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d : I → ℕ} (p : DimensionSplit d)
    (hp : OnSlopeOrZero c η θ (left p) ∧ OnSlopeOrZero c η θ (right p)) (W : ℤ)
    (f : S d) (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d W) :
    (splitCoproductFiltration a c η hc θ p hp W ⟨_,hf⟩).val=
      (unitalSeparationSeries a c η hc (hp.1.compatible hp.2)
        (quotientAlg a (slope c η) (left p+right p) (castS (left_add_right p).symm f))).coeff 0 := by
  rw [splitCoproductFiltration_val,castB_mk]
  rfl

lemma columnGradeTerm_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ)
    (x : unitalSourceFiltration a c η hc θ d U)
    (y : unitalSourceFiltration a c η hc θ e V) (s : ColumnDimensionGrid d e α β) :
    columnGradeTerm a c η hc θ hχ U V (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) s=
      (Submodule.Quotient.mk (columnFiltrationTerm a c η hc θ hχ U V x y s) :
        UnitalSourceTensorGrade a c η hc θ α β (U+V)) := by
  unfold columnGradeTerm columnFiltrationTerm
  split_ifs with hon
  · rw [splitCoproductGrade_mk,splitCoproductGrade_mk,signedCellGradeMultiply_mk,unitalTensorGradeCast_mk]
  · rfl

lemma columnFiltrationTerm_val_mk (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    {d e α β : I → ℕ} (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    (s : ColumnDimensionGrid d e α β) :
    (columnFiltrationTerm a c η hc θ hχ U V ⟨_,hf⟩ ⟨_,hg⟩ s).val=
      dimensionColumnLeadingB a c η hc θ f g s := by
  unfold columnFiltrationTerm dimensionColumnLeadingB
  split_ifs with hon
  · rw [unitalTensorFiltrationCast_val,cellLeadingB,
      dite_eq_left ⟨left_add_right s.val.1,left_add_right s.val.2⟩]
    congr 1
    apply congrArg₂ (fun x y=>signedCellMultiplyB a c η hc θ _ _ _ _ hon x y)
    · exact splitCoproductFiltration_val_mk a c η hc θ _ _ U f hf
    · exact splitCoproductFiltration_val_mk a c η hc θ _ _ V g hg
  · rfl

theorem unitalGradeCoproduct_shuffle_column (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e)
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d U) (y : UnitalSourceGrade a c η hc θ e V) :
    unitalGradeCoproduct a c η hc θ α β (hα.compatible hβ) (U+V)
      (unitalGradeCast a c η hc θ h rfl (unitalGradeShuffle a c η hc θ hχ d e hd he U V x y))=
      ∑ s : ColumnDimensionGrid d e α β,columnGradeTerm a c η hc θ hχ U V x y s := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rcases x with ⟨x,hx⟩
      rcases y with ⟨y,hy⟩
      induction x using Submodule.Quotient.induction_on with
      | H f =>
        induction y using Submodule.Quotient.induction_on with
        | H g =>
          simp only [unitalGradeShuffle_mk,unitalGradeCast_mk,unitalGradeCoproduct_mk,
            columnGradeTerm_mk]
          change mk _ _ _=∑ s : ColumnDimensionGrid d e α β,
            mk _ _ (columnFiltrationTerm a c η hc θ hχ U V ⟨_,hx⟩ ⟨_,hy⟩ s)
          rw [←map_sum]
          apply (mk_eq_mk_iff_sub_mem _ _ _ _).mpr
          dsimp only [Subtype.coe_mk]
          rw [unitalFiltrationCast_val]
          have hv : (∑ s : ColumnDimensionGrid d e α β,
              columnFiltrationTerm a c η hc θ hχ U V ⟨_,hx⟩ ⟨_,hy⟩ s).val=
              ∑ s : ColumnDimensionGrid d e α β,dimensionColumnLeadingB a c η hc θ f g s := by
            rw [Submodule.coe_sum]
            exact Finset.sum_congr rfl (fun s _=>columnFiltrationTerm_val_mk a c η hc θ hχ U V f g hx hy s)
          rw [hv]
          change (unitalSeparationSeries a c η hc (hα.compatible hβ)
            (castB a (slope c η) h (quotientAlg a (slope c η) (d+e) (shufflePolynomial a f g)))).coeff 0-_∈_
          rw [castB_mk]
          let R : Realization (α+β) (A:=fun i=>Fin ((α+β) i)) (fun _=>Finset.univ) :=
            fun _=>(Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm
          exact unitalSeparationConstant_shuffle_column a c η hc θ hχ h U V f g hx hy hα hβ hd R

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorMiddleEnd
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma signedCellMultiplyB_tmul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (x : B a (slope c η) d₁) (y : B a (slope c η) d₂)
    (z : B a (slope c η) e₁) (w : B a (slope c η) e₂) :
    signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon (x⊗ₜ[ℚ]y) (z⊗ₜ[ℚ]w)=
      ((-1:ℚ)^eulerForm a d₂ e₁) •
        (shuffleBUnit a c η hc d₁ e₁ (hon.1.compatible hon.2.1) x z⊗ₜ[ℚ]
          shuffleBUnit a c η hc d₂ e₂ (hon.2.2.1.compatible hon.2.2.2) y w) := rfl

private lemma mk_eq_smul_of_val_eq {M : Type*} [AddCommGroup M] [Module ℚ M]
    (F G : Submodule ℚ M) (x y : F) (r : ℚ) (h : x.val=r • y.val) :
    mk F G x=r • mk F G y :=
  (congrArg (mk F G) (Subtype.ext h)).trans ((mk F G).map_smul r y)

lemma signedCellGradeMultiply_part (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d₁ e₁ d₂ e₂ : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (U V u v : ℤ)
    (x : UnitalSourceGrade a c η hc θ d₁ u)
    (y : UnitalSourceGrade a c η hc θ d₂ (U-u))
    (z : UnitalSourceGrade a c η hc θ e₁ v)
    (w : UnitalSourceGrade a c η hc θ e₂ (V-v)) :
    signedCellGradeMultiply a c η hc θ hχ d₁ e₁ d₂ e₂ hon U V
      (unitalTensorGradeInclusionW a c η hc θ d₁ d₂ U u (x⊗ₜ[ℚ]y))
      (unitalTensorGradeInclusionW a c η hc θ e₁ e₂ V v (z⊗ₜ[ℚ]w))=
    ((-1:ℚ)^eulerForm a d₂ e₁) •
      unitalTensorGradeInclusionW a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) (u+v)
        (unitalGradeShuffle a c η hc θ hχ d₁ e₁ hon.1 hon.2.1 u v x z⊗ₜ[ℚ]
          unitalGradeCast a c η hc θ rfl (show (U-u)+(V-v)=U+V-(u+v) by omega)
            (unitalGradeShuffle a c η hc θ hχ d₂ e₂ hon.2.2.1 hon.2.2.2 (U-u) (V-v) y w)) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        induction w using Submodule.Quotient.induction_on with
        | H w =>
          simp only [unitalGradeShuffle_mk,unitalGradeCast_mk,unitalTensorGradeInclusionW]
          apply mk_eq_smul_of_val_eq
          change signedCellMultiplyB a c η hc θ _ _ _ _ hon
            (x.val⊗ₜ[ℚ]y.val) (z.val⊗ₜ[ℚ]w.val)=
              ((-1:ℚ)^eulerForm a d₂ e₁) •
                (shuffleBUnit a c η hc d₁ e₁ _ x.val z.val⊗ₜ[ℚ]
                  (unitalFiltrationCast a c η hc θ rfl _ _).val)
          rw [unitalFiltrationCast_val]
          exact signedCellMultiplyB_tmul a c η hc θ d₁ e₁ d₂ e₂ hon x.val y.val z.val w.val

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalTensorGradeInclusion_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e d' e' : slopeDimensions c η hc θ} {U V : ℤ}
    (h : d.val=d'.val) (k : e.val=e'.val) (w : U=V)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val U) :
    globalTensorGradeInclusion a c η hc θ d' e' V (unitalTensorGradeCast a c η hc θ h k w x)=
      globalTensorGradeInclusion a c η hc θ d e U x := by
  have hd : d=d' := Subtype.ext h
  have he : e=e' := Subtype.ext k
  subst d'; subst e'; subst V
  rfl

lemma unitalLof_shuffle (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d+e,U+V)
      (unitalGradeShuffle a c η hc θ hχ.out d.val e.val (slopeDimensions_onSlope c η hc θ d) (slopeDimensions_onSlope c η hc θ e) U V x y)=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x *
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) y := by
  exact (DirectSum.of_mul_of (A:=unitalComponent a c η hc θ) (i:=(d,U)) (j:=(e,V)) x y).symm

lemma globalTensorGradeInclusion_part_add (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ)
    (d₁ e₁ d₂ e₂ : slopeDimensions c η hc θ) (W u : ℤ)
    (x : UnitalSourceGrade a c η hc θ (d₁.val+e₁.val) u)
    (y : UnitalSourceGrade a c η hc θ (d₂.val+e₂.val) (W-u)) :
    globalTensorGradeInclusion a c η hc θ (d₁+e₁) (d₂+e₂) W
      (unitalTensorGradeInclusionW a c η hc θ (d₁.val+e₁.val) (d₂.val+e₂.val) W u (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d₁+e₁,u) x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d₂+e₂,W-u) y := by
  have h := globalTensorGradeInclusion_part a c η hc θ (d₁+e₁) (d₂+e₂) W u x y
  simpa only [AddSubmonoid.coe_add] using h

theorem globalTensorGradeInclusion_signedProduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d₁ e₁ d₂ e₂ : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d₁.val d₂.val U)
    (y : UnitalSourceTensorGrade a c η hc θ e₁.val e₂.val V) :
    globalTensorGradeInclusion a c η hc θ (d₁+e₁) (d₂+e₂) (U+V)
      (signedCellGradeMultiply a c η hc θ hχ.out d₁.val e₁.val d₂.val e₂.val
        (slopeDimensions_cellsOnSlope c η hc θ d₁ e₁ d₂ e₂) U V x y)=
    globalSignedTensorMultiply a c η hc θ
      (globalTensorGradeInclusion a c η hc θ d₁ d₂ U x)
      (globalTensorGradeInclusion a c η hc θ e₁ e₂ V y) := by
  induction x using unitalTensorGrade_induction a c η hc θ d₁.val d₂.val U with
  | hz => simp only [map_zero,LinearMap.zero_apply]
  | ha x x' hx hx' => simp only [map_add,LinearMap.add_apply,hx,hx']
  | ht u x₁ x₂ =>
    induction y using unitalTensorGrade_induction a c η hc θ e₁.val e₂.val V with
    | hz => simp only [map_zero]
    | ha y y' hy hy' => simp only [map_add,hy,hy']
    | ht v y₁ y₂ =>
      rw [signedCellGradeMultiply_part a c η hc θ hχ.out d₁.val e₁.val d₂.val e₂.val
        (slopeDimensions_cellsOnSlope c η hc θ d₁ e₁ d₂ e₂) U V u v x₁ x₂ y₁ y₂,
        map_smul,globalTensorGradeInclusion_part a c η hc θ d₁ d₂,
        globalTensorGradeInclusion_part a c η hc θ e₁ e₂]
      rw [globalTensorGradeInclusion_part_add,globalSignedTensorMultiply_tmul_lof]
      rw [unitalLof_cast a c η hc θ (d:=d₂+e₂) (e:=d₂+e₂)
        rfl (show (U-u)+(V-v)=U+V-(u+v) by omega)]
      rw [unitalLof_shuffle,unitalLof_shuffle]

lemma globalTensorGradeInclusion_signedProduct_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d₁ e₁ d₂ e₂ α β : slopeDimensions c η hc θ) (U V : ℤ)
    (hα : (d₁+e₁).val=α.val) (hβ : (d₂+e₂).val=β.val)
    (x : UnitalSourceTensorGrade a c η hc θ d₁.val d₂.val U)
    (y : UnitalSourceTensorGrade a c η hc θ e₁.val e₂.val V) :
    globalTensorGradeInclusion a c η hc θ α β (U+V)
      (unitalTensorGradeCast a c η hc θ hα hβ rfl
        (signedCellGradeMultiply a c η hc θ hχ.out d₁.val e₁.val d₂.val e₂.val
          (slopeDimensions_cellsOnSlope c η hc θ d₁ e₁ d₂ e₂) U V x y))=
    globalSignedTensorMultiply a c η hc θ
      (globalTensorGradeInclusion a c η hc θ d₁ d₂ U x)
      (globalTensorGradeInclusion a c η hc θ e₁ e₂ V y) := by
  exact (globalTensorGradeInclusion_cast a c η hc θ
    (d:=d₁+e₁) (e:=d₂+e₂) (d':=α) (e':=β) hα hβ rfl _).trans
      (globalTensorGradeInclusion_signedProduct a c η hc θ d₁ e₁ d₂ e₂ U V x y)

lemma globalRawColumnProduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d₁ e₁ d₂ e₂ α β : I → ℕ) (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (hα : d₁+e₁=α) (hβ : d₂+e₂=β)
    (hA : OnSlopeOrZero c η θ α) (hB : OnSlopeOrZero c η θ β) (U V : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d₁ d₂ U)
    (y : UnitalSourceTensorGrade a c η hc θ e₁ e₂ V) :
    globalTensorGradeInclusion a c η hc θ ⟨α,hA⟩ ⟨β,hB⟩ (U+V)
      (unitalTensorGradeCast a c η hc θ hα hβ rfl
        (signedCellGradeMultiply a c η hc θ hχ.out d₁ e₁ d₂ e₂ hon U V x y))=
    globalSignedTensorMultiply a c η hc θ
      (globalTensorGradeInclusion a c η hc θ ⟨d₁,hon.1⟩ ⟨d₂,hon.2.2.1⟩ U x)
      (globalTensorGradeInclusion a c η hc θ ⟨e₁,hon.2.1⟩ ⟨e₂,hon.2.2.2⟩ V y) := by
  have h := globalTensorGradeInclusion_signedProduct_cast a c η hc θ
    ⟨d₁,hon.1⟩ ⟨e₁,hon.2.1⟩ ⟨d₂,hon.2.2.1⟩ ⟨e₂,hon.2.2.2⟩
    ⟨α,hA⟩ ⟨β,hB⟩ U V hα hβ x y
  simp only at h
  exact h

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SlopeGridSum
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma sum_dite_zero_subtype {A M : Type*} [Fintype A] [AddCommMonoid M]
    (p : A → Prop) [DecidablePred p] (F : ∀ x,p x → M) :
    (∑ x,if h : p x then F x h else 0)=∑ x : {x // p x},F x.val x.property := by
  have h := (Fintype.sum_subtype_add_sum_subtype p (fun x=>if h:p x then F x h else 0)).symm
  refine h.trans ?_
  have hn : (∑ x : {x // ¬p x},if hx:p x.val then F x.val hx else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact dite_eq_right x.property
  rw [hn,add_zero]
  exact Finset.sum_congr rfl (fun x _=>dite_eq_left x.property)

lemma sum_slope_column (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    {M : Type*} [AddCommMonoid M]
    (F : SlopeSplit c η hc θ d → SlopeSplit c η hc θ e → M) :
    (∑ t : SlopeSplit c η hc θ (d+e),
      ∑ s : ColumnDimensionGrid d e (left t.val) (right t.val),
        if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
          F ⟨s.val.1,hon.1,hon.2.2.1⟩ ⟨s.val.2,hon.2.1,hon.2.2.2⟩
        else 0)=∑ p : SlopeSplit c η hc θ d,∑ q : SlopeSplit c η hc θ e,F p q := by
  calc
    _=∑ z : (Σ t : SlopeSplit c η hc θ (d+e),
        SlopeColumnGrid c η θ d e (left t.val) (right t.val)),
        F (slopeColumnEquiv c η hc θ d e z).1 (slopeColumnEquiv c η hc θ d e z).2 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro t _
      exact sum_dite_zero_subtype _ _
    _=∑ z : SlopeSplit c η hc θ d × SlopeSplit c η hc θ e,F z.1 z.2 :=
      Equiv.sum_comp (slopeColumnEquiv c η hc θ d e) (fun z=>F z.1 z.2)
    _=_ := Fintype.sum_prod_type _

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma globalSplitCoproduct_eq (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d : slopeDimensions c η hc θ) (W : ℤ)
    (s : SlopeSplit c η hc θ d.val) (x : UnitalSourceGrade a c η hc θ d.val W) :
    globalSplitCoproduct a c η hc θ (d,W) s x=
      globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ W
        (splitCoproductGrade a c η hc θ s.val s.property W x) := rfl

lemma globalColumnGradeTerm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V)
    (t : SlopeSplit c η hc θ (d.val+e.val))
    (s : ColumnDimensionGrid d.val e.val (left t.val) (right t.val)) :
    globalTensorGradeInclusion a c η hc θ ⟨left t.val,t.property.1⟩ ⟨right t.val,t.property.2⟩ (U+V)
      (columnGradeTerm a c η hc θ hχ.out U V x y s)=
    if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
      globalSignedTensorMultiply a c η hc θ
        (globalSplitCoproduct a c η hc θ (d,U) ⟨s.val.1,hon.1,hon.2.2.1⟩ x)
        (globalSplitCoproduct a c η hc θ (e,V) ⟨s.val.2,hon.2.1,hon.2.2.2⟩ y)
    else 0 := by
  unfold columnGradeTerm
  split_ifs with hon
  · rw [globalSplitCoproduct_eq,globalSplitCoproduct_eq]
    have h := globalRawColumnProduct a c η hc θ
      (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2)
      (left t.val) (right t.val) hon s.property.1 s.property.2 t.property.1 t.property.2 U V
      (splitCoproductGrade a c η hc θ s.val.1 ⟨hon.1,hon.2.2.1⟩ U x)
      (splitCoproductGrade a c η hc θ s.val.2 ⟨hon.2.1,hon.2.2.2⟩ V y)
    simpa only [Subtype.coe_mk] using h
  · exact map_zero _

lemma globalSplitCoproduct_shuffle (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V)
    (t : SlopeSplit c η hc θ (d.val+e.val)) :
    globalSplitCoproduct a c η hc θ (d+e,U+V) t
      (unitalGradeShuffle a c η hc θ hχ.out d.val e.val d.property e.property U V x y)=
      ∑ s : ColumnDimensionGrid d.val e.val (left t.val) (right t.val),
        if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
          globalSignedTensorMultiply a c η hc θ
            (globalSplitCoproduct a c η hc θ (d,U) ⟨s.val.1,hon.1,hon.2.2.1⟩ x)
            (globalSplitCoproduct a c η hc θ (e,V) ⟨s.val.2,hon.2.1,hon.2.2.2⟩ y)
        else 0 := by
  have h := congrArg (globalTensorGradeInclusion a c η hc θ
      ⟨left t.val,t.property.1⟩ ⟨right t.val,t.property.2⟩ (U+V))
    (unitalGradeCoproduct_shuffle_column a c η hc θ hχ.out (left_add_right t.val).symm
      d.property e.property t.property.1 t.property.2 U V x y)
  refine h.trans ?_
  rw [map_sum]
  exact Finset.sum_congr rfl (fun s _=>globalColumnGradeTerm a c η hc θ d e U V x y t s)

lemma globalCoproduct_mul_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
    (d e : slopeDimensions c η hc θ) (U V : ℤ)
    (x : UnitalSourceGrade a c η hc θ d.val U) (y : UnitalSourceGrade a c η hc θ e.val V) :
    globalCoproduct a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x *
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) y)=
      globalSignedTensorMultiply a c η hc θ
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,U) x))
        (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (e,V) y)) := by
  rw [←unitalLof_shuffle,globalCoproduct_lof,globalCoproduct_lof,globalCoproduct_lof]
  simp only [map_sum,LinearMap.sum_apply]
  calc
    _=∑ t : SlopeSplit c η hc θ (d.val+e.val),
      ∑ s : ColumnDimensionGrid d.val e.val (left t.val) (right t.val),
        if hon : CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2) then
          globalSignedTensorMultiply a c η hc θ
            (globalSplitCoproduct a c η hc θ (d,U) ⟨s.val.1,hon.1,hon.2.2.1⟩ x)
            (globalSplitCoproduct a c η hc θ (e,V) ⟨s.val.2,hon.2.1,hon.2.2.2⟩ y)
        else 0 := by
      exact Finset.sum_congr rfl (fun t _=>globalSplitCoproduct_shuffle a c η hc θ d e U V x y t)
    _=_ := by
      have h := sum_slope_column c η hc θ d.val e.val
        (fun p q=>globalSignedTensorMultiply a c η hc θ
          (globalSplitCoproduct a c η hc θ (d,U) p x)
          (globalSplitCoproduct a c η hc θ (e,V) q y))
      exact h.trans (Finset.sum_comm)

theorem globalCoproduct_mul_oai (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x y : UnitalShuffle a c η hc θ) :
    globalCoproduct a c η hc θ (x*y)=
      globalSignedTensorMultiply a c η hc θ
        (globalCoproduct a c η hc θ x) (globalCoproduct a c η hc θ y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_mul,map_zero,LinearMap.zero_apply]
  | add x x' hx hx' => simp only [add_mul,map_add,LinearMap.add_apply,hx,hx']
  | of k x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [mul_zero,map_zero]
    | add y y' hy hy' => simp only [mul_add,map_add,hy,hy']
    | of l y => exact globalCoproduct_mul_lof a c η hc θ k.1 l.1 k.2 l.2 x y

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul_oai.{u_1}
