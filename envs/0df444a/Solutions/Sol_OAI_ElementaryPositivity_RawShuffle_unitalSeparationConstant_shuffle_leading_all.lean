-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:25.425998+00:00
-- url     : https://prove2.me/submissions/3c9bba59-6396-4664-b03e-d7fb35d28091

import Mathlib
import Definitions.Def_OAIQ368Chrom035
import Definitions.Def_OAIQ368Chrom037
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_clearedSeparationB_cell

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CenterCoefficientMembership
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

lemma evalRat_mem_of_coeff (M : Submodule ℚ A) (p : MvPolynomial σ A)
    (hp : ∀ s,p.coeff s∈M) (v : σ → ℚ) : evalRat v p∈M := by
  classical
  rw [p.as_sum,map_sum]
  apply M.sum_mem
  intro s hs
  rw [evalRat_monomial]
  exact M.smul_mem _ (hp s)

end ElementaryPositivity.CenterCalculus

end

end OAI
end

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
lemma mapRing_rat_smul (f : R →ₐ[ℚ] S) (r : ℚ) (x : LaurentSeries R) :
    mapRing f.toRingHom (r • x)=r • mapRing f.toRingHom x := by
  apply HahnSeries.ext
  funext k
  simp only [mapRing_coeff,HahnSeries.coeff_smul]
  exact f.toLinearMap.map_smul r (x.coeff k)
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ClearingKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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

lemma rawInverseKernel_zero (d e : I → ℕ) :
    (SeparationInfinity.rawInverseKernelUnit (fun _ _ : I=>0) d e).val=
      ∏ i,∏ x : Fin (d i),∏ y : Fin (e i),
        (affineUnit (X (Sum.inr ⟨i,y⟩)-X (Sum.inl ⟨i,x⟩) : MvPolynomial (CellVars d e) ℚ)).val := by
  have h : SeparationInfinity.rawInverseKernelUnit (fun _ _ : I=>0) d e=
      rectangular (fun i j : I=>if i=j then 1 else 0)
        (fun i j x y=>affineUnit (X (Sum.inr ⟨j,y⟩)-X (Sum.inl ⟨i,x⟩) : MvPolynomial (CellVars d e) ℚ)) := by
    simp only [SeparationInfinity.rawInverseKernelUnit,SeparationInfinity.rawFactor,
      SeparationInfinity.inverseExponent,Nat.cast_zero,sub_zero,rectangular]
  rw [h,rectangular_diagonal]
  simp only [Units.coe_prod]

lemma polynomial_crossDifference (d e : I → ℕ) :
    polynomial (relativeRaw d e (crossDifference d e))=
      crossSign d e • (SeparationInfinity.rawInverseKernelUnit (fun _ _ : I=>0) d e).val := by
  rw [relativeRaw_crossDifference,rawInverseKernel_zero]
  rw [rat_smul_series]
  simp only [map_prod,crossSign,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro y hy
  simp only [map_add,polynomial_X,polynomial_C,affineUnit_val,map_neg,map_one,neg_one_mul]
  simp only [map_sub]
  ring

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearingTensorRing
noncomputable local instance clearingTensorAlg_rfa2d34_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
lemma polynomial_crossTensor (d e : I → ℕ) :
    polynomial (relativeTaylor d e (crossTensor d e))=
      crossSign d e • (SeparationInfinity.inverseKernelUnit (fun _ _ : I=>0) d e).val := by
  apply SeparationInfinity.realize_injective d e
  rw [polynomial_map,map_relativeTaylor,tensorValue_crossTensor]
  rw [mapRing_rat_smul,
    SeparationInfinity.realize_inverseKernelUnit,polynomial_crossDifference]

omit [DecidableEq I] in
lemma crossSign_sq (d e : I → ℕ) : crossSign d e * crossSign d e=1 := by
  rw [crossSign,←Finset.prod_mul_distrib]
  simp only [←Finset.prod_mul_distrib,neg_mul_neg,one_mul,Finset.prod_const_one]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_ClearedSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {R : Type*} [CommRing R] [Algebra ℚ R]
lemma polynomial_rat_smul (r : ℚ) (x : Polynomial R) :
    polynomial (r • x)=r • polynomial x := by
  rw [Algebra.smul_def,Polynomial.algebraMap_apply,map_mul,polynomial_C,rat_smul_series]
lemma rat_smul_mul (r : ℚ) (x y : LaurentSeries R) :
    (r • x)*y=r • (x*y) := by
  rw [rat_smul_series,rat_smul_series,mul_assoc]
end ElementaryPositivity.LaurentAtInfinity

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearedSepTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearedSepTensorAlg
lemma normalize_cleared_tensor (d e : I → ℕ) (x y : S d⊗[ℚ]S e)
    (h : crossTensor d e*x=crossSign d e • y) :
    (inverseKernelUnit (fun _ _ : I=>0) d e).val *
      polynomial (relativeTaylor d e x)=polynomial (relativeTaylor d e y) := by
  have H := congrArg (fun z=>polynomial (relativeTaylor d e z)) h
  rw [map_mul,map_mul,polynomial_crossTensor] at H
  have hs : relativeTaylor d e (crossSign d e • y)=
      crossSign d e • relativeTaylor d e y := (relativeTaylor d e).toLinearMap.map_smul _ _
  rw [hs,polynomial_rat_smul,rat_smul_mul] at H
  have H' := congrArg (fun z=>crossSign d e • z) H
  simpa only [smul_smul,crossSign_sq,one_smul] using H'

lemma separation_of_cleared (a : I → I → ℕ) (d e : I → ℕ) (x y : S d⊗[ℚ]S e)
    (h : crossTensor d e*x=crossSign d e • y) :
    (inverseKernelUnit a d e).val * polynomial (relativeTaylor d e x)=
    ((inverseKernelUnit a d e)*(inverseKernelUnit (fun _ _ : I=>0) d e)⁻¹).val *
      polynomial (relativeTaylor d e y) := by
  rw [←normalize_cleared_tensor d e x y h,Units.val_mul]
  simp only [mul_assoc,Units.inv_mul_cancel_left]

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma separation_shuffle_grid (a : I → I → ℕ) {d e α β : I → ℕ} (h : d+e=α+β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) :
    tensorSeparationSeries a α β (castS h (shufflePolynomial a f g))=
    ((inverseKernelUnit a α β)*(inverseKernelUnit (fun _ _ : I=>0) α β)⁻¹).val *
      polynomial (relativeTaylor α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) :=
  separation_of_cleared a α β _ _ (cleared_restrictTensor a h f g R (firstCut α β))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentConstantMultiplication
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries Finset
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma coeff_mul_zero_sub_mem (J : Submodule ℚ R) (f g : LaurentSeries R)
    (h : ∀ i j : ℤ, i+j=0 → (i,j)≠(0,0) → f.coeff i*g.coeff j∈J) :
    (f*g).coeff 0-f.coeff 0*g.coeff 0∈J := by
  classical
  apply (Submodule.Quotient.eq J).mp
  change J.mkQ ((f*g).coeff 0)=J.mkQ (f.coeff 0*g.coeff 0)
  rw [coeff_mul,map_sum]
  apply Finset.sum_eq_single (0,0)
  · intro ij hij hne
    apply (Submodule.Quotient.mk_eq_zero J).mpr
    exact h ij.1 ij.2 (mem_antidiagonal.mp hij).2.2 hne
  · intro hn
    have hz : f.coeff 0=0 ∨ g.coeff 0=0 := by
      by_contra hc
      push Not at hc
      exact hn (mem_antidiagonal.mpr ⟨hc.1,hc.2,by simp⟩)
    rcases hz with hf|hg
    · simp only [hf,zero_mul,map_zero]
    · simp only [hg,mul_zero,map_zero]

lemma coeff_mul_zero_sub_mem_of_positive (J : Submodule ℚ R) (f g : LaurentSeries R)
    (h : ∀ i j : ℤ, (0 < i ∨ 0 < j) → f.coeff i*g.coeff j∈J) :
    (f*g).coeff 0-f.coeff 0*g.coeff 0∈J := by
  apply coeff_mul_zero_sub_mem J f g
  intro i j hij hne
  apply h i j
  have hn : i≠0 ∨ j≠0 := by simpa only [ne_eq,Prod.mk.injEq,not_and_or] using hne
  omega

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_UnitalProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma OnSlopeOrZero.mass_eq {c η : I → ℝ} (hc : ∀ i,0 < c i)
    {θ : ℝ} {d : I → ℕ} (h : OnSlopeOrZero c η θ d) :
    mass η d=θ*mass c d := by
  rcases h with rfl|h
  · simp only [mass_zero,mul_zero]
  · rw [ElementaryPositivity.SlopeArithmetic.mass_eq c η hc d,h]

lemma high_mass_destabilizes_onSlope (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hs : OnSlopeOrZero c η θ (d+e))
    (h : mass η d > θ*mass c d) :
    d≠0 ∧ e≠0 ∧ slope c η d>slope c η (d+e) := by
  have hne : d+e≠0 := by
    intro hz
    have hd : d=0 := by
      funext i
      have hi:=congrFun hz i
      simp only [Pi.add_apply,Pi.zero_apply] at hi
      change d i=0
      omega
    simp only [hd,mass_zero,mul_zero,lt_self_iff_false] at h
  have hθ := hs.resolve_left hne
  exact high_mass_destabilizes c η hc d e (by simpa only [hθ] using h)

theorem offSlope_destabilizes_onSlope (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht₁ : OnSlopeOrZero c η θ (d₁+e₁)) (ht₂ : OnSlopeOrZero c η θ (d₂+e₂))
    (hs : OnSlopeOrZero c η θ (d₁+d₂))
    (hoff : ¬CellsOnSlope c η θ d₁ e₁ d₂ e₂) :
    (d₁≠0 ∧ e₁≠0 ∧ slope c η d₁>slope c η (d₁+e₁)) ∨
    (d₂≠0 ∧ e₂≠0 ∧ slope c η d₂>slope c η (d₂+e₂)) := by
  by_cases h₁ : mass η d₁>θ*mass c d₁
  · exact Or.inl (high_mass_destabilizes_onSlope c η hc θ d₁ e₁ ht₁ h₁)
  by_cases h₂ : mass η d₂>θ*mass c d₂
  · exact Or.inr (high_mass_destabilizes_onSlope c η hc θ d₂ e₂ ht₂ h₂)
  have hsrc:=hs.mass_eq hc
  have htar₁:=ht₁.mass_eq hc
  have htar₂:=ht₂.mass_eq hc
  simp only [mass_add] at hsrc htar₁ htar₂
  have hd₁ : mass η d₁=θ*mass c d₁ := by nlinarith
  have hd₂ : mass η d₂=θ*mass c d₂ := by nlinarith
  have he₁ : mass η e₁=θ*mass c e₁ := by nlinarith
  have he₂ : mass η e₂=θ*mass c e₂ := by nlinarith
  exact (hoff ⟨onSlopeOrZero_of_mass c η hc θ d₁ hd₁,
    onSlopeOrZero_of_mass c η hc θ e₁ he₁,onSlopeOrZero_of_mass c η hc θ d₂ hd₂,
    onSlopeOrZero_of_mass c η hc θ e₂ he₂⟩).elim
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

lemma quotient_cellTransfer_offSlope_unital (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht₁ : OnSlopeOrZero c η θ (d₁+e₁)) (ht₂ : OnSlopeOrZero c η θ (d₂+e₂))
    (hs : OnSlopeOrZero c η θ (d₁+d₂))
    (hoff : ¬CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p)=0 :=
  quotient_cellTransfer_zero a (slope c η) _ _ _ _
    (offSlope_destabilizes_onSlope c η hc θ _ _ _ _ ht₁ ht₂ hs hoff) p

omit [(index : I) → Fintype (A index)] in
lemma quotient_gridShapeTensor_offSlope_unital (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d)
    (hoff : ¬CellsOnSlope c η θ
      (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v)=0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply quotient_cellTransfer_offSlope_unital a c η hc θ
    · rwa [(shape_add_complement u).trans (realization_card R)]
    · rwa [(shape_add_complement v).trans (realization_card T)]
    · rwa [hsum]
    · exact hoff
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [(index : I) → Fintype (A index)] in
theorem quotient_gridTensor_unital_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d) :
    quotientTensor a (slope c η) α β (gridTensor a f g p R T)=
      ∑ u : CutShape (left p),∑ v : CutShape (right p),
        if CellsOnSlope c η θ
          (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)
        then quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) else 0 := by
  classical
  simp only [gridTensor,map_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with hon
  · rfl
  · exact quotient_gridShapeTensor_offSlope_unital a c η hc θ f g p R T u v hα hβ hd hon
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellTransferSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma eulerForm_transpose (a : I → I → ℕ) (d e : I → ℕ) :
    eulerForm (fun i j=>a j i) d e=eulerForm a e d := by
  unfold eulerForm
  congr 1
  · exact Finset.sum_congr rfl (fun i hi=>mul_comm _ _)
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

namespace SeparationInfinity

lemma pointed_mixedInverseKernel (a b : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
      (mixedInverseKernelUnit a b (SlopeArithmetic.slope c η) L.dim R.dim).val =
    mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (mapRing (crossPointEval L R v w) (rawInverseKernelUnit b L.dim R.dim).val) := by
  apply HahnSeries.ext
  funext k
  change pointedTensorRestriction a c η hc θ L R hL hR v w
    (Algebra.TensorProduct.map (quotientAlg a (SlopeArithmetic.slope c η) L.dim)
      (quotientAlg a (SlopeArithmetic.slope c η) R.dim) ((inverseKernelUnit b L.dim R.dim).val.coeff k))=_
  rw [pointedTensorRestriction_quotient]
  have h:=congrArg (fun f : LaurentSeries (MvPolynomial (CellVars L.dim R.dim) ℚ)=>f.coeff k)
    (realize_inverseKernelUnit b L.dim R.dim)
  exact congrArg (fun f=>algebraMap ℚ _ (crossPointEval L R v w f)) h

lemma refined_mixedKernel_degreeZero (a b : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (mixedInverseKernelUnit a b (SlopeArithmetic.slope c η) L.dim R.dim).val)=
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel b L R v w).val := by
  trans mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
    (mixedInverseKernelUnit a b (SlopeArithmetic.slope c η) L.dim R.dim).val
  · apply HahnSeries.ext
    funext k
    exact degreeZero_refinedAtB a c η hc θ L R hL hR v w _
  · rw [pointed_mixedInverseKernel]
    congr 1
    exact congrArg Units.val (crossPointEval_inverseKernel_scalar b L R v w)

end SeparationInfinity

namespace SplitTree
omit [DecidableEq I] in
lemma scalarCrossKernel_transpose (a : I → I → ℕ) (c η : I → ℝ)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    scalarCrossKernel (fun i j=>a j i) L R v w=scalarCrossKernel a L R v w := by
  unfold scalarCrossKernel
  apply Finset.prod_congr rfl
  intro z hz
  apply Finset.prod_congr rfl
  intro t ht
  rw [eulerForm_transpose]
  congr 1
  obtain ⟨hz,hzs⟩:=L.leafDimension_onSlope c η θ hL z
  obtain ⟨ht,hts⟩:=R.leafDimension_onSlope c η θ hR t
  exact (hχ _ _ hz ht hzs hts).symm
end SplitTree
namespace SeparationInfinity
lemma refined_braidingRatio_degreeZero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val)=1 := by
  let H := (mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom).comp
    (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom)
  let Φ := Units.map H.toMonoidHom
  have he : Φ (mixedInverseKernelUnit a a (SlopeArithmetic.slope c η) L.dim R.dim)=
      Φ (mixedInverseKernelUnit a (fun i j=>a j i) (SlopeArithmetic.slope c η) L.dim R.dim) := by
    apply Units.ext
    change H _=H _
    dsimp only [H,RingHom.comp_apply]
    rw [refined_mixedKernel_degreeZero,refined_mixedKernel_degreeZero,
      scalarCrossKernel_transpose a c η θ hχ L R hL hR]
  have hh : Φ (braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim)=1 := by
    rw [braidingRatioUnit,map_mul,map_inv,he,mul_inv_cancel]
  exact congrArg Units.val hh
end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossCancellation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma crossKernel_leading_polynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    ∃ p : Polynomial (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)),
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel a L R v w).val *
      polynomial (lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
        (totalLeadingPolynomial a c η hc θ (.node L R) ⟨hL,hR⟩ W f)) = polynomial p := by
  obtain ⟨q,hq⟩:=totalLeadingPolynomial_denominator_divisible a c η hc θ (.node L R) ⟨hL,hR⟩
    W f hf (crossPairs L R) (crossPairs_ne L R) (crossPairs_norev L R)
      (crossPairs_symmetric a c η θ hχ L R hL hR)
  refine ⟨(crossPolynomial a L R v w Int.toNat).map
    (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))) *
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0)) q, ?_⟩
  rw [hq,map_mul,lineSpecialization_map_algebra,centerDenominator_crossPairs_line,
    map_mul,←polynomial_map,←mul_assoc,←map_mul,scalarCrossKernel_denominator,
    polynomial_map,map_mul]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RefinedTensorDetection
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refinedAtB_weight_zero_test (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim ⊗[ℚ] B a (SlopeArithmetic.slope c η) R.dim)
    (hx : ∀ v w,weightComponent a (SlopeArithmetic.slope c η) (.node L R) W
      (refinedAtB a c η hc θ L R hL hR v w x)=0)
    (k : L.Degrees) (l : R.Degrees) (z : L.Centers →₀ ℕ) (w : R.Centers →₀ ℕ)
    (hw : 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W) :
    TensorProduct.map (restrictionTest a c η hc θ L hL rfl k z)
      (restrictionTest a c η hc θ R hR rfl l w) x=0 := by
  have hp : mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (refinedCenterPolynomial a c η hc θ L R hL hR x)=0 := by
    apply eq_of_evalRat
    intro v
    rw [evalRat_mapLinear,map_zero,refinedCenterPolynomial_eval]
    exact hx _ _
  have h:=congrArg (fun p=>componentTensor a (SlopeArithmetic.slope c η) (.node L R) (k,l)
    (MvPolynomial.coeff (z.sumElim w) p)) hp
  rw [coeff_mapLinear,componentTensor_weightComponent,ite_eq_left hw,MvPolynomial.coeff_zero,
    map_zero,refinedCenterPolynomial_coeff_test] at h
  exact h
end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
open SplitTree SeparationInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma refined_negative_separation_weight_zero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W j : ℤ) (hj : j<0)
    (f : B a (SlopeArithmetic.slope c η) (L.dim+R.dim))
    (hf : f∈sourceFiltration a c η hc θ (L.dim+R.dim) W) :
    weightComponent a (SlopeArithmetic.slope c η) (.node L R) W
      (refinedAtB a c η hc θ L R hL hR v w
        (separationCoefficient a c η hc
          ((slope_dim c η hc hL).trans (slope_dim c η hc hR).symm) j f))=0 := by
  obtain ⟨p,hp⟩:=crossKernel_leading_polynomial a c η hc θ hχ L R hL hR v w W f hf
  have h:=refined_leading_separation_formula a c η hc θ L R hL hR v w W f hf
  rw [hp] at h
  have hh:=congrArg (fun x : LaurentSeries (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))=>x.coeff (-j)) h
  rw [mapLinear_coeff,mapRing_coeff,polynomial_coeff_positive p (-j) (by omega)] at hh
  exact hh

theorem separationCoefficient_negative_filtration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W j : ℤ) (hj : j<0) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    separationCoefficient a c η hc hs j f∈sourceTensorFiltration a c η hc θ d e (W+1) := by
  apply tensor_leading_restrictions_detect a c η hc θ d e W _
    (separationCoefficient_filtration a c η hc θ d e hs W j f hf)
  rintro ⟨L,hoL,hL,hd,k,z⟩ ⟨R,hoR,hR,he,l,w⟩ hw
  subst d
  subst e
  apply refinedAtB_weight_zero_test a c η hc θ L R hL hR W _
    (fun v w=>refined_negative_separation_weight_zero a c η hc θ hχ L R hL hR v w W j hj f hf)
  change (2*L.totalDegree k+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W at hw
  change 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W
  omega

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_BraidingFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open SplitTree SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.CenterCalculus
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidTensorCommRing
noncomputable local instance braidTensorAlgebra_rfa2d34_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidTensorNUSemiring
lemma refinedAtB_mem_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (x : B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim)
    (hx : x∈sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    refinedAtB a c η hc θ L R hL hR v w x∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.node L R) W := by
  have he := refinedCenterPolynomial_eval a c η hc θ L R hL hR (Sum.elim v w) x
  change evalRat (Sum.elim v w) (refinedCenterPolynomial a c η hc θ L R hL hR x)=
    refinedAtB a c η hc θ L R hL hR v w x at he
  rw [←he]
  exact evalRat_mem_of_coeff _ _
    (refinedCenterPolynomial_coeff_degreeCut a c η hc θ L R hL hR W x hx) _

lemma braidingRatio_refined_leading (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (W : ℤ)
    (F : LaurentSeries (B a (SlopeArithmetic.slope c η) L.dim⊗[ℚ]B a (SlopeArithmetic.slope c η) R.dim))
    (hF : ∀ k,F.coeff k∈sourceTensorFiltration a c η hc θ L.dim R.dim W) :
    LaurentAtInfinity.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        ((braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val*F))=
    LaurentAtInfinity.mapLinear (weightComponent a (SlopeArithmetic.slope c η) (.node L R) W)
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom F) := by
  rw [map_mul]
  have h := weightComponent_laurent_mul a (SlopeArithmetic.slope c η) (.node L R) W
    (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
      (braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val)
    (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom F) 1
    (fun k=>refinedAtB_mem_degreeCut a c η hc θ L R hL hR v w W _ (hF k))
    (by rw [map_one]; exact refined_braidingRatio_degreeZero a c η hc θ hχ L R hL hR v w)
  simpa only [map_one,one_mul] using h

theorem braidingRatio_coeff_next (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ)
    (F : LaurentSeries (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e))
    (hF : ∀ k,F.coeff k∈sourceTensorFiltration a c η hc θ d e W) (k : ℤ) :
    ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val*F-F).coeff k∈
      sourceTensorFiltration a c η hc θ d e (W+1) := by
  apply tensor_leading_restrictions_detect a c η hc θ d e W
  · rw [HahnSeries.coeff_sub]
    apply Submodule.sub_mem _ _ (hF k)
    rw [mul_comm]
    exact coeff_mul_mem (sourceTensorFiltrationIdeal a c η hc θ d e W) F _ hF k
  · rintro ⟨L,hoL,hL,hd,j,z⟩ ⟨R,hoR,hR,he,l,w⟩ hjl
    subst d
    subst e
    apply refinedAtB_weight_zero_test a c η hc θ L R hL hR W
    · intro v w
      have hh := congrArg (fun S : LaurentSeries
        (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R))=>S.coeff k)
        (braidingRatio_refined_leading a c η hc θ hχ L R hL hR v w W F hF)
      change weightComponent a (SlopeArithmetic.slope c η) (.node L R) W
        (refinedAtB a c η hc θ L R hL hR v w _)=_ at hh
      rw [HahnSeries.coeff_sub,map_sub,map_sub,sub_eq_zero]
      exact hh
    · change (2*L.totalDegree j+L.doubleShift a)+(2*R.totalDegree l+R.doubleShift a)=W at hjl
      change 2*(L.totalDegree j+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=W
      omega

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SeparationInfinity

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorS
noncomputable local instance braidCoeffTensorSA_rfa2d34_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorB
noncomputable local instance braidCoeffTensorBA_rfa2d34_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorBN
noncomputable local instance braidCoeffTensorBM_rfa2d34_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule
lemma braidingRatioUnit_zero_left (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (e : I → ℕ) :
    braidingRatioUnit a μ 0 e=1 := by
  simp only [braidingRatioUnit,mixedInverseKernelUnit,inverseKernelUnit_zero_left,map_one,
    inv_one,mul_one]

lemma braidingRatioUnit_zero_right (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    braidingRatioUnit a μ d 0=1 := by
  simp only [braidingRatioUnit,mixedInverseKernelUnit,inverseKernelUnit_zero_right,map_one,
    inv_one,mul_one]
end SeparationInfinity

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorS
noncomputable local instance braidCoeffTensorSA_rfa2d34_2 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorB
noncomputable local instance braidCoeffTensorBA_rfa2d34_2 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorBN
noncomputable local instance braidCoeffTensorBM_rfa2d34_2 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule
lemma braidingDifference_coeff_mul_next (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ) (x : B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)
    (hx : x∈sourceTensorFiltration a c η hc θ d e W) (k : ℤ) :
    ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val-1).coeff k*x∈
      sourceTensorFiltration a c η hc θ d e (W+1) := by
  have H:=braidingRatio_coeff_next a c η hc θ hχ d e W (single (0 : ℤ) x) (fun j=>?_) k
  · have he : ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val-1)*single (0 : ℤ) x=
        (braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val*single (0 : ℤ) x-single (0 : ℤ) x := by
      rw [sub_mul,one_mul]
    rw [←he,coeff_mul_single_zero] at H
    exact H
  · by_cases hj : j=0
    · subst j; simpa only [coeff_single_same] using hx
    · rw [coeff_single_of_ne hj]
      exact Submodule.zero_mem _

lemma braidingDifference_coeff_mul_unital_next (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : I → ℕ) (W : ℤ) (x : B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d e W) (k : ℤ) :
    ((braidingRatioUnit a (SlopeArithmetic.slope c η) d e).val-1).coeff k*x∈
      unitalSourceTensorFiltration a c η hc θ d e (W+1) := by
  by_cases hd : d=0
  · subst d
    rw [braidingRatioUnit_zero_left,Units.val_one,sub_self,coeff_zero,zero_mul]
    exact Submodule.zero_mem _
  by_cases he : e=0
  · subst e
    rw [braidingRatioUnit_zero_right,Units.val_one,sub_self,coeff_zero,zero_mul]
    exact Submodule.zero_mem _
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he] at hx ⊢
  exact braidingDifference_coeff_mul_next a c η hc θ hχ d e W x hx k

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TensorMiddleFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]

lemma middleInsert_tmul (a : A) (d : D) (c : C) (b : B) :
    middleInsert a d (c⊗ₜ[K]b)=(a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d) := rfl

lemma middleInsert_mem_filtration
    (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (u z W : ℤ) (a : A) (d : D) (ha : a∈P u) (hd : d∈S z)
    (x : C⊗[K]B) (hx : x∈additiveTensorFiltration R Q W) :
    middleInsert a d x∈
      additiveTensorFiltration (additiveTensorFiltration P R)
        (additiveTensorFiltration Q S) (u+W+z) := by
  let J:=additiveTensorFiltration (additiveTensorFiltration P R)
    (additiveTensorFiltration Q S) (u+W+z)
  change middleInsert a d x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,w,c,b,hw,hc,hb,rfl⟩:=hx
    rw [middleInsert_tmul]
    exact tmul_mem_additiveTensorFiltration _ _ (show u+W+z≤(u+v)+(w+z) by omega)
      (tmul_mem_additiveTensorFiltration P R (le_refl _) ha hc)
      (tmul_mem_additiveTensorFiltration Q S (le_refl _) hb hd)
  | zero => rw [map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact J.smul_mem r hx

end ElementaryPositivity.LinearDetection

end
section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K A B C D : Type*} [Field K]
  [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]

lemma middleEmbedding_mul (r : C⊗[K]B) (a : A) (c : C) (b : B) (d : D) :
    middleEmbedding r*((a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d))=
      middleInsert a d (r*(c⊗ₜ[K]b)) := by
  induction r using OAI.tensorInductionOn with
  | add r s hr hs => rw [map_add,add_mul,add_mul,map_add,hr,hs]
  | tmul x y =>
    change ((1⊗ₜ[K]x)⊗ₜ[K](y⊗ₜ[K]1))*((a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d))=_
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,middleInsert_tmul]

lemma middleAction_mem_filtration
    (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (δ : ℤ) (r : C⊗[K]B)
    (hr : ∀ v w c b,c∈R v → b∈Q w → r*(c⊗ₜ[K]b)∈additiveTensorFiltration R Q (v+w+δ))
    (W : ℤ) (x : (A⊗[K]C)⊗[K](B⊗[K]D))
    (hx : x∈additiveTensorFiltration (additiveTensorFiltration P R)
      (additiveTensorFiltration Q S) W) :
    middleEmbedding r*x∈additiveTensorFiltration (additiveTensorFiltration P R)
      (additiveTensorFiltration Q S) (W+δ) := by
  let J:=additiveTensorFiltration (additiveTensorFiltration P R)
    (additiveTensorFiltration Q S) (W+δ)
  let L : (A⊗[K]C)⊗[K](B⊗[K]D) →ₗ[K] (A⊗[K]C)⊗[K](B⊗[K]D) :=
    LinearMap.mulLeft K (middleEmbedding r)
  change L x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,z,f,g,hw,hf,hg,rfl⟩:=hx
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨p,v,a,c,hpv,ha,hc,rfl⟩:=hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨w,t,b,d,hwt,hb,hd,rfl⟩:=hg
        change middleEmbedding r*((a⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]d))∈J
        rw [middleEmbedding_mul]
        exact additiveTensorFiltration_antitone _ _ (show W+δ≤p+(v+w+δ)+t by omega)
          (middleInsert_mem_filtration P Q R S p t (v+w+δ) a d ha hd _ (hr v w c b hc hb))
      | zero => rw [TensorProduct.tmul_zero,L.map_zero]; exact J.zero_mem
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add,L.map_add]; exact J.add_mem hx hy
      | smul s x _ hx => rw [TensorProduct.tmul_smul,L.map_smul]; exact J.smul_mem s hx
    | zero => rw [TensorProduct.zero_tmul,L.map_zero]; exact J.zero_mem
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul,L.map_add]; exact J.add_mem hx hy
    | smul s x _ hx => rw [←TensorProduct.smul_tmul',L.map_smul]; exact J.smul_mem s hx
  | zero => rw [L.map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [L.map_add]; exact J.add_mem hx hy
  | smul s x _ hx => rw [L.map_smul]; exact J.smul_mem s hx

end ElementaryPositivity.LinearDetection

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourBraiding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorM
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourM
lemma fourBraidingCoefficient_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ) (W : ℤ)
    (x : (B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂))
    (hx : x∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ W) (j : ℤ) :
    crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂
      (((braidingRatioUnit a (slope c η) e₁ d₂).val-1).coeff j)*x∈
      fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (W+1) := by
  exact middleAction_mem_filtration (unitalSourceFiltration a c η hc θ d₁)
    (unitalSourceFiltration a c η hc θ d₂) (unitalSourceFiltration a c η hc θ e₁)
    (unitalSourceFiltration a c η hc θ e₂) 1 _
    (fun v w f g hf hg=>braidingDifference_coeff_mul_unital_next a c η hc θ hχ e₁ d₂
      (v+w) (f⊗ₜ[ℚ]g) (tmul_mem_additiveTensorFiltration _ _ (le_refl _) hf hg) j) W x hx

lemma map_sub_one_mul {R T : Type*} [Ring R] [Ring T] (f : R →+* T) (x : R) (y : T) :
    f (x-1)*y=f x*y-y := by rw [map_sub,map_one,sub_mul,one_mul]

lemma fourBraiding_coeff_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ) (W : ℤ)
    (F : LaurentSeries ((B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂)))
    (hF : ∀ j,F.coeff j∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ W) (k : ℤ) :
    (mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      (braidingRatioUnit a (slope c η) e₁ d₂).val*F-F).coeff k∈
      fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (W+1) := by
  classical
  have he : mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      ((braidingRatioUnit a (slope c η) e₁ d₂).val-1)*F=
      mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      (braidingRatioUnit a (slope c η) e₁ d₂).val*F-F := map_sub_one_mul _ _ _
  rw [←he,coeff_mul]
  apply Submodule.sum_mem
  intro ij hij
  exact fourBraidingCoefficient_next a c η hc θ hχ d₁ e₁ d₂ e₂ W _ (hF ij.2) ij.1

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace SeparationInfinity

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorA
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorM
lemma unitalSeparationSeries_coeff_positive_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W j : ℤ) (hj : 0<j) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) :
    (unitalSeparationSeries a c η hc hs f).coeff j∈unitalSourceTensorFiltration a c η hc θ d e (W+1) := by
  by_cases hd : d=0
  · subst d
    change ((quotientInverseKernelUnit a (slope c η) 0 e).val*
      polynomial (unitalRestrictionRelativeB a c η hc hs f)).coeff j∈unitalSourceTensorFiltration a c η hc θ 0 e (W+1)
    rw [quotientInverseKernelUnit_zero_left,Units.val_one,one_mul,polynomial_coeff_positive _ j hj]
    exact Submodule.zero_mem _
  by_cases he : e=0
  · subst e
    change ((quotientInverseKernelUnit a (slope c η) d 0).val*
      polynomial (unitalRestrictionRelativeB a c η hc hs f)).coeff j∈unitalSourceTensorFiltration a c η hc θ d 0 (W+1)
    rw [quotientInverseKernelUnit_zero_right,Units.val_one,one_mul,polynomial_coeff_positive _ j hj]
    exact Submodule.zero_mem _
  have hde : d+e≠0 := add_ne_zero_left _ _ hd
  have hs' := hs.resolve_left hd |>.resolve_left he
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) hde W] at hf
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he]
  have hn := separationCoefficient_negative_filtration a c η hc θ hχ d e hs' W (-j) (by omega) f hf
  have heq : unitalRestrictionRelativeB a c η hc hs=restrictionRelativeB a c η hc hs' (firstCut d e) := by
    unfold unitalRestrictionRelativeB restrictionRelativeB
    congr 1
  simp only [unitalSeparationSeries,LinearMap.comp_apply,heq]
  simpa only [separationCoefficient_eq_coeff,neg_neg,separationSeries,LinearMap.comp_apply] using hn
end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridQuotient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
variable {K A B C D : Type*} [CommRing K]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D]

lemma first_tmul (a : A) (b : B) :
    first (C:=C) (D:=D) (a⊗ₜ[K]b)=(a⊗ₜ[K]1)⊗ₜ[K](b⊗ₜ[K]1) := rfl
lemma second_tmul (c : C) (d : D) :
    second (A:=A) (B:=B) (c⊗ₜ[K]d)=(1⊗ₜ[K]c)⊗ₜ[K](1⊗ₜ[K]d) := rfl

lemma product (x : A⊗[K]B) (y : C⊗[K]D) :
    first x * second y=TensorProduct.tensorTensorTensorComm K A B C D (x⊗ₜ[K]y) := by
  induction x using OAI.tensorInductionOn with
  | add x z hx hz => rw [map_add,add_mul,TensorProduct.add_tmul,(TensorProduct.tensorTensorTensorComm K A B C D).map_add,hx,hz]
  | tmul a b =>
    induction y using OAI.tensorInductionOn with
    | add y z hy hz => rw [map_add,mul_add,TensorProduct.tmul_add,(TensorProduct.tensorTensorTensorComm K A B C D).map_add,hy,hz]
    | tmul c d =>
      rw [first_tmul,second_tmul,TensorProduct.tensorTensorTensorComm_tmul]
      simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

end ElementaryPositivity.TensorColumns

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorColumnSeriesFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {A B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C] [Algebra ℚ D]

lemma seriesProduct_coeff_filtration
    (P : ℤ → Submodule ℚ A) (Q : ℤ → Submodule ℚ B)
    (R : ℤ → Submodule ℚ C) (S : ℤ → Submodule ℚ D)
    (U V : ℤ) (f : LaurentSeries (A⊗[ℚ]B)) (g : LaurentSeries (C⊗[ℚ]D))
    (hf : ∀ j,f.coeff j∈additiveTensorFiltration P Q U)
    (hg : ∀ j,g.coeff j∈additiveTensorFiltration R S V) (k : ℤ) :
    (seriesProduct f g).coeff k∈
      additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V) := by
  classical
  rw [seriesProduct,coeff_mul]
  apply Submodule.sum_mem
  intro ij hij
  change first (f.coeff ij.1)*second (g.coeff ij.2)∈
    additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V)
  rw [product]
  exact interchange_mem_filtration P Q R S U V _ _ (hf _) (hg _)

lemma seriesProduct_constant_filtration
    (P : ℤ → Submodule ℚ A) (Q : ℤ → Submodule ℚ B)
    (R : ℤ → Submodule ℚ C) (S : ℤ → Submodule ℚ D)
    (U V : ℤ) (f : LaurentSeries (A⊗[ℚ]B)) (g : LaurentSeries (C⊗[ℚ]D))
    (hf : ∀ j,f.coeff j∈additiveTensorFiltration P Q U)
    (hg : ∀ j,g.coeff j∈additiveTensorFiltration R S V)
    (hf' : ∀ j,0<j → f.coeff j∈additiveTensorFiltration P Q (U+1))
    (hg' : ∀ j,0<j → g.coeff j∈additiveTensorFiltration R S (V+1)) :
    (seriesProduct f g).coeff 0-
      TensorProduct.tensorTensorTensorComm ℚ A B C D (f.coeff 0⊗ₜ[ℚ]g.coeff 0)∈
      additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V+1) := by
  rw [←product]
  unfold seriesProduct
  apply coeff_mul_zero_sub_mem_of_positive
  intro i j hij
  change first (f.coeff i)*second (g.coeff j)∈
    additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V+1)
  rw [product]
  rcases hij with hi|hj
  · convert interchange_mem_filtration P Q R S (U+1) V _ _ (hf' i hi) (hg j) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega
  · convert interchange_mem_filtration P Q R S U (V+1) _ _ (hf i) (hg' j hj) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega

end ElementaryPositivity.TensorColumns

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

lemma fourInputSeriesB_constant_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (U V : ℤ) (f : B a (slope c η) (d₁+d₂)) (g : B a (slope c η) (e₁+e₂))
    (hf : f∈unitalSourceFiltration a c η hc θ (d₁+d₂) U)
    (hg : g∈unitalSourceFiltration a c η hc θ (e₁+e₂) V) :
    (fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he f g).coeff 0-
      fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
        ((unitalSeparationSeries a c η hc hd f).coeff 0⊗ₜ[ℚ]
          (unitalSeparationSeries a c η hc he g).coeff 0)∈
      fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (U+V+1) := by
  let P:=unitalSourceFiltration a c η hc θ
  let F:=unitalSeparationSeries a c η hc hd f
  let G:=unitalSeparationSeries a c η hc he g
  let H:=ElementaryPositivity.TensorColumns.seriesProduct F G
  have hF (j) := unitalSeparationSeries_coeff_filtration a c η hc θ d₁ d₂ hd U j f hf
  have hG (j) := unitalSeparationSeries_coeff_filtration a c η hc θ e₁ e₂ he V j g hg
  have hH (j) : H.coeff j∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (U+V) :=
    ElementaryPositivity.TensorColumns.seriesProduct_coeff_filtration
      (P d₁) (P d₂) (P e₁) (P e₂) U V F G hF hG j
  have h₁ := fourBraiding_coeff_next a c η hc θ hχ d₁ e₁ d₂ e₂ (U+V) H hH 0
  have h₂ := ElementaryPositivity.TensorColumns.seriesProduct_constant_filtration
    (P d₁) (P d₂) (P e₁) (P e₂) U V F G hF hG
    (fun j hj=>unitalSeparationSeries_coeff_positive_next a c η hc θ hχ d₁ d₂ hd U j hj f hf)
    (fun j hj=>unitalSeparationSeries_coeff_positive_next a c η hc θ hχ e₁ e₂ he V j hj g hg)
  rw [coeff_sub] at h₁
  have h:=Submodule.add_mem (fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (U+V+1)) h₁ h₂
  simpa only [fourInputSeriesB,fourInterchangeB,F,G,H,sub_add_sub_cancel] using h

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalNatS
noncomputable local instance unitalNatSA_rfa2d34_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalNatB
noncomputable local instance unitalNatBA_rfa2d34_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
lemma unitalRestrictionRelativeB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S (d+e)) :
    unitalRestrictionRelativeB a c η hc hs (quotientAlg a (slope c η) (d+e) f)=
    Polynomial.map (quotientTensor a (slope c η) d e).toRingHom
      (relativeTaylor d e (restrictTensor (firstCut d e) f)) := by
  rw [relativeTaylor_quotient]
  rfl

lemma unitalSeparationSeries_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S (d+e)) :
    unitalSeparationSeries a c η hc hs (quotientAlg a (slope c η) (d+e) f)=
    mapRing (quotientTensor a (slope c η) d e).toRingHom (tensorSeparationSeries a d e f) := by
  rw [tensorSeparationSeries,mapRing_mul_polynomial]
  dsimp only [unitalSeparationSeries,LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  rw [unitalRestrictionRelativeB_mk]
  rfl

end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ClearedSeparationB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma mapRing_ratio_val {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (u v : (LaurentSeries R)ˣ) :
    mapRing f (u*v⁻¹).val=
      (Units.map (mapRing f).toMonoidHom u*(Units.map (mapRing f).toMonoidHom v)⁻¹).val := by
  rw [Units.val_mul,map_mul]
  rfl

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorS
noncomputable local instance clearBTensorSA_rfa2d34_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorB
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.clearBTensorBA
lemma clearedSeparationB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : S d⊗[ℚ]S e) :
    clearedSeparationB a μ d e (quotientTensor a μ d e x)=
    mapRing (quotientTensor a μ d e).toRingHom
      ((inverseKernelUnit a d e*(inverseKernelUnit (fun _ _ : I=>0) d e)⁻¹).val *
        polynomial (relativeTaylor d e x)) := by
  rw [mapRing_mul_polynomial,mapRing_ratio_val,relativeTaylor_quotient]
  rfl

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma unitalSeparationSeries_shuffle_grid (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e α β : I → ℕ} (h : d+e=α+β)
    (hs : α=0 ∨ β=0 ∨ slope c η α=slope c η β)
    (f : S d) (g : S e) {s : ElementaryPositivity.PackConvolution.Pack (A:=A)}
    (R : Realization (α+β) s) :
    unitalSeparationSeries a c η hc hs
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))=
    clearedSeparationB a (slope c η) α β
      (quotientTensor a (slope c η) α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) := by
  rw [unitalSeparationSeries_mk,separation_shuffle_grid a h f g R,clearedSeparationB_mk]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TwoTargetFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

lemma clearedSeparationB_cell_constant_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd₁ : OnSlopeOrZero c η θ d₁) (he₁ : OnSlopeOrZero c η θ e₁)
    (hd₂ : OnSlopeOrZero c η θ d₂) (he₂ : OnSlopeOrZero c η θ e₂)
    (U V : ℤ) (f : S (d₁+d₂)) (g : S (e₁+e₂))
    (hf : quotientAlg a (slope c η) (d₁+d₂) f∈unitalSourceFiltration a c η hc θ (d₁+d₂) U)
    (hg : quotientAlg a (slope c η) (e₁+e₂) g∈unitalSourceFiltration a c η hc θ (e₁+e₂) V) :
    (clearedSeparationB a (slope c η) (d₁+e₁) (d₂+e₂)
      (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))).coeff 0-
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ (hd₁.compatible he₁) (hd₂.compatible he₂)
        (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
          ((unitalSeparationSeries a c η hc (hd₁.compatible hd₂)
              (quotientAlg a (slope c η) (d₁+d₂) f)).coeff 0⊗ₜ[ℚ]
           (unitalSeparationSeries a c η hc (he₁.compatible he₂)
              (quotientAlg a (slope c η) (e₁+e₂) g)).coeff 0))∈
      unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V+1) := by
  rw [clearedSeparationB_cell a c η hc d₁ e₁ d₂ e₂
    (hd₁.compatible hd₂) (he₁.compatible he₂) (hd₁.compatible he₁) (hd₂.compatible he₂)]
  simp only [coeff_smul,mapLinear_coeff]
  rw [←smul_sub,←LinearMap.map_sub]
  apply Submodule.smul_mem
  exact twoTargetTransferB_filtered a c η hc θ hχ d₁ e₁ d₂ e₂ hd₁ he₁ hd₂ he₂ (U+V+1) _
    (fourInputSeriesB_constant_next a c η hc θ hχ d₁ e₁ d₂ e₂
      (hd₁.compatible hd₂) (he₁.compatible he₂) U V _ _ hf hg)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open ElementaryPositivity.PackConvolution HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA Classical.propDecidable

lemma clearedConstantB_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d⊗[ℚ]B a μ e) :
    clearedConstantB a μ d e x=(clearedSeparationB a μ d e x).coeff 0 := rfl

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma unitalSeparationConstant_shuffle_grid (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e α β : I → ℕ} (h : d+e=α+β)
    (hs : α=0 ∨ β=0 ∨ slope c η α=slope c η β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc hs
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0=
    clearedConstantB a (slope c η) α β
      (quotientTensor a (slope c η) α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) := by
  exact congrArg (fun F=>F.coeff 0) (unitalSeparationSeries_shuffle_grid a c η hc h hs f g R)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellLeadingSum
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMonoid _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedMul _root_.OAI.ElementaryPositivity.RawShuffle.componentGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open ElementaryPositivity.PackConvolution HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA Classical.propDecidable

noncomputable local instance cellLeadTensorN_rfa2d34_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) :=
  (clearBTensorB a μ d e).toNonUnitalNonAssocSemiring
lemma clearedConstantB_cell_leading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) {d e : I → ℕ} (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (h : d+e=(d₁+e₁)+(d₂+e₂))
    (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V) :
    clearedConstantB a (slope c η) (d₁+e₁) (d₂+e₂)
      (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))) -
      cellLeadingB a c η hc θ d₁ e₁ d₂ e₂ hon f g∈
    unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V+1) := by
  by_cases hd : d₁+d₂=d
  · have he : e₁+e₂=e := by
      apply add_left_cancel (a:=d)
      calc
        d+(e₁+e₂)=(d₁+e₁)+(d₂+e₂) := by rw [←hd]; ac_rfl
        _=d+e := h.symm
    subst d
    subst e
    simpa only [cellLeadingB,dite_eq_left,castS_rfl,clearedConstantB_apply,and_self,
      dite_true] using
      clearedSeparationB_cell_constant_next a c η hc θ hχ d₁ e₁ d₂ e₂
        hon.1 hon.2.1 hon.2.2.1 hon.2.2.2 U V f g hf hg
  · rw [cellLeadingB,dite_eq_right (fun hm=>hd hm.1),
      fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hd]
    simp only [map_zero,sub_zero]
    exact Submodule.zero_mem _

lemma castBTensor_sub (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e')
    (x y : B a μ d⊗[ℚ]B a μ e) :
    castBTensor a μ h k (x-y)=castBTensor a μ h k x-castBTensor a μ h k y := by
  subst d'
  subst e'
  rfl

lemma clearedConstantB_castTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (x : S d⊗[ℚ]S e) :
    clearedConstantB a μ d' e' (quotientTensor a μ d' e' (castTensor h k x))=
      castBTensor a μ h k (clearedConstantB a μ d e (quotientTensor a μ d e x)) := by
  subst d'
  subst e'
  rfl

lemma castBTensor_mem_unitalSource (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (W : ℤ)
    (x : B a (slope c η) d⊗[ℚ]B a (slope c η) e)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d e W) :
    castBTensor a (slope c η) h k x∈unitalSourceTensorFiltration a c η hc θ d' e' W := by
  subst d'
  subst e'
  exact hx

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [∀ i, Fintype (A i)] in
lemma clearedConstantB_gridShape_leading (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) {d e α β : I → ℕ} (h : d+e=α+β)
    (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hon : CellsOnSlope c η θ (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v))-
      gridShapeLeadingB a c η hc θ f g p R T u v hon∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  unfold gridShapeTensor gridShapeLeadingB
  rw [clearedConstantB_castTensor,←castBTensor_sub]
  apply castBTensor_mem_unitalSource
  apply clearedConstantB_cell_leading a c η hc θ hχ _ _ _ _ hon _ U V f g hf hg
  rw [(shape_add_complement u).trans (realization_card R),
    (shape_add_complement v).trans (realization_card T)]
  exact h

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
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open ElementaryPositivity.LinearFiltration
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

omit [∀ i,Fintype (A i)] in
lemma clearedConstantB_grid_unital_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridTensor a f g p R T))=
    ∑ u : CutShape (left p),∑ v : CutShape (right p),
      if CellsOnSlope c η θ
        (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)
      then clearedConstantB a (slope c η) α β
        (quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v)) else 0 := by
  rw [quotient_gridTensor_unital_support a c η hc θ f g p R T hα hβ hd]
  simp only [map_sum,apply_ite,(clearedConstantB a (slope c η) α β).map_zero]

omit [∀ i,Fintype (A i)] in
lemma clearedConstantB_grid_leading_unital (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d) :
    clearedConstantB a (slope c η) α β (quotientTensor a (slope c η) α β (gridTensor a f g p R T))-
      gridLeadingB a c η hc θ f g p R T∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  rw [clearedConstantB_grid_unital_support a c η hc θ f g p R T hα hβ hd,gridLeadingB,
    ←Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro u _
  rw [←Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro v _
  split_ifs with hon
  · exact clearedConstantB_gridShape_leading a c η hc θ hχ h U V f g hf hg p R T u v hon
  · rw [sub_self]
    exact Submodule.zero_mem _

lemma unitalSeparationConstant_shuffle_leading_all_oai (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc (hα.compatible hβ)
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0-
      gridLeadingB a c η hc θ f g (cutRealizationEquiv R (firstCut α β)).val
        (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β))∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  rw [unitalSeparationConstant_shuffle_grid a c η hc h (hα.compatible hβ) f g R]
  exact clearedConstantB_grid_leading_unital a c η hc θ hχ h U V f g hf hg _ _ _ hα hβ hd

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all_oai.{u_1, u_2} := @OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all_oai.{u_1, u_2}
