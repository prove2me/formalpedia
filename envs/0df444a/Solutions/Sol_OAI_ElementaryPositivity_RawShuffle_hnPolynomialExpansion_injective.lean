-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:20.400212+00:00
-- url     : https://prove2.me/submissions/65ff4d23-bded-4a61-9552-980cd33e1f86

import Mathlib
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom028
import Definitions.Def_OAIQ368Chrom033
import Definitions.Def_OAIQ368Chrom038
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_clipped_grid_constant_head

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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma mass_nonneg (c : I → ℝ) (hc : ∀ i,0 ≤ c i) (d : I → ℕ) : 0 ≤ mass c d := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _) (hc i)

end ElementaryPositivity.SlopeArithmetic

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
noncomputable local instance clearingTensorAlg_r7697b1_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNRestrictionOrder
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.componentB_idempotent _root_.OAI.ElementaryPositivity.RawShuffle.componentB_mk _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_left _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_right _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.dimensionCast_trans _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleB_mk _root_.OAI.ElementaryPositivity.RawShuffle.shufflePolynomial_zero_left _root_.OAI.ElementaryPositivity.RawShuffle.shufflePolynomial_zero_right _root_.OAI.ElementaryPositivity.RawShuffle.taylorB_coeff_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)
lemma clippedSlope_of_le {θ : ℝ} {d : I → ℕ} (h : slope c η d ≤ θ) :
    clippedSlope c η θ d=θ := max_eq_right h
lemma clippedSlope_of_ge {θ : ℝ} {d : I → ℕ} (h : θ ≤ slope c η d) :
    clippedSlope c η θ d=slope c η d := max_eq_left h
lemma clippedSlope_le (θ : ℝ) (d : I → ℕ) : slope c η d ≤ clippedSlope c η θ d := le_max_left _ _

lemma clipped_high_mass (hc : ∀ i,0 < c i) (θ : ℝ) (d e : I → ℕ)
    (h : clippedSlope c η θ (d+e)*mass c d < mass η d) :
    d≠0 ∧ e≠0 ∧ clippedSlope c η θ (d+e) < clippedSlope c η θ d := by
  have hm : slope c η (d+e)*mass c d < mass η d :=
    (mul_le_mul_of_nonneg_right (clippedSlope_le c η θ (d+e))
      (mass_nonneg c (fun i=>(hc i).le) d)).trans_lt h
  obtain ⟨hd,he,_⟩:=high_mass_destabilizes c η hc d e hm
  refine ⟨hd,he,lt_of_lt_of_le ?_ (clippedSlope_le c η θ d)⟩
  exact (lt_div_iff₀ (mass_pos c hc d hd)).mpr h

lemma clipped_split_destabilizes (hc : ∀ i,0 < c i) (κ θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : clippedSlope c η κ (d₁+e₁) ≤ θ) (h₂ : clippedSlope c η κ (d₂+e₂) ≤ θ)
    (hd : d₁+d₂≠0) (hs : θ < slope c η (d₁+d₂)) :
    (d₁≠0 ∧ e₁≠0 ∧ clippedSlope c η κ (d₁+e₁) < clippedSlope c η κ d₁) ∨
    (d₂≠0 ∧ e₂≠0 ∧ clippedSlope c η κ (d₂+e₂) < clippedSlope c η κ d₂) := by
  by_cases hp : clippedSlope c η κ (d₁+e₁)*mass c d₁ < mass η d₁
  · exact Or.inl (clipped_high_mass c η hc κ d₁ e₁ hp)
  by_cases hq : clippedSlope c η κ (d₂+e₂)*mass c d₂ < mass η d₂
  · exact Or.inr (clipped_high_mass c η hc κ d₂ e₂ hq)
  have hpd := (mul_le_mul_of_nonneg_right h₁ (mass_nonneg c (fun i=>(hc i).le) d₁))
  have hqd := (mul_le_mul_of_nonneg_right h₂ (mass_nonneg c (fun i=>(hc i).le) d₂))
  have hh := (lt_div_iff₀ (mass_pos c hc (d₁+d₂) hd)).mp hs
  rw [mass_add,mass_add] at hh
  push Not at hp hq
  nlinarith
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
omit [∀ i, Fintype (A i)] in
lemma clipped_gridShape_zero (hc : ∀ i,0 < c i) (κ θ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (hμ : θ < slope c η d) :
    quotientTensor a (clippedSlope c η κ) α β (gridShapeTensor a f g p R T u v)=0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hs : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply quotient_cellTransfer_zero
    apply clipped_split_destabilizes c η hc κ θ
    · rwa [(shape_add_complement u).trans (realization_card R)]
    · rwa [(shape_add_complement v).trans (realization_card T)]
    · rwa [hs]
    · rwa [hs]
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hs,map_zero,map_zero]
omit [∀ i, Fintype (A i)] in
lemma clipped_grid_zero (hc : ∀ i,0 < c i) (κ θ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) (hd : d≠0)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (hμ : θ < slope c η d) :
    quotientTensor a (clippedSlope c η κ) α β (gridTensor a f g p R T)=0 := by
  simp only [gridTensor,map_sum]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  exact clipped_gridShape_zero a c η hc κ θ f g p R T u v hd hα hβ hμ
omit [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in

theorem clipped_restrict_high (hc : ∀ i,0 < c i) (κ θ : ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (u : Cut α β) (hd : d≠0)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (hμ : θ < slope c η d) :
    quotientTensor a (clippedSlope c η κ) α β
      (restrictTensor u (dimensionCast h (shufflePolynomial a f g)))=0 := by
  rw [dimensionCast_eq_castS]
  apply quotient_crossTensor_cancel
  let s : Pack (A:=fun i=>Fin ((α+β) i)) := fun _=>Finset.univ
  let R : Realization (α+β) s := defaultRealization (by intro i; simp [s])
  rw [cleared_restrictTensor a h f g R u,map_smul,
    clipped_grid_zero a c η hc κ θ f g _ _ _ hd hα hβ hμ,smul_zero]

lemma clipped_restrict_ideal (hc : ∀ i,0 < c i) (κ θ : ℝ)
    (α β : I → ℕ) (hμ : slope c η (α+β) ≤ θ)
    (hα : clippedSlope c η κ α ≤ θ) (hβ : clippedSlope c η κ β ≤ θ)
    (u : Cut α β) (f : S (α+β))
    (hf : f∈destabilizingSpace a (clippedSlope c η θ) (α+β)) :
    quotientTensor a (clippedSlope c η κ) α β (restrictTensor u f)=0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d,e,h,x,y,hd,he,hs,rfl⟩:=hf
    have hs' : θ < slope c η d := by
      rw [clippedSlope_of_le c η hμ,clippedSlope] at hs
      exact (lt_max_iff.mp hs).resolve_right (lt_irrefl θ)
    exact clipped_restrict_high a c η hc κ θ h x y u hd hα hβ hs'
  | zero => rw [map_zero,map_zero]
  | add f g _ _ hf hg => rw [map_add,map_add,hf,hg,add_zero]
  | smul q f _ hf => rw [map_smul,map_smul,hf,smul_zero]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CutoffRow
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ) (hc : ∀ i,0 < c i)
include hc

lemma clipped_equal_head (κ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hk : κ < slope c η (d₁+e₁)) (ht : slope c η (d₂+e₂) ≤ κ)
    (hd : d₁+d₂≠0) (hs : slope c η (d₁+e₁) ≤ slope c η (d₁+d₂))
    (hm : slope c η (d₁+d₂)=slope c η (d₁+e₁) → mass c (d₁+e₁) ≤ mass c (d₁+d₂))
    (hp : mass η d₁ ≤ clippedSlope c η κ (d₁+e₁)*mass c d₁)
    (hq : mass η d₂ ≤ clippedSlope c η κ (d₂+e₂)*mass c d₂) :
    e₁=0 ∧ d₂=0 := by
  rw [clippedSlope_of_ge c η hk.le] at hp
  rw [clippedSlope_of_le c η ht] at hq
  have hmass := mass_eq c η hc (d₁+d₂)
  have hsrc := mul_le_mul_of_nonneg_right hs (mass_nonneg c (fun i=>(hc i).le) (d₁+d₂))
  rw [←hmass,mass_add,mass_add] at hsrc
  have hz : d₂=0 := by
    by_contra hn
    have hpos:=mass_pos c hc d₂ hn
    have hh := mul_lt_mul_of_pos_right hk hpos
    nlinarith
  have hm' : mass c (d₁+e₁) ≤ mass c d₁ := by
    apply (by simpa only [hz,add_zero] using hm)
    apply le_antisymm _ (by simpa only [hz,add_zero] using hs)
    have hn : d₁≠0 := by simpa only [hz,add_zero] using hd
    exact (div_le_iff₀ (mass_pos c hc d₁ hn)).mpr hp
  rw [mass_add] at hm'
  refine ⟨?_,hz⟩
  by_contra hn
  have hp:=mass_pos c hc e₁ hn
  linarith

lemma clipped_head_destabilizes (κ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hk : κ < slope c η (d₁+e₁)) (ht : slope c η (d₂+e₂) ≤ κ)
    (hd : d₁+d₂≠0) (hs : slope c η (d₁+e₁) ≤ slope c η (d₁+d₂))
    (hm : slope c η (d₁+d₂)=slope c η (d₁+e₁) → mass c (d₁+e₁) ≤ mass c (d₁+d₂))
    (hne : ¬ (e₁=0 ∧ d₂=0)) :
    (d₁≠0 ∧ e₁≠0 ∧ clippedSlope c η κ (d₁+e₁) < clippedSlope c η κ d₁) ∨
    (d₂≠0 ∧ e₂≠0 ∧ clippedSlope c η κ (d₂+e₂) < clippedSlope c η κ d₂) := by
  by_cases hp : clippedSlope c η κ (d₁+e₁)*mass c d₁ < mass η d₁
  · exact Or.inl (clipped_high_mass c η hc κ d₁ e₁ hp)
  by_cases hq : clippedSlope c η κ (d₂+e₂)*mass c d₂ < mass η d₂
  · exact Or.inr (clipped_high_mass c η hc κ d₂ e₂ hq)
  exact (hne (clipped_equal_head c η hc κ d₁ e₁ d₂ e₂ hk ht hd hs hm
    (le_of_not_gt hp) (le_of_not_gt hq))).elim
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
include hc
lemma clipped_cell_nonhead_zero (κ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hk : κ < slope c η (d₁+e₁)) (ht : slope c η (d₂+e₂) ≤ κ)
    (hd : d₁+d₂≠0) (hs : slope c η (d₁+e₁) ≤ slope c η (d₁+d₂))
    (hm : slope c η (d₁+d₂)=slope c η (d₁+e₁) → mass c (d₁+e₁) ≤ mass c (d₁+d₂))
    (hne : ¬ (e₁=0 ∧ d₂=0))
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a (clippedSlope c η κ) (d₁+e₁) (d₂+e₂)
      (cellTransfer a d₁ e₁ d₂ e₂ p)=0 :=
  quotient_cellTransfer_zero a (clippedSlope c η κ) _ _ _ _
    (clipped_head_destabilizes c η hc κ d₁ e₁ d₂ e₂ hk ht hd hs hm hne) p
end ElementaryPositivity.RawShuffle

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
noncomputable local instance clearBTensorSA_r7697b1_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
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

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TwoTargetFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma clearedConstantB_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : B a μ d⊗[ℚ]B a μ e) :
    clearedConstantB a μ d e x=(clearedSeparationB a μ d e x).coeff 0 := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CutoffGrid
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_left _root_.OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
include hc
omit [∀ i, Fintype (A i)] in
lemma clipped_gridShape_nonhead_zero (κ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d)
    (hne : ¬(shapeComplement u=0 ∧ (fun i=>(v i).val)=0)) :
    quotientTensor a (clippedSlope c η κ) α β (gridShapeTensor a f g p R T u v)=0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply clipped_cell_nonhead_zero a c η hc κ
    · rwa [(shape_add_complement u).trans (realization_card R)]
    · rwa [(shape_add_complement v).trans (realization_card T)]
    · rwa [hsum]
    · rwa [(shape_add_complement u).trans (realization_card R),hsum]
    · rwa [(shape_add_complement u).trans (realization_card R),hsum]
    · exact hne
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [∀ i, Fintype (A i)] in
lemma clipped_gridShape_wrong_source (κ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    quotientTensor a (clippedSlope c η κ) α β (gridShapeTensor a f g p R T u v)=0 := by
  by_cases hsum : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply clipped_gridShape_nonhead_zero a c η hc κ f g p R T u v hd hk ht hs hm
    rintro ⟨hu,hv⟩
    have he := (shape_add_complement u).trans (realization_card R)
    rw [hu,add_zero] at he
    rw [hv,add_zero,he] at hsum
    exact hne hsum.symm
  · unfold gridShapeTensor
    rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero,map_zero]

omit [∀ i, Fintype (A i)] in
lemma clipped_grid_wrong_source (κ : ℝ)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    quotientTensor a (clippedSlope c η κ) α β (gridTensor a f g p R T)=0 := by
  simp only [gridTensor,map_sum]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  exact clipped_gridShape_wrong_source a c η hc κ f g p R T u v hd hk ht hs hm hne
omit [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in

theorem clipped_restrict_wrong_head (κ : ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (u : Cut α β) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    quotientTensor a (clippedSlope c η κ) α β
      (restrictTensor u (castS h (shufflePolynomial a f g)))=0 := by
  apply quotient_crossTensor_cancel
  let s : Pack (A:=fun i=>Fin ((α+β) i)) := fun _=>Finset.univ
  let R : Realization (α+β) s := defaultRealization (by intro i; simp [s])
  rw [cleared_restrictTensor a h f g R u,map_smul,
    clipped_grid_wrong_source a c η hc κ f g _ _ _ hd hk ht hs hm hne,smul_zero]
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA

lemma headRestriction_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : S (d+e)) :
    headRestriction a μ d e f=
      quotientTensor a μ d e ((tensorSeparationSeries a d e f).coeff 0) := by
  change _=(mapRing (R:=S d⊗[ℚ]S e) (S:=B a μ d⊗[ℚ]B a μ e) (quotientTensor a μ d e).toRingHom (tensorSeparationSeries a d e f)).coeff 0
  rw [tensorSeparationSeries,mapRing_mul_polynomial,relativeTaylor_quotient]
  rfl

lemma headRestriction_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : S (d+e)) (hf : quotientTensor a μ d e (restrictTensor (firstCut d e) f)=0) :
    headRestriction a μ d e f=0 := by
  unfold headRestriction
  simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  change (coeff.linearMap (R:=ℚ) 0)
    (mulPolynomial (mixedInverseKernelUnit a a μ d e).val
      (relativeTaylorB a μ d e (quotientTensor a μ d e (restrictTensor (firstCut d e) f))))=0
  rw [hf,map_zero,map_zero,map_zero]

lemma headRestriction_ideal (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (κ θ : ℝ) (d e : I → ℕ) (hμ : slope c η (d+e) ≤ θ)
    (hd : clippedSlope c η κ d ≤ θ) (he : clippedSlope c η κ e ≤ θ)
    (f : S (d+e)) (hf : f∈destabilizingSpace a (clippedSlope c η θ) (d+e)) :
    headRestriction a (clippedSlope c η κ) d e f=0 :=
  headRestriction_zero a _ d e f (clipped_restrict_ideal a c η hc κ θ d e hμ hd he _ f hf)

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma headRestriction_shuffle_grid (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    headRestriction a μ α β (castS h (shufflePolynomial a f g))=
      clearedConstantB a μ α β (quotientTensor a μ α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) := by
  rw [headRestriction_mk,clearedConstantB_apply,clearedSeparationB_mk,
    ←separation_shuffle_grid a h f g R,mapRing_coeff]
  rfl

omit [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in

theorem headRestriction_shuffle_head (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (κ : ℝ) {d e : I → ℕ} (f : S d) (g : S e) (hd : d≠0)
    (hk : κ < slope c η d) (ht : slope c η e ≤ κ) :
    headRestriction a (clippedSlope c η κ) d e (shufflePolynomial a f g)=
      quotientTensor a (clippedSlope c η κ) d e (f⊗ₜ[ℚ]g) := by
  let s : Pack (A:=fun i=>Fin ((d+e) i)) := fun _=>Finset.univ
  let R : Realization (d+e) s := defaultRealization (by intro i; simp [s])
  have h := headRestriction_shuffle_grid a (clippedSlope c η κ) rfl f g R
  rw [castS_rfl] at h
  rw [h]
  exact clipped_grid_constant_head a c η hc κ f g _ _ _ hd hk ht
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNPolynomial
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

lemma headRestriction_wrong_head (hc : ∀ i,0 < c i) (κ : ℝ)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (hd : d≠0)
    (hk : κ < slope c η α) (ht : slope c η β ≤ κ)
    (hs : slope c η α ≤ slope c η d)
    (hm : slope c η d=slope c η α → mass c α ≤ mass c d) (hne : d≠α) :
    headRestriction a (clippedSlope c η κ) α β (castS h (shufflePolynomial a f g))=0 :=
  headRestriction_zero a _ α β _
    (clipped_restrict_wrong_head a c η hc κ h f g (firstCut α β) hd hk ht hs hm hne)
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNMatrixTriangular
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleB_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ) (hc : ∀ i,0 < c i)
include hc
omit hc in
lemma list_mass_bound (θ : ℝ) (l : List (I → ℕ))
    (h : ∀ d∈l,mass η d ≤ θ*mass c d) : mass η l.sum ≤ θ*mass c l.sum := by
  induction l with
  | nil => simp [mass]
  | cons d l ih =>
    simp only [List.sum_cons,mass_add,mul_add]
    exact add_le_add (h d (by simp)) (ih (fun e he=>h e (by simp [he])))
lemma list_slope_le (θ : ℝ) (l : List (I → ℕ)) (hn : l.sum≠0)
    (h : ∀ d∈l,slope c η d ≤ θ) : slope c η l.sum ≤ θ := by
  apply (div_le_iff₀ (mass_pos c hc _ hn)).mpr
  apply list_mass_bound c η θ l
  intro d hd
  rw [mass_eq c η hc d]
  exact mul_le_mul_of_nonneg_right (h d hd) (mass_nonneg c (fun i=>(hc i).le) d)
omit hc [Fintype I] in
lemma list_sum_ne_zero {l : List (I → ℕ)} (hn : ∀ d∈l,d≠0) (hl : l≠[]) : l.sum≠0 := by
  obtain ⟨d,l,rfl⟩:=List.exists_cons_of_ne_nil hl
  exact add_ne_zero_left d l.sum (hn d (by simp))
lemma ordered_sum_le_head {d : I → ℕ} {l : List (I → ℕ)} (h : HNOrdered c η (d::l)) :
    slope c η (d::l).sum ≤ slope c η d := by
  apply list_slope_le c η hc
  · exact list_sum_ne_zero h.1 (by simp)
  · intro e he
    rcases List.mem_cons.mp he with rfl|he
    · rfl
    · exact ((List.pairwise_cons.mp h.2).1 e he).le
lemma ordered_tail_lt_head {d : I → ℕ} {l : List (I → ℕ)} (h : HNOrdered c η (d::l))
    (hl : l≠[]) : slope c η l.sum < slope c η d := by
  obtain ⟨e,l,rfl⟩:=List.exists_cons_of_ne_nil hl
  exact (ordered_sum_le_head c η hc ⟨fun x hx=>h.1 x (by simp [hx]),h.2.tail⟩).trans_lt
    ((List.pairwise_cons.mp h.2).1 e (by simp))

omit hc in
lemma exists_uniform_cutoff (d : I → ℕ) (θ : ℝ) :
    ∃ κ : ℝ, κ<θ ∧ ∀ e : I → ℕ,e ≤ d → e≠0 → slope c η e<θ → slope c η e ≤ κ := by
  classical
  let E : Set (I → ℕ) := {e | e ≤ d ∧ e≠0 ∧ slope c η e<θ}
  have hE : E.Finite := (Set.finite_Iic d).subset (fun _ h=>h.1)
  by_cases hn : E.Nonempty
  · obtain ⟨e,he,hm⟩:=Set.exists_max_image E (slope c η) hE hn
    exact ⟨slope c η e,he.2.2,fun f hf hz hs=>hm f ⟨hf,hz,hs⟩⟩
  · refine ⟨θ-1,by linarith,?_⟩
    intro e hd he hs
    exact (hn ⟨e,hd,he,hs⟩).elim
end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNDetectorBasics
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)
lemma hnKeyLT_irrefl (d : I → ℕ) : ¬hnKeyLT c η d d := by
  simp [hnKeyLT]
lemma hnKeyLT_trans {d e f : I → ℕ} (h : hnKeyLT c η d e) (k : hnKeyLT c η e f) :
    hnKeyLT c η d f := by
  rcases h with h|⟨h,hm⟩ <;> rcases k with k|⟨k,km⟩
  · exact Or.inl (h.trans k)
  · exact Or.inl (k ▸ h)
  · exact Or.inl (h ▸ k)
  · exact Or.inr ⟨h.trans k,hm.trans km⟩
instance hnKeyLT_strict : IsStrictOrder (I → ℕ) (hnKeyLT c η) where
  irrefl := hnKeyLT_irrefl c η
  trans := fun _ _ _=>hnKeyLT_trans c η
lemma hnKeyLT_bounds {d e : I → ℕ} (h : ¬hnKeyLT c η d e) :
    slope c η e ≤ slope c η d ∧ (slope c η d=slope c η e → mass c e ≤ mass c d) := by
  exact ⟨le_of_not_gt (fun hs=>h (Or.inl hs)),fun hs=>le_of_not_gt (fun hm=>h (Or.inr ⟨hs,hm⟩))⟩
lemma ordered_tail {d : I → ℕ} {l : List (I → ℕ)} (h : HNOrdered c η (d::l)) : HNOrdered c η l :=
  ⟨fun e he=>h.1 e (by simp [he]),h.2.tail⟩
lemma ordered_total_lt_head (hc : ∀ i,0 < c i) {d : I → ℕ} {l : List (I → ℕ)}
    (h : HNOrdered c η (d::l)) (hl : l≠[]) : slope c η (d::l).sum < slope c η d := by
  have hn:=list_sum_ne_zero h.1 (by simp)
  have ht:=list_sum_ne_zero (ordered_tail c η h).1 hl
  have H:=ordered_tail_lt_head c η hc h hl
  apply (div_lt_iff₀ (mass_pos c hc _ hn)).mpr
  simp only [List.sum_cons,mass_add]
  rw [mass_eq c η hc d,mass_eq c η hc l.sum,mul_add]
  exact add_lt_add_right (mul_lt_mul_of_pos_right H (mass_pos c hc _ ht)) _
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

lemma castS_shuffle_right {d e f : I → ℕ} (h : e=f) (x : S d) (y : S e) :
    castS (congrArg (d+·) h) (shufflePolynomial a x y)=shufflePolynomial a x (castS h y) := by
  subst f; rfl
lemma quotient_clipped_zero {κ : ℝ} {d : I → ℕ} {f : S d}
    (hf : f∈destabilizingSpace a (clippedSlope c η κ) d) :
    quotientAlg a (slope c η) d f=0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (clipped_destabilizingSpace_le a c η κ d hf)

lemma singletonDetector_apply (d : I → ℕ) (f : S [d].sum) :
    singletonDetector a c η d f=quotientAlg a (slope c η) d (castS (add_zero d) f)⊗ₜ[ℚ]1 := rfl
lemma singletonDetector_diagonal (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
    (d : I → ℕ) : (singletonDetector a c η d).comp (hnPolynomial a c η σ [d])=LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  change B a (slope c η) d at x
  change S (0 : I → ℕ) at y
  change singletonDetector a c η d (shufflePolynomial a (σ d x) y)=x⊗ₜ[ℚ]y
  erw [S_zero_eq_scalar y,shufflePolynomial_smul_right,shufflePolynomial_unit_right,map_smul,
    singletonDetector_apply,castS_trans,castS_rfl]
  change _=x⊗ₜ[ℚ](_ • (1 : S (0 : I → ℕ)))
  rw [TensorProduct.tmul_smul]
  exact congrArg (fun z=>MvPolynomial.constantCoeff y.val • (z⊗ₜ[ℚ](1 : S (0 : I → ℕ)))) (hσ d x)
lemma singletonDetector_ideal (d : I → ℕ) (θ : ℝ) (f : S [d].sum)
    (hf : f∈destabilizingSpace a (clippedSlope c η θ) [d].sum) : singletonDetector a c η d f=0 := by
  change quotientAlg a (slope c η) d (castS (add_zero d) f)⊗ₜ[ℚ](1 : S (0 : I → ℕ))=0
  exact (congrArg (fun z=>z⊗ₜ[ℚ](1 : S (0 : I → ℕ)))
    (quotient_clipped_zero a c η (castS_mem_destabilizing a _ (add_zero d) hf))).trans (TensorProduct.zero_tmul _ _)

lemma singletonDetector_off (hc : ∀ i,0 < c i) (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (hd : d≠0) (r : List (I → ℕ)) (hr : HNOrdered c η r) (h : r.sum=[d].sum) (hne : r≠[d])
    (x : HNTensor a c η r) : singletonDetector a c η d (castS h (hnPolynomial a c η σ r x))=0 := by
  cases r with
  | nil =>
    exact (hd (by simpa using h.symm)).elim
  | cons e r =>
    have hn : r≠[] := by
      intro he; subst r
      have : e=d := by simpa using h
      exact hne (by simp [this])
    have H : (singletonDetector a c η d).comp ((dimensionCast h).comp (hnPolynomial a c η σ (e::r)))=0 := by
      apply TensorProduct.ext'
      intro x y
      have hz : quotientAlg a (slope c η) d
          (castS (h.trans (add_zero d)) (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y)))=0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        apply Submodule.subset_span
        refine ⟨e,r.sum,h.trans (add_zero d),σ e x,hnPolynomial a c η σ r y,
          hr.1 e (by simp),list_sum_ne_zero (ordered_tail c η hr).1 hn,?_,?_⟩
        · have H:=ordered_total_lt_head c η hc hr hn
          simpa only [h,List.sum_cons,List.sum_nil,add_zero] using H
        · exact (dimensionCast_eq_castS (h.trans (add_zero d)) (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y))).symm
      have Hcast : castS (add_zero d) (dimensionCast h
          (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y)))=
          castS (h.trans (add_zero d)) (shufflePolynomial a (σ e x) (hnPolynomial a c η σ r y)) :=
        (congrArg (castS (add_zero d)) (dimensionCast_eq_castS h _)).trans (castS_trans _ _ _)
      exact (singletonDetector_apply a c η d _).trans
        ((congrArg (fun f=>quotientAlg a (slope c η) d f⊗ₜ[ℚ](1 : S (0 : I → ℕ))) Hcast).trans
          ((congrArg (fun z=>z⊗ₜ[ℚ](1 : S (0 : I → ℕ))) hz).trans (TensorProduct.zero_tmul _ _)))
    simpa only [LinearMap.comp_apply,dimensionCast_eq_castS,LinearMap.zero_apply] using LinearMap.congr_fun H x
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

lemma consDetector_shuffle (hc : ∀ i,0 < c i) (d : I → ℕ) (l : List (I → ℕ))
    (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hd : d≠0) (hk' : κ < slope c η d) (ht : slope c η l.sum≤κ) (f : S d) (g : S l.sum) :
    consDetector a c η d l D κ hk (shufflePolynomial a f g)=quotientAlg a (slope c η) d f⊗ₜ[ℚ]D g := by
  change TensorProduct.map _ _ (headRestriction a (clippedSlope c η κ) d l.sum (shufflePolynomial a f g))=_
  rw [headRestriction_shuffle_head a c η hc κ f g hd hk' ht]
  rfl

lemma consDetector_apply (d : I → ℕ) (l : List (I → ℕ))
    (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (f : S (d+l.sum)) : consDetector a c η d l D κ hk f=
    TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk)
      (headRestriction a (clippedSlope c η κ) d l.sum f) := rfl

lemma consDetector_ideal (hc : ∀ i,0 < c i) (d : I → ℕ) (l : List (I → ℕ))
    (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (θ : ℝ) (hs : slope c η (d+l.sum)≤θ) (hd : clippedSlope c η κ d≤θ)
    (ht : clippedSlope c η κ l.sum≤θ) (f : S (d+l.sum))
    (hf : f∈destabilizingSpace a (clippedSlope c η θ) (d+l.sum)) :
    consDetector a c η d l D κ hk f=0 := by
  exact (consDetector_apply a c η d l D κ hk f).trans
    ((congrArg (TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk))
      (headRestriction_ideal a c η hc κ θ d l.sum hs hd ht f hf)).trans (map_zero _))

lemma consDetector_diagonal (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
    (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hd : d≠0) (hk' : κ < slope c η d) (ht : slope c η l.sum≤κ)
    (hD : D.comp (hnPolynomial a c η σ l)=LinearMap.id) :
    (consDetector a c η d l D κ hk).comp (hnPolynomial a c η σ (d::l))=LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  change consDetector a c η d l D κ hk (shufflePolynomial a (σ d x) (hnPolynomial a c η σ l y))=x⊗ₜ[ℚ]y
  rw [consDetector_shuffle a c η hc d l D κ hk hd hk' ht]
  change (destabilizingSpace a (slope c η) d).mkQ (σ d x)⊗ₜ[ℚ]D (hnPolynomial a c η σ l y)=_
  rw [hσ d x,show D (hnPolynomial a c η σ l y)=y from LinearMap.congr_fun hD y]

lemma consDetector_same_head (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hd : d≠0) (hk' : κ < slope c η d) (ht : slope c η l.sum≤κ)
    (r : List (I → ℕ)) (h : r.sum=l.sum)
    (hD : ∀ x,D (castS h (hnPolynomial a c η σ r x))=0) (x : HNTensor a c η (d::r)) :
    consDetector a c η d l D κ hk (castS (congrArg (d+·) h) (hnPolynomial a c η σ (d::r) x))=0 := by
  have Hzero : (consDetector a c η d l D κ hk).comp ((dimensionCast (congrArg (d+·) h)).comp
      (hnPolynomial a c η σ (d::r)))=0 := by
    apply TensorProduct.ext'
    intro v w
    have Hcast := dimensionCast_eq_castS (congrArg (d+·) h)
      (shufflePolynomial a (σ d v) (hnPolynomial a c η σ r w))
    exact (congrArg (consDetector a c η d l D κ hk) Hcast).trans
      ((congrArg (consDetector a c η d l D κ hk) (castS_shuffle_right a h _ _)).trans
        ((consDetector_shuffle a c η hc d l D κ hk hd hk' ht _ _).trans
          ((congrArg (fun z=>quotientAlg a (slope c η) d (σ d v)⊗ₜ[ℚ]z) (hD w)).trans
            (TensorProduct.tmul_zero _ _))))
  exact (congrArg (consDetector a c η d l D κ hk) (dimensionCast_eq_castS _ _)).symm.trans
    (LinearMap.congr_fun Hzero x)

lemma consDetector_wrong_head (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (d : I → ℕ) (l : List (I → ℕ)) (D : S l.sum →ₗ[ℚ] HNTensor a c η l) (κ : ℝ)
    (hk : ∀ f : S l.sum,f∈destabilizingSpace a (clippedSlope c η κ) l.sum → D f=0)
    (hk' : κ < slope c η d) (ht : slope c η l.sum≤κ)
    (b : I → ℕ) (r : List (I → ℕ)) (h : b+r.sum=d+l.sum) (hb : b≠0)
    (hs : slope c η d ≤ slope c η b) (hm : slope c η b=slope c η d → mass c d ≤ mass c b)
    (hne : b≠d) (x : HNTensor a c η (b::r)) :
    consDetector a c η d l D κ hk (castS h (hnPolynomial a c η σ (b::r) x))=0 := by
  have Hzero : (consDetector a c η d l D κ hk).comp ((dimensionCast h).comp
      (hnPolynomial a c η σ (b::r)))=0 := by
    apply TensorProduct.ext'
    intro v w
    have Hcast := dimensionCast_eq_castS h (shufflePolynomial a (σ b v) (hnPolynomial a c η σ r w))
    exact (congrArg (consDetector a c η d l D κ hk) Hcast).trans
      ((consDetector_apply a c η d l D κ hk _).trans
        ((congrArg (TensorProduct.map (clippedToOriginal a c η κ d) (quotientDetector a c η l D κ hk))
          (headRestriction_wrong_head a c η hc κ h (σ b v) (hnPolynomial a c η σ r w) hb hk' ht hs hm hne)).trans (map_zero _)))
  exact (congrArg (consDetector a c η d l D κ hk) (dimensionCast_eq_castS _ _)).symm.trans
    (LinearMap.congr_fun Hzero x)

theorem hn_detector_exists (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ)
    (l : List (I → ℕ)) (hl : HNOrdered c η l) :
    ∃ D : S l.sum →ₗ[ℚ] HNTensor a c η l,IsHNDetector a c η σ l D := by
  classical
  induction l with
  | nil =>
    refine ⟨LinearMap.id,?_,rfl,?_⟩
    · intro θ h f hf
      change f∈destabilizingSpace a (clippedSlope c η θ) 0 at hf
      rw [destabilizingSpace_zero] at hf
      exact hf
    · intro r hr h hn he x
      exact (list_sum_ne_zero hr.1 he h).elim
  | cons d l ih =>
    have hd : d≠0:=hl.1 d (by simp)
    cases l with
    | nil =>
      refine ⟨singletonDetector a c η d,?_,singletonDetector_diagonal a c η σ hσ d,?_⟩
      · intro θ h f hf; exact singletonDetector_ideal a c η d θ f hf
      · intro r hr h hn he x; exact singletonDetector_off a c η hc σ d hd r hr h he x
    | cons e l =>
      let t:=e::l
      have ho : HNOrdered c η t := ordered_tail c η hl
      obtain ⟨D,hD⟩:=ih ho
      obtain ⟨κ,hκ,hkb⟩:=exists_uniform_cutoff c η (d+t.sum) (slope c η d)
      have hb : ∀ x∈t,slope c η x ≤ κ := by
        intro x hx
        apply hkb x _ (ho.1 x hx) ((List.pairwise_cons.mp hl.2).1 x hx)
        exact (List.le_sum_of_mem hx).trans (le_add_of_nonneg_left zero_le)
      have ht : slope c η t.sum ≤ κ := list_slope_le c η hc κ t
        (list_sum_ne_zero ho.1 (by simp [t])) hb
      let hk := hD.ideal κ hb
      refine ⟨consDetector a c η d t D κ hk,?_,?_,?_⟩
      · intro θ h f hf
        apply consDetector_ideal a c η hc d t D κ hk θ ?_ ?_ ?_ f hf
        · exact (ordered_sum_le_head c η hc hl).trans (h d (by simp))
        · exact max_le (h d (by simp)) (hκ.le.trans (h d (by simp)))
        · exact max_le (ht.trans (hκ.le.trans (h d (by simp)))) (hκ.le.trans (h d (by simp)))
      · exact consDetector_diagonal a c η hc σ hσ d t D κ hk hd hκ ht hD.diagonal
      · intro r hr h hn he x
        cases r with
        | nil => exact (list_sum_ne_zero hl.1 (by simp) h.symm).elim
        | cons b r =>
          have hb0:=hr.1 b (by simp)
          have hbd : ¬hnKeyLT c η b d := fun H=>hn (List.Lex.rel H)
          obtain ⟨hs,hm⟩:=hnKeyLT_bounds c η hbd
          by_cases hbd' : b=d
          · subst b
            have hr' : r.sum=t.sum := add_left_cancel h
            have hne : r≠t := fun H=>he (congrArg (d::·) H)
            have hn' : ¬List.Lex (hnKeyLT c η) r t := fun H=>hn (List.Lex.cons H)
            exact consDetector_same_head a c η hc σ d t D κ hk hd hκ ht r hr'
              (hD.off r (ordered_tail c η hr) hr' hn' hne) x
          · exact consDetector_wrong_head a c η hc σ d t D κ hk hκ ht b r h hb0 hs hm hbd' x
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularDirectSum
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped DirectSum
universe u v w

theorem triangular_directSum_injective {J : Type u} [DecidableEq J] {M : J → Type v} {N : Type w}
    [∀ j,AddCommGroup (M j)] [∀ j,Module ℚ (M j)] [AddCommGroup N] [Module ℚ N]
    (r : J → J → Prop) [IsStrictOrder J r]
    (F : ∀ j,M j →ₗ[ℚ] N) (D : ∀ j,N →ₗ[ℚ] M j)
    (hdiag : ∀ j x,D j (F j x)=x)
    (hoff : ∀ i j,j≠i → ¬r j i → ∀ x,D i (F j x)=0) :
    Function.Injective (DirectSum.toModule ℚ J N F) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hn
  have hs : (x.support : Set J).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h=>hn (DFinsupp.support_eq_empty.mp h))
  have hwf : WellFounded (fun i j=>r i j ∧ i∈x.support ∧ j∈x.support) :=
    Set.wellFoundedOn_iff.mp x.support.finite_toSet.wellFoundedOn
  obtain ⟨i,hi,hm⟩:=hwf.has_min (x.support : Set J) hs
  have H : D i (DirectSum.toModule ℚ J N F x)=x i := by
    calc
      _ = D i (DirectSum.toModule ℚ J N F (∑ j∈x.support,DirectSum.of M j (x j))) :=
        congrArg (fun y=>D i (DirectSum.toModule ℚ J N F y)) (DirectSum.sum_support_of x).symm
      _ = ∑ j∈x.support,D i (F j (x j)) := by
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (D i) (DirectSum.toModule_lof (R:=ℚ) (φ:=F) j (x j))
      _ = x i := by
        rw [Finset.sum_eq_single i]
        · exact hdiag i (x i)
        · intro j hj hji
          exact hoff i j hji (fun h=>hm j hj ⟨h,hj,hi⟩) (x j)
        · intro h; exact (h hi).elim
  rw [hx,map_zero] at H
  exact (DFinsupp.mem_support_iff.mp hi) H.symm
end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNIndependent
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

instance hnIndex_strict (d : I → ℕ) :
    IsStrictOrder (HNIndex c η d) (fun l r=>List.Lex (hnKeyLT c η) l.val r.val) where
  irrefl := fun l=>List.lex_irrefl (hnKeyLT_irrefl c η) l.val
  trans := fun _ _ _=>List.lex_trans (hnKeyLT_trans c η)

theorem hnPolynomialExpansion_injective_oai (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    Function.Injective (hnPolynomialExpansion a c η σ d) := by
  classical
  choose D hD using fun l : HNIndex c η d=>hn_detector_exists a c η hc σ hσ l.val l.property.2
  let F := fun l : HNIndex c η d=>(dimensionCast l.property.1).comp (hnPolynomial a c η σ l.val)
  let T := fun l : HNIndex c η d=>(D l).comp (dimensionCast l.property.1.symm)
  apply triangular_directSum_injective (fun l r : HNIndex c η d=>List.Lex (hnKeyLT c η) l.val r.val) F T
  · intro l x
    change D l (dimensionCast l.property.1.symm (dimensionCast l.property.1 (hnPolynomial a c η σ l.val x)))=x
    rw [dimensionCast_trans]
    exact LinearMap.congr_fun (hD l).diagonal x
  · intro l r hne hn x
    change D l (dimensionCast l.property.1.symm (dimensionCast r.property.1 (hnPolynomial a c η σ r.val x)))=0
    rw [dimensionCast_trans,dimensionCast_eq_castS]
    exact (hD l).off r.val r.property.2 (r.property.1.trans l.property.1.symm) hn
      (fun h=>hne (Subtype.ext h)) x

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u} : type_of% @OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective_oai.{u} := @OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective_oai.{u}
