-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:18.368729+00:00
-- url     : https://prove2.me/submissions/319b95ae-1766-46d1-9fe2-3549e74e6671

import Mathlib
import Definitions.Def_OAIQ368Chrom028
import Definitions.Def_OAIQ368Chrom036
import Definitions.Def_OAIQ368Chrom038
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_cellTransfer_normalized
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourTaylor_column_product

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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNRestrictionOrder
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
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

end ElementaryPositivity.SlopeArithmetic

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
noncomputable local instance taylorFourRing_r67a393_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra
noncomputable local instance taylorTensorNonUnital_r67a393_1 (d e : I → ℕ) :
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
noncomputable local instance clearBTensorSA_r67a393_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellLeadingSum
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

noncomputable local instance cellLeadTensorN_r67a393_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) :=
  (clearBTensorB a μ d e).toNonUnitalNonAssocSemiring
lemma clearedConstantB_castTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (x : S d⊗[ℚ]S e) :
    clearedConstantB a μ d' e' (quotientTensor a μ d' e' (castTensor h k x))=
      castBTensor a μ h k (clearedConstantB a μ d e (quotientTensor a μ d e x)) := by
  subst d'
  subst e'
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorDistrib cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule

lemma mappedInverseKernel_zero_head {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : I → I → ℕ) (e : I → ℕ) (F : S 0⊗[ℚ]S e →ₐ[ℚ]R) :
    mappedInverseKernel a 0 e F=1 := by
  unfold mappedInverseKernel
  rw [inverseKernelUnit_zero_left,map_one]

lemma mappedInverseRatio_zero_head {R : Type*} [CommRing R] [Algebra ℚ R]
    (a b : I → I → ℕ) (e : I → ℕ) (F : S 0⊗[ℚ]S e →ₐ[ℚ]R) :
    (mappedInverseKernel a 0 e F*(mappedInverseKernel b 0 e F)⁻¹).val=1 := by
  rw [mappedInverseKernel_zero_head,mappedInverseKernel_zero_head,inv_one,mul_one,Units.val_one]

lemma separation_zero_right (a : I → I → ℕ) (d : I → ℕ) (f : S d) :
    tensorSeparationSeries a d 0 (castS (add_zero d).symm f)=
    polynomial (relativeTaylor d 0 (f⊗ₜ[ℚ](1 : S 0))) := by
  rw [tensorSeparationSeries,inverseKernelUnit_zero_right,Units.val_one,one_mul,restrictTensor_zero_right]
lemma separation_zero_left (a : I → I → ℕ) (e : I → ℕ) (g : S e) :
    tensorSeparationSeries a 0 e (castS (zero_add e).symm g)=
    polynomial (relativeTaylor 0 e ((1 : S 0)⊗ₜ[ℚ]g)) := by
  rw [tensorSeparationSeries,inverseKernelUnit_zero_left,Units.val_one,one_mul,restrictTensor_zero_left]

lemma fourInputSeries_head (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    fourInputSeries a d 0 0 e (castS (add_zero d).symm f) (castS (zero_add e).symm g)=
    polynomial (fourRelativeTaylor d 0 0 e ((f⊗ₜ[ℚ](1 : S 0))⊗ₜ[ℚ]((1 : S 0)⊗ₜ[ℚ]g))) := by
  unfold fourInputSeries
  have hf := congrArg (mapRing (firstColumnAlg d 0 0 e).toRingHom)
    (separation_zero_right a d f)
  have hg := congrArg (mapRing (secondColumnAlg d 0 0 e).toRingHom)
    (separation_zero_left a e g)
  have hkernel := mappedInverseRatio_zero_head a (fun i j => a j i)
    (0 : I → ℕ) (crossingColumnAlg d 0 0 e)
  exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) hf hg) hkernel).trans
    ((mul_one _).trans (fourTaylor_column_product d 0 0 e _ _))

lemma cellTransfer_head_normalized (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    rawClearedSeparation a (d+0) (0+e)
        (cellTransfer a d 0 0 e
          (fourGridPolynomial a (castS (add_zero d).symm f) (castS (zero_add e).symm g) d 0 0 e))=
    rawRelativeSeries (d+0) (0+e)
      (castS (add_zero d).symm f⊗ₜ[ℚ]castS (zero_add e).symm g) := by
  unfold rawClearedSeparation
  simp only [LinearMap.comp_apply,mulPolynomial_apply,AlgHom.toLinearMap_apply]
  rw [cellTransfer_normalized,fourInputSeries_head,twoTarget_polynomial_relativeTaylor,
    twoTargetTransfer_tmul,shufflePolynomial_unit_right,shufflePolynomial_unit_left]
  simp [eulerForm,rawRelativeSeries]
end ElementaryPositivity.RawShuffle

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNDiagonalConstant
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
attribute [local instance] clearedSepTensorRing clearedSepTensorAlg clearBTensorB clearBTensorBA

omit [Fintype I] [DecidableEq I] in
lemma rawRelativeSeries_constant (d e : I → ℕ) (x : S d⊗[ℚ]S e) :
    (rawRelativeSeries d e x).coeff 0=x := by
  have ht : translationS d 0=LinearMap.id := by apply LinearMap.ext; intro f; exact translationS_zero d f
  have he := relativeTaylor_eval d e x 0
  rw [map_zero,←Polynomial.coeff_zero_eq_eval_zero,ht,TensorProduct.map_id] at he
  simpa only [rawRelativeSeries,show (0 : ℤ)=-(0 : ℕ) by rfl,polynomial_coeff,LinearMap.id_apply] using he

lemma fourGridPolynomial_castSources (a : I → I → ℕ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (f : S d) (g : S e)
    (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourGridPolynomial a (castS h f) (castS k g) d₁ e₁ d₂ e₂=
      fourGridPolynomial a f g d₁ e₁ d₂ e₂ := by
  subst d'; subst e'; rfl

lemma clearedConstantB_cell_head (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (f : S d) (g : S e) :
    clearedConstantB a μ (d+0) (0+e)
      (quotientTensor a μ (d+0) (0+e)
        (cellTransfer a d 0 0 e (fourGridPolynomial a f g d 0 0 e)))=
    quotientTensor a μ (d+0) (0+e)
      (castS (add_zero d).symm f⊗ₜ[ℚ]castS (zero_add e).symm g) := by
  have h := cellTransfer_head_normalized a d e f g
  rw [fourGridPolynomial_castSources] at h
  rw [clearedConstantB_apply,clearedSeparationB_mk]
  change (mapRing (quotientTensor a μ (d+0) (0+e)).toRingHom
    (rawClearedSeparation a (d+0) (0+e) _)).coeff 0=_
  rw [h,mapRing_coeff,rawRelativeSeries_constant]
  rfl

lemma castBTensor_quotient_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (f : S d) (g : S e) :
    castBTensor a μ h k (quotientTensor a μ d e (f⊗ₜ[ℚ]g))=
      quotientTensor a μ d' e' (castS h f⊗ₜ[ℚ]castS k g) := by
  subst d'; subst e'; rfl

lemma clearedConstantB_cell_head_cast (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e d₁ e₁ d₂ e₂ : I → ℕ) (h₁ : d₁+e₁=d) (h₂ : d₂+e₂=e)
    (he : e₁=0) (hd : d₂=0) (f : S d) (g : S e) :
    clearedConstantB a μ d e (quotientTensor a μ d e
      (castTensor h₁ h₂ (cellTransfer a d₁ e₁ d₂ e₂
        (fourGridPolynomial a f g d₁ e₁ d₂ e₂))))=
    quotientTensor a μ d e (f⊗ₜ[ℚ]g) := by
  subst e₁; subst d₂
  have h₁' : d₁=d := by simpa only [add_zero] using h₁
  have h₂' : e₂=e := by simpa only [zero_add] using h₂
  subst d₁; subst e₂
  rw [clearedConstantB_castTensor,clearedConstantB_cell_head,castBTensor_quotient_tmul]
  simp only [castS_trans,castS_rfl]
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

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma shapeComplement_full (s : Pack (A:=A)) : shapeComplement (fullShape s)=0 := by
  funext i; simp [shapeComplement,fullShape]
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma zeroShape_val (s : Pack (A:=A)) : (fun i=>(zeroShape s i).val)=0 := rfl
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma eq_fullShape_of_complement {s : Pack (A:=A)} (u : CutShape s)
    (hu : shapeComplement u=0) : u=fullShape s := by
  funext i; apply Fin.ext
  have h := congrFun hu i
  have hh := (u i).isLt
  change (s i).card-(u i).val=0 at h
  change (u i).val=(s i).card
  omega
omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma eq_zeroShape_of_val {s : Pack (A:=A)} (u : CutShape s)
    (hu : (fun i=>(u i).val)=0) : u=zeroShape s := by
  funext i; apply Fin.ext; exact congrFun hu i

omit [∀ i, Fintype (A i)] in
lemma clipped_grid_constant_head_oai (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (κ : ℝ) {d e : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization d (left p)) (T : Realization e (right p)) (hd : d≠0)
    (hk : κ < slope c η d) (ht : slope c η e ≤ κ) :
    clearedConstantB a (clippedSlope c η κ) d e
      (quotientTensor a (clippedSlope c η κ) d e (gridTensor a f g p R T))=
    quotientTensor a (clippedSlope c η κ) d e (f⊗ₜ[ℚ]g) := by
  classical
  simp only [gridTensor,map_sum]
  rw [Finset.sum_eq_single (fullShape (left p))]
  · rw [Finset.sum_eq_single (zeroShape (right p))]
    · unfold gridShapeTensor
      exact clearedConstantB_cell_head_cast a _ d e _ _ _ _ _ _
        (shapeComplement_full _) (zeroShape_val _) f g
    · intro v _ hv
      rw [clipped_gridShape_nonhead_zero a c η hc κ f g p R T _ v hd hk ht le_rfl (fun _=>le_rfl),map_zero]
      rintro ⟨_,h⟩
      exact hv (eq_zeroShape_of_val v h)
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    rw [clipped_gridShape_nonhead_zero a c η hc κ f g p R T u v hd hk ht le_rfl (fun _=>le_rfl),map_zero]
    rintro ⟨h,_⟩
    exact hu (eq_fullShape_of_complement u h)
  · intro h; exact (h (Finset.mem_univ _)).elim

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head_oai.{u_1, u_2} := @OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head_oai.{u_1, u_2}
