-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:11.647577+00:00
-- url     : https://prove2.me/submissions/c584ecdc-096a-4c10-bb88-c5a8e52880d3

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033

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
noncomputable local instance columnFourRing_re3b331_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.columnFourAlgebra
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourTensorKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
noncomputable local instance kernelTensorDistrib_re3b331_1 (d e : I → ℕ) :
    DistribSMul (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) where
  smul_add := mul_add
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.kernelFourAlg
noncomputable local instance kernelTensorSelf_re3b331_1 (d e : I → ℕ) :
    Module (S d⊗[ℚ]S e) (S d⊗[ℚ]S e) := Semiring.toModule
noncomputable local instance kernelTensorNonUnital_re3b331_1 (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (S d⊗[ℚ]S e) := (kernelTensorRing d e).toNonUnitalNonAssocSemiring
noncomputable local instance kernelFourNonUnital_re3b331_1 (d₁ e₁ d₂ e₂ : I → ℕ) :
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

lemma fourKernel_secondColumn (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (R:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (S:=MvPolynomial (CellVars d₁ e₁⊕CellVars d₂ e₂) ℚ) (fourValueAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (Units.map (mapRing (R:=S e₁⊗[ℚ]S e₂) (S:= (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
        (SeparationInfinity.inverseKernelUnit a e₁ e₂))=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) := by
  refine Eq.trans (fourKernel_lift_naturality a e₁ e₂ d₁ e₁ d₂ e₂
    ( secondColumnAlg d₁ e₁ d₂ e₂ ) _ (fourValue_secondColumn d₁ e₁ d₂ e₂)) ?_
  have he : secondColumnVars d₁ e₁ d₂ e₂ =
      Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr) := by
    funext x; cases x <;> rfl
  rw [he]
  have h := rawKernel_rename (σ:=CellVars d₁ e₁⊕CellVars d₂ e₂) a e₁ e₂
    (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr)
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
lemma fourSeriesValue_second_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourSecondInverseUnit a d₁ e₁ d₂ e₂)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) :=
  fourKernel_secondColumn a d₁ e₁ d₂ e₂

end ElementaryPositivity.RawShuffle

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second_oai.{u_1}
