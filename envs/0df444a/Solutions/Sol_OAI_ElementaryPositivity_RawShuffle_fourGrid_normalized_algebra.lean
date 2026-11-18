-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:19.35405+00:00
-- url     : https://prove2.me/submissions/6820c7eb-ab31-4937-9e65-747786d1135e

import Mathlib
import Definitions.Def_OAIQ368Chrom036
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourGrid_taylor_factor

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

lemma kernel_product_rearrange {R : Type*} [CommRing R]
    (K L A B C D P Q r : R) (h : K*L*C=r*(A*B*D)) :
    K*L*(P*Q*C)=r*((A*P)*(B*Q)*D) := by
  calc
    _ = (K*L*C)*(P*Q) := by ring
    _ = _ := by rw [h]; ring

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourModule
lemma firstColumn_tensorSeparationSeries (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) :
    mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a d₁ d₂ f)=
      (fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f))) :=
  (mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom).map_mul _ _

lemma secondColumn_tensorSeparationSeries (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (g : S (e₁+e₂)) :
    mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a e₁ e₂ g)=
      (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g))) :=
  (mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom).map_mul _ _

lemma fourInputSeries_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    fourInputSeries a d₁ e₁ d₂ e₂ f g=
      ((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f)))) *
      ((fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g)))) *
      (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val := by
  exact congrArg₂
    (fun x y : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) =>
      x * y * (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val)
    (firstColumn_tensorSeparationSeries a d₁ e₁ d₂ e₂ f)
    (secondColumn_tensorSeparationSeries a d₁ e₁ d₂ e₂ g)

lemma kernel_product_rearrange_with_factors {R : Type*} [CommRing R]
    (K L A B C D P Q r X Y : R) (h : K*L*C=r*(A*B*D))
    (hX : X=P*Q*C) (hY : Y=(A*P)*(B*Q)*D) : K*L*X=r*Y := by
  rw [hX,hY]
  exact kernel_product_rearrange K L A B C D P Q r h

lemma fourGrid_normalized_algebra_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂))
    (K L r : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))
    (h : K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
      r*((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
        (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
        (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
          (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val)) :
    K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
      r*fourInputSeries a d₁ e₁ d₂ e₂ f g :=
  @kernel_product_rearrange_with_factors
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) (cancelSeriesRing d₁ e₁ d₂ e₂)
    K L _ _ _ _ _ _ r _ _ h
    (fourGrid_taylor_factor a d₁ e₁ d₂ e₂ f g) (fourInputSeries_factor a d₁ e₁ d₂ e₂ f g)

end ElementaryPositivity.RawShuffle

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra_oai.{u_1}
