-- Prove2me | solution 1 for OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:08.821461+00:00
-- url     : https://prove2.me/submissions/a6f1bc3b-f855-4303-b03d-87036365bf47

import Mathlib
import Definitions.Def_OAIQ368Chrom026
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourGrid_relativeTaylor_factor

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
omit [Fintype I] [DecidableEq I] in
private lemma fourPolynomial_mapped_product_pair (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : Polynomial (S d₁⊗[ℚ]S d₂)) (q : Polynomial (S e₁⊗[ℚ]S e₂)) :
    polynomial (Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p *
      Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q)=
      mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial p)*
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial q) :=
  (polynomial.map_mul _ _).trans
    (congrArg₂ (fun x y => x * y)
      (polynomial_map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p).symm
      (polynomial_map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q).symm)

omit [Fintype I] [DecidableEq I] in
lemma fourPolynomial_mapped_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : Polynomial (S d₁⊗[ℚ]S d₂)) (q : Polynomial (S e₁⊗[ℚ]S e₂))
    (r : Polynomial ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    polynomial (Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p *
      Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q * r)=
      mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial p)*
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial q)*polynomial r := by
  calc
    _ = polynomial (Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p *
        Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q) * polynomial r :=
      polynomial.map_mul _ _
    _ = _ := congrArg (fun t => t * polynomial r)
      (fourPolynomial_mapped_product_pair d₁ e₁ d₂ e₂ p q)

lemma fourGrid_taylor_factor_oai (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (polynomial (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f))) *
    mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (polynomial (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g))) *
    polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)) := by
  rw [fourGrid_relativeTaylor_factor]
  exact fourPolynomial_mapped_product d₁ e₁ d₂ e₂ _ _ _

end ElementaryPositivity.RawShuffle

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor_oai.{u_1} := @OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor_oai.{u_1}
