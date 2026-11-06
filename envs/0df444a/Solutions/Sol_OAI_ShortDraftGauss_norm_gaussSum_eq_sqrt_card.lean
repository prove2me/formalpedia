-- Prove2me | solution 1 for OAI.ShortDraftGauss.norm_gaussSum_eq_sqrt_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:53.996909+00:00
-- url     : https://prove2.me/submissions/0c3c110a-2aa1-489c-b95f-e0fe8e904194

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ShortDraftGauss
open Complex
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.ShortDraftGauss
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  let g := gaussSum χ ψ
  have hprod : g * conj g = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ hψ
    rw [← star_gaussSum_eq] at h
    simpa only [g, Complex.star_def] using h
  have hnorm : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    apply Complex.ofReal_injective
    calc
      ((‖g‖ ^ 2 : ℝ) : ℂ) = (‖g‖ : ℂ) ^ 2 := by norm_cast
      _ = g * conj g := (Complex.mul_conj' g).symm
      _ = (Fintype.card F : ℂ) := hprod
      _ = ((Fintype.card F : ℝ) : ℂ) := by norm_cast
  have hcard : (0 : ℝ) ≤ Fintype.card F := by positivity
  have hsqrt := Real.sq_sqrt hcard
  nlinarith [norm_nonneg g, Real.sqrt_nonneg (Fintype.card F)]
end OAI.ShortDraftGauss
