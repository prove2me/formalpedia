-- Prove2me | solution 1 for OAI.ShortDraftGaussJacobi.cubic_jacobi_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:32.759758+00:00
-- url     : https://prove2.me/submissions/a376dfff-137c-4841-99f1-73faa33196e0

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
open OAI.ShortDraftGaussJacobi
open Finset
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.ShortDraftGaussJacobi
theorem _root_.solution (χ : MulChar F ℂ)
    (horder : orderOf χ = 3)
    (hchar : ringChar ℂ ≠ ringChar F) :
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = (Fintype.card F : ℂ) := by
  have hχ : χ ≠ 1 := by
    intro h
    simp [h] at horder
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have ho : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [horder] at ho
    norm_num at ho
  exact jacobiSum_mul_jacobiSum_inv hchar hχ hχ hχ2
end OAI.ShortDraftGaussJacobi
