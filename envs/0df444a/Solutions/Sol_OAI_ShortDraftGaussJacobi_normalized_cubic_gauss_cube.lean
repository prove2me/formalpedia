-- Prove2me | solution 1 for OAI.ShortDraftGaussJacobi.normalized_cubic_gauss_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:33.397783+00:00
-- url     : https://prove2.me/submissions/b19106df-7d30-4157-bff3-9a33058bafe5

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ShortDraftGaussJacobi_cubic_gauss_cube

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
theorem _root_.solution (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (horder : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    (gaussSum χ ψ / (Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 3 =
      jacobiSum χ χ / (Real.sqrt (Fintype.card F : ℝ) : ℂ) := by
  let s : ℂ := Real.sqrt (Fintype.card F : ℝ)
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (Real.sqrt_pos.2 hcard).ne'
  have hs2 : s ^ 2 = (Fintype.card F : ℂ) := by
    dsimp [s]
    exact_mod_cast Real.sq_sqrt hcard.le
  rw [div_pow, cubic_gauss_cube χ ψ horder hψ, ← hs2]
  field_simp
  change s ^ 2 * jacobiSum χ χ = jacobiSum χ χ * s ^ 2
  ring
end OAI.ShortDraftGaussJacobi
