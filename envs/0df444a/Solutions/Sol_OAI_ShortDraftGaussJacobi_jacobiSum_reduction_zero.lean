-- Prove2me | solution 1 for OAI.ShortDraftGaussJacobi.jacobiSum_reduction_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:32.104609+00:00
-- url     : https://prove2.me/submissions/5aca00a6-aa6a-47b8-b36c-7d294e211c50

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ShortDraftGaussJacobi_sum_cubic_jacobi_reduction_zero

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
theorem _root_.solution {R : Type*} [CommRing R]
    (χ : MulChar F R) (ρ : R →+* F) (m : ℕ)
    (hχ : ∀ x : F, ρ (χ x) = x ^ m)
    (hm : 2 * m < Fintype.card F - 1) :
    ρ (jacobiSum χ χ) = 0 := by
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, hχ]
  exact sum_cubic_jacobi_reduction_zero m hm
end OAI.ShortDraftGaussJacobi
