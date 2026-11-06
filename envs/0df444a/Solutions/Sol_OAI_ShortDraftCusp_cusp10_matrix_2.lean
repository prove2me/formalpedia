-- Prove2me | solution 2 for OAI.ShortDraftCusp.cusp10_matrix
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:33.913085+00:00
-- url     : https://prove2.me/submissions/ed45e599-268d-48d2-81e9-fc1d38579078

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
open OAI.ShortDraftCusp
variable {R : Type*} [CommRing R]

theorem solution (ω : R) :
    U (-ω) * E * L (-ω) = E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, L, E, Matrix.mul_apply, Fin.sum_univ_two]
