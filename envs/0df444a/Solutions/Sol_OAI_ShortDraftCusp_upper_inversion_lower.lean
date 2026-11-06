-- Prove2me | solution 1 for OAI.ShortDraftCusp.upper_inversion_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:22:03.159709+00:00
-- url     : https://prove2.me/submissions/9ea30ea7-46a4-4f4d-af03-b3418a3c528e

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
namespace OAI.ShortDraftCusp
theorem _root_.solution (u v : R) :
    U u * E * L (-v) = !![u + v, -1; 1, 0] := by
  simp [U,E,L]
end OAI.ShortDraftCusp
