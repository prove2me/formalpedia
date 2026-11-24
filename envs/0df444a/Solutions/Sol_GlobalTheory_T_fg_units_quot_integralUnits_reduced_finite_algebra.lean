-- Prove2me | solution 1 for GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:15.752951+00:00
-- url     : https://prove2.me/submissions/ee29879a-0c48-43cb-8f93-4ea77d1743ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
import Theorems.Thm_GlobalTheory_UnitLemma_NormUnits_units_quot_intUnits_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) → ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A] [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  first | exact @GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | exact GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | (intros; apply GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg <;> assumption)
end _root_.GlobalTheory.T
