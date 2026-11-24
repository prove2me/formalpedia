-- Prove2me | solution 1 for GlobalTheory.NormUnits.fg_quot_intUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:12.924085+00:00
-- url     : https://prove2.me/submissions/5362260f-97aa-4e0b-98d2-d0bbcb3a7b41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetCosetsIntegralNormUnits
import Theorems.Thm_GlobalTheory_T_fg_units_quot_integralUnits_finite_field_ext
import Theorems.Thm_GlobalTheory_T_fg_units_quot_integralUnits_reduced_finite_algebra
import Theorems.Thm_GlobalTheory_T_isReduced_of_separable_markedCharpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    Group.FG (B.Aˣ ⧸ intUnits K.O B.A) := fun K B hP =>
  haveI := GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP
  GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra K (GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext K) B.A (GlobalTheory.T.isReduced_of_separable_markedCharpoly K B hP)
end GlobalTheory.NormUnits
