-- Prove2me | solution 1 for GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:43.704099+00:00
-- url     : https://prove2.me/submissions/f658e1e7-3a11-4d6c-b65c-684f1750dce2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDVROfClosedSubringPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSystemOfParametersInsert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Theorems.Thm_GlobalTheory_CohenStructure_isAdicComplete_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_P1_isAdicComplete_ps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.CohenStructure
namespace GlobalTheory.CohenStructure
theorem _root_.solution (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact isAdicComplete_of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := ReciprocityTheory.P1.isAdicComplete_ps (R := MvPowerSeries (Fin n) R)
    exact isAdicComplete_of_ringEquiv (finSuccEquiv R n).toRingEquiv.symm
end GlobalTheory.CohenStructure
