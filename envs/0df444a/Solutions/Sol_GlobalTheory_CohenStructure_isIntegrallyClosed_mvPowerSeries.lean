-- Prove2me | solution 1 for GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:22.243338+00:00
-- url     : https://prove2.me/submissions/e5d14c3e-61a2-4ed2-b6ea-8c616202790d

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
import Theorems.Thm_GlobalTheory_CohenStructure_isDomain_mvPowerSeries
import Theorems.Thm_GlobalTheory_PowerSeriesNormal_isIntegrallyClosed_powerSeries


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
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := isDomain_mvPowerSeries R n
    have := GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries (MvPowerSeries (Fin n) R)
    exact IsIntegrallyClosed.of_equiv (finSuccEquiv R n).toRingEquiv.symm
end GlobalTheory.CohenStructure
