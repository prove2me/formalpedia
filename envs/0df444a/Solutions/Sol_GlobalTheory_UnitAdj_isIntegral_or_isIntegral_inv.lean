-- Prove2me | solution 1 for GlobalTheory.UnitAdj.isIntegral_or_isIntegral_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:09.274901+00:00
-- url     : https://prove2.me/submissions/b39497e7-b028-48ba-bcc3-04db36d5a039

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
import Theorems.Thm_GlobalTheory_FormalIsogeny_isDiscreteValuationRing_integralClosure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.UnitAdj
namespace GlobalTheory.UnitAdj
theorem _root_.solution {O K L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [Algebra O L]
    [IsScalarTower O K L] [FiniteDimensional K L] (y : L) :
    IsIntegral O y ∨ IsIntegral O y⁻¹ := by
  haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O K L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := O) K L
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left; rw [← hz]; exact z.2
  · right; rw [← hz]; exact z.2
end GlobalTheory.UnitAdj
