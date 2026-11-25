-- Prove2me | solution 1 for GlobalTheory.mem_integralClosure_padicInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:58.434096+00:00
-- url     : https://prove2.me/submissions/aa2d55e6-213b-4255-929c-f1cb90235c95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_isIntegral_padicInt_iff_norm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {p K}
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
namespace GlobalTheory
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : K) :
    x ∈ integralClosure ℤ_[p] K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  rw [← isIntegral_padicInt_iff_norm_le_one, mem_integralClosure_iff]
  exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[p]) K.val.toRingHom.injective).symm
end GlobalTheory
