-- Prove2me | solution 1 for GlobalTheory.isLocalHom_of_injective_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:45.542804+00:00
-- url     : https://prove2.me/submissions/b5fa2f19-91a3-4c34-8de6-2359576687e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt

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
omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
namespace GlobalTheory
theorem _root_.solution {B : Type*} [CommRing B] [Algebra ℤ_[p] B]
    (g : B →ₐ[ℤ_[p]] integralClosure ℤ_[p] K) (hg : Function.Injective g) :
    IsLocalHom (g : B →+* integralClosure ℤ_[p] K) := by
  refine RingHom.IsIntegral.isLocalHom ?_ hg
  refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[p] B) _ ?_
  rw [g.comp_algebraMap]
  exact fun x => (Algebra.IsIntegral.isIntegral x : IsIntegral ℤ_[p] x)
end GlobalTheory
