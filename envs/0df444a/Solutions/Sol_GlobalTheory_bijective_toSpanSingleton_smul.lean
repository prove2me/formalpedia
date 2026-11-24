-- Prove2me | solution 1 for GlobalTheory.bijective_toSpanSingleton_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:43.171411+00:00
-- url     : https://prove2.me/submissions/2556f64d-ef8f-4e24-a1f1-9e7cb40ed424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
variable {A M}
namespace GlobalTheory
theorem _root_.solution {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) (g : G) :
    Function.Bijective (LinearMap.toSpanSingleton A M (g • e)) := by
  have : ⇑(LinearMap.toSpanSingleton A M (g • e)) =
      (g • ·) ∘ LinearMap.toSpanSingleton A M e ∘ (g⁻¹ • ·) := by
    ext a
    simp [smul_distrib_smul]
  rw [this]
  exact (MulAction.bijective g).comp (he.comp (MulAction.bijective g⁻¹))
end GlobalTheory
