-- Prove2me | solution 1 for GlobalTheory.OrbitUnfold.setIntegral_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:17:32.666148+00:00
-- url     : https://prove2.me/submissions/d07bdd24-d0c1-41bf-8c42-e43411b791f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
open GlobalTheory.OrbitUnfold
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
namespace GlobalTheory.OrbitUnfold
namespace _root_.GlobalTheory.OrbitUnfold
theorem _root_.solution (g : H) (f : H → ℂ) :
    ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setIntegral_preimage_emb (measurableEmbedding_mulLeft g) f 𝓕
end _root_.GlobalTheory.OrbitUnfold
end GlobalTheory.OrbitUnfold
