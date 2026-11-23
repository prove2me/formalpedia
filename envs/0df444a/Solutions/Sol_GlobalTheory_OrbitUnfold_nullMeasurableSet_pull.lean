-- Prove2me | solution 1 for GlobalTheory.OrbitUnfold.nullMeasurableSet_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:27.742873+00:00
-- url     : https://prove2.me/submissions/820fabb5-04f6-478f-8cf0-8de717839551

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
theorem _root_.solution (hF : IsFundamentalDomain Γ 𝓕 ν) (g : H) :
    NullMeasurableSet (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 g) ν :=
  hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving
end _root_.GlobalTheory.OrbitUnfold
end GlobalTheory.OrbitUnfold
