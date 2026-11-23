-- Prove2me | solution 1 for GlobalTheory.finiteIndex_map_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:42.972124+00:00
-- url     : https://prove2.me/submissions/aa96c037-93c4-4f19-9a0c-53659282edca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty

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
variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}
variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]
variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}
omit [MeasurableSpace X] [MulAction G X] [MulAction H X] [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G]
namespace GlobalTheory
theorem _root_.solution [K.FiniteIndex] (hφ : Function.Surjective φ) :
    (K.map φ).FiniteIndex :=
  ⟨ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (K.index_map_dvd hφ)⟩
end GlobalTheory
