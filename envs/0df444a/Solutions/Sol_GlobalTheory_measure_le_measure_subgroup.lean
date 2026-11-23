-- Prove2me | solution 1 for GlobalTheory.measure_le_measure_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:12.045847+00:00
-- url     : https://prove2.me/submissions/db16a262-9e46-4724-9349-62a535a148e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_measure_le_of_isFundamentalDomain_of_ae_covers

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
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}
namespace GlobalTheory
theorem _root_.solution (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) : μ D ≤ μ D' :=
  measure_le_of_isFundamentalDomain_of_ae_covers hD
    (hD'.ae_covers.mono fun _ ⟨k, hk⟩ => ⟨k, hk⟩)
end GlobalTheory
