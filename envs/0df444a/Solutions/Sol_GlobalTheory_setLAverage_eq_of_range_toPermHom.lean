-- Prove2me | solution 1 for GlobalTheory.setLAverage_eq_of_range_toPermHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:08.720833+00:00
-- url     : https://prove2.me/submissions/b0bb15f7-eb8d-4cc3-acc2-923a3d84c64b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_setLAverage_eq_of_surjective

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
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {B D D' : Set X}
  {K : Subgroup G}
namespace GlobalTheory
theorem _root_.solution [K.FiniteIndex]
    (hD : IsFundamentalDomain (MulAction.toPermHom G X).range D μ)
    (hD' : IsFundamentalDomain (MulAction.toPermHom K X).range D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ :=
  setLAverage_eq_of_surjective (MulAction.toPermHom G X).rangeRestrict_surjective
    (fun _ _ => rfl) hD (MulAction.toPermHom K X).rangeRestrict_surjective (fun _ _ => rfl) hD' hu
end GlobalTheory
