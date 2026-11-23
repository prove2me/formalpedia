-- Prove2me | solution 1 for GlobalTheory.exists_isFundamentalDomain_and_quotMeasure_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:51.088991+00:00
-- url     : https://prove2.me/submissions/c3af9535-e7e5-4cb2-9619-0e4104debffc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_of_ae_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
variable {X}
namespace GlobalTheory
theorem _root_.solution [ProperlyDiscontinuousSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (hfree : μ {x | MulAction.stabilizer G x ≠ ⊥} = 0) :
    (∃ D : Set X, MeasurableSet D ∧ IsFundamentalDomain G D μ) ∧
      ∀ D : Set X, IsFundamentalDomain G D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) = quotMeasure G μ := by
  obtain ⟨D, hD, -, -, h⟩ := exists_isFundamentalDomain_of_ae_free G μ hfree
  exact ⟨⟨D, hD, h⟩, fun D h => (quotMeasure_eq_of_isFundamentalDomain h).symm⟩
end GlobalTheory
