-- Prove2me | solution 1 for GlobalTheory.Chow.incidenceIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:37.379642+00:00
-- url     : https://prove2.me/submissions/9f175027-e561-48fd-ad92-cd8592de6604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution {p : Ideal (MvPolynomial σ K)}
    {J : Ideal (MvPolynomial (β × σ) (MvPolynomial σ K))} :
    incidenceIdeal β p ≤ J ↔ (∀ g ∈ p, C g ∈ J) ∧ ∀ i, genericForm K σ i ∈ J := by
  rw [incidenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]
  rfl
end GlobalTheory.Chow
