-- Prove2me | solution 1 for GlobalTheory.Chow.genericForm_mem_incidenceIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:01.058786+00:00
-- url     : https://prove2.me/submissions/3cd699bf-d16b-4862-9fdb-4db954eabc7e

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
theorem _root_.solution (p : Ideal (MvPolynomial σ K)) (i : β) :
    genericForm K σ i ∈ incidenceIdeal β p :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
end GlobalTheory.Chow
