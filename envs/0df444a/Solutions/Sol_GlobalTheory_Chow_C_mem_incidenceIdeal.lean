-- Prove2me | solution 1 for GlobalTheory.Chow.C_mem_incidenceIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:37.298805+00:00
-- url     : https://prove2.me/submissions/c4675334-d4c5-4472-af68-779700271f78

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
theorem _root_.solution {p : Ideal (MvPolynomial σ K)} {g : MvPolynomial σ K} (hg : g ∈ p) :
    C g ∈ incidenceIdeal β p :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)
end GlobalTheory.Chow
