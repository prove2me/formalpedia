-- Prove2me | solution 1 for GlobalTheory.Chow.IsBlockHomogeneous.isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:45.805906+00:00
-- url     : https://prove2.me/submissions/3ac40fc3-64c2-4a24-a28a-f22857bb4ae1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_isBlockHomogeneous_iff

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
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']
namespace GlobalTheory.Chow
namespace IsBlockHomogeneous
theorem _root_.solution [Fintype σ] [Fintype β] {f : MvPolynomial (β × σ) K}
    {a : β → ℕ} (h : IsBlockHomogeneous f a) : f.IsHomogeneous (∑ i, a i) := by
  intro d hd
  have := isBlockHomogeneous_iff.1 h d (mem_support_iff.2 hd)
  change Finsupp.weight (fun _ => 1) d = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => this i
end IsBlockHomogeneous
end GlobalTheory.Chow
