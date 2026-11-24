-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.ind_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:19.324833+00:00
-- url     : https://prove2.me/submissions/a71328f8-34e7-49ca-9622-8e325eea7aa0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_ind_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.FrobHaarR
theorem _root_.solution (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (x : G) :
    (ind K hK : G → ℂ) (k * x) = (ind K hK : G → ℂ) x := by
  have h : k * x ∈ (K : Set G) ↔ x ∈ (K : Set G) :=
    Subgroup.mul_mem_cancel_left K.toSubgroup hk
  by_cases hx : x ∈ (K : Set G)
  · rw [ind_apply, ind_apply, Set.indicator_of_mem (h.2 hx), Set.indicator_of_mem hx]
  · rw [ind_apply, ind_apply, Set.indicator_of_notMem (fun h' => hx (h.1 h')),
      Set.indicator_of_notMem hx]
end GlobalTheory.CompanionTheory.FrobHaarR
