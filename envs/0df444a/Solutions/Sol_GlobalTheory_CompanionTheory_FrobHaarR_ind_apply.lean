-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.ind_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:44.171517+00:00
-- url     : https://prove2.me/submissions/78e91311-cebc-4137-8e3e-a81b46932fe7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple

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
theorem _root_.solution (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    (ind K hK : G → ℂ) x = Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x :=
  rfl
end GlobalTheory.CompanionTheory.FrobHaarR
