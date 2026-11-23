-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:29.472811+00:00
-- url     : https://prove2.me/submissions/5446a5ab-80dc-4ceb-b2f4-b0fb19524b46

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat
variable {P G₁ : Type} [Group P] [Group G₁]
namespace GlobalTheory.CompanionTheory.SplitExtLat
theorem _root_.solution [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) (z : π.ker × G₁) :
    splitHomeo ι π hι hπ h z = (z.1 : P) * ι z.2 := rfl
end GlobalTheory.CompanionTheory.SplitExtLat
