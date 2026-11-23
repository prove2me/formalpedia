-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitExtLat.mul_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:59.357292+00:00
-- url     : https://prove2.me/submissions/af1bb5cb-0cc1-4a65-ad0d-0d00c0b48691

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_splitHomeo_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply

set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat
variable {P G₁ : Type} [Group P] [Group G₁]
namespace GlobalTheory.CompanionTheory.SplitExtLat
theorem _root_.solution (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (g : P) (m : π.ker) (u : G₁) :
    g * ((m : P) * ι u) =
      ((kerPart ι π h g * MulAut.conjNormal (ι (π g)) m : π.ker) : P) * ι (π g * u) := by
  simp only [kerPart, Subgroup.coe_mul, MulAut.conjNormal_apply, map_mul]
  group
end GlobalTheory.CompanionTheory.SplitExtLat
