-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.top_le_preimage_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:40:08.8582+00:00
-- url     : https://prove2.me/submissions/7bcb02ea-efd4-44dc-912a-705753306831

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_spMap_fst_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution (x : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ W ↔ ⊤ ≤ (spMap fstC ≫ x) ⁻¹ᵁ W := by
  constructor
  · intro h p _
    exact h (Set.mem_univ (spMap fstC p))
  · intro h p _
    obtain ⟨q, rfl⟩ := spMap_fst_surjective p
    exact h (Set.mem_univ q)
end GlobalTheory.TangentOrigin
