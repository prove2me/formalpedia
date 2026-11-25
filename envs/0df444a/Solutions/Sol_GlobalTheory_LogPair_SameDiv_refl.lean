-- Prove2me | solution 1 for GlobalTheory.LogPair.SameDiv.refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:27.776052+00:00
-- url     : https://prove2.me/submissions/2333c4d2-6531-4efd-bf4e-b28084d619f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SameDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
namespace GlobalTheory.LogPair
namespace SameDiv
theorem _root_.solution {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (σ : L.Sec) : SameDiv σ σ := fun x => by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  exact ⟨L.U i, i, i, le_rfl, le_rfl, 1, hi, by simp⟩
end SameDiv
end GlobalTheory.LogPair
