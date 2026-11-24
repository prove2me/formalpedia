-- Prove2me | solution 1 for GlobalTheory.TorusEnd.top_le_preimage_finset_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:07.973431+00:00
-- url     : https://prove2.me/submissions/903fb736-b2aa-4b51-838f-512ad90883bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTopLePreimageOfISupEqTop
import Theorems.Thm_GlobalTheory_top_le_preimage_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.TorusEnd
namespace GlobalTheory.TorusEnd
theorem _root_.solution {X : Scheme.{0}} {κ : Type*} (x : Sp ℂ ⟶ X) (s : Finset κ) (U : κ → X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (s.inf U) ↔ ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => rw [Finset.inf_insert, top_le_preimage_inf, ih, Finset.forall_mem_insert]
end GlobalTheory.TorusEnd
