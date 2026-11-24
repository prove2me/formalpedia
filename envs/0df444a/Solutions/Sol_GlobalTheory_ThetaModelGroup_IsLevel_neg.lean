-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.IsLevel.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:25.572637+00:00
-- url     : https://prove2.me/submissions/39b518a0-d108-41f9-9c53-ee5cc65d383f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor

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
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
namespace GlobalTheory.ThetaModelGroup
namespace IsLevel
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {N : ℕ} {f : (Fin g → ℂ) → ℂ} (h : IsLevel τ N f) :
    IsLevel τ N (fun z => f (-z)) := by
  refine ⟨h.1.comp (differentiable_id (𝕜 := ℂ) (E := Fin g → ℂ)).neg, fun n n' z => ?_⟩
  have := h.2 (-n) (-n') (-z)
  simp only [ofIntVec_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at this
  rw [← this]
  congr 1
  abel
end IsLevel
end GlobalTheory.ThetaModelGroup
