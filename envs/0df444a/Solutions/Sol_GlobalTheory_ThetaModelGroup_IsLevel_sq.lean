-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.IsLevel.sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:30:54.590014+00:00
-- url     : https://prove2.me/submissions/c87f404c-5d4f-4ceb-8abd-955f40bd49de

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
    IsLevel τ (N * 2) (fun z => f z ^ 2) := by
  refine ⟨h.1.pow 2, fun n n' z => ?_⟩
  simp only [h.2, mul_pow, eC]
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
end IsLevel
end GlobalTheory.ThetaModelGroup
