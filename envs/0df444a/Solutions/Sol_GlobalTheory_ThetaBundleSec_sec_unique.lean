-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSec.sec_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:59:54.005774+00:00
-- url     : https://prove2.me/submissions/c71b61e1-c9af-4dfa-b65d-b0fe69c077f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Theorems.Thm_GlobalTheory_existsUnique_point_of_ringHom
import Theorems.Thm_P2M_GlobalTheory_eq_of_valAt__eq_229a7b1c0d79
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


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
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSec
open ThetaBundleSym
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.ThetaBundleSec
theorem _root_.solution [IsReduced A.left] [LocallyOfFiniteType A.hom] (u : HolUnif A L g) (n : ℕ)
    {θ : (Fin g → ℂ) → ℂ} {s s' : (lbPow L n).Sec} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ) : s = s' := by
  have hf : s.f = s'.f := by
    funext j
    refine eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom A inferInstance inferInstance _ _ _
      fun x hx => ?_
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [hs j z hx, hs' j z hx]
  cases s
  cases s'
  cases hf
  rfl
end GlobalTheory.ThetaBundleSec
