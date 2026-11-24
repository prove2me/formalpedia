-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.le_preimage_lbPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:49.562552+00:00
-- url     : https://prove2.me/submissions/2629c5ce-7bc7-4635-a47c-d232443a6f50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g')
namespace GlobalTheory.AnalyticHom
theorem _root_.solution {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) (k : ℕ) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (lbPow L k).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  refine (le_preimage_wchart x L (fun _ : PUnit => 𝟙 X) j).trans ?_
  simp only [Category.comp_id]
  exact ⟨fun h => h _, fun h _ => h⟩
end GlobalTheory.AnalyticHom
