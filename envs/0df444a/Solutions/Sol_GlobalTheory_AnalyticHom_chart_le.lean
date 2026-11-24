-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.chart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:58:51.461084+00:00
-- url     : https://prove2.me/submissions/8c74d804-40e7-4942-a140-66e9afc17646

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm

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
variable {X Y : Scheme.{0}} (L : LB X) (κ : Y ⟶ X) (σ : X ⟶ Y) (e : σ ≫ κ = 𝟙 X) (N : ℕ)
include e
namespace GlobalTheory.AnalyticHom
theorem _root_.solution (j : PUnit → L.ι) :
    L.wchart (fun _ : PUnit => 𝟙 X) j ≤
      σ ⁻¹ᵁ L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit) := by
  intro y hy
  have h : κ (σ y) = y := by rw [← Scheme.Hom.comp_apply, e]; rfl
  refine Set.mem_iInter.2 fun _ => ?_
  have := Set.mem_iInter.1 hy PUnit.unit
  show κ (σ y) ∈ L.U (j PUnit.unit)
  rw [h]; exact this
end GlobalTheory.AnalyticHom
