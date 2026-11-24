-- Prove2me | solution 1 for GlobalTheory.RelChart.top_le_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:25.768653+00:00
-- url     : https://prove2.me/submissions/1cc61a6f-53e2-4c35-9a88-04c72f335ab8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsChartWithParameters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.RelChart
open GlobalTheory.TangentOrigin
namespace GlobalTheory.RelChart
theorem _root_.solution {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage]
  exact fun _ hp => e (hV hp)
end GlobalTheory.RelChart
