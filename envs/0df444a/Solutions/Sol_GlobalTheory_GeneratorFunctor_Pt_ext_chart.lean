-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.Pt.ext_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:14.605268+00:00
-- url     : https://prove2.me/submissions/ae0af2c0-533f-4f10-8a10-22c99b9d9c23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)
variable {N}
namespace GlobalTheory.GeneratorFunctor
namespace Pt
theorem _root_.solution {Z : Scheme.{0}} {x y : Pt N Z} (hb : x.b = y.b) (j : ∀ k, (N k).ι)
    (hx : ∀ k, ⊤ ≤ 𝟙 Z ⁻¹ᵁ x.b ⁻¹ᵁ (N k).U (j k)) (hy : ∀ k, ⊤ ≤ 𝟙 Z ⁻¹ᵁ y.b ⁻¹ᵁ (N k).U (j k))
    (hs : ∀ k, pb (𝟙 Z) _ ⊤ (hx k) (x.s k (j k)) = pb (𝟙 Z) _ ⊤ (hy k) (y.s k (j k))) :
    x = y := by
  refine Pt.ext' hb fun k i => ?_
  have := congrArg (pb (𝟙 Z) ⊤ (x.b ⁻¹ᵁ (N k).U i) le_top) (hs k)
  rw [pb_id_comp, pb_id_comp] at this
  rw [← pb_id le_rfl (x.s k i), x.compat k (j k) i _ (le_top.trans (hx k)) le_rfl,
    y.compat k (j k) i _ (le_top.trans (hy k)) (by rw [hb]), this, pb_congr hb]
end Pt
end GlobalTheory.GeneratorFunctor
