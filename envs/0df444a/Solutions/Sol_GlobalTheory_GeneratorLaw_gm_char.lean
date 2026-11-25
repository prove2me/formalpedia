-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.gm_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:50:25.184252+00:00
-- url     : https://prove2.me/submissions/f28a27d5-19b3-4b8e-81e1-3f633e5dabcb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W : Over S}
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution (t : W ⟶ splitTorus S X) (z : W.left) (χ : X) : gm t.left z ⊤ (charUnit S X χ) =
    gm (𝟙 W.left) z ⊤ (splitTorusPointsEquiv S X W t (Multiplicative.ofAdd χ)) := by
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial, splitTorusPointsEquiv_val]
  rfl
end GlobalTheory.GeneratorLaw
