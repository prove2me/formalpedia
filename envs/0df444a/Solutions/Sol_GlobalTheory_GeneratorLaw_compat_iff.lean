-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.compat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:01.121716+00:00
-- url     : https://prove2.me/submissions/0465c1f2-b591-4a86-82f6-3ecb55ec4a16

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
variable {X Y Y' : Scheme.{0}} {L : LB X}
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution {b : Y ⟶ X} (s : ∀ i : L.ι, Γ(Y, b ⁻¹ᵁ L.U i)ˣ) : GenScheme.Compat L b s ↔
    ∀ Z (r : Z ⟶ Y) (z : Z) i i', b (r z) ∈ L.U i → b (r z) ∈ L.U i' → gm r z (b ⁻¹ᵁ L.U i') (s i') =
      gm (r ≫ b) z _ (L.g i i') * gm r z (b ⁻¹ᵁ L.U i) (s i) := by
  constructor
  · intro h Z r z i i' hi hi'
    have hm : r z ∈ b ⁻¹ᵁ (L.U i ⊓ L.U i') := ⟨hi, hi'⟩
    have := congrArg (gm r z _) (h i i')
    rwa [map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull r b z _ hm] at this
  · intro h i i'
    refine unit_ext fun y hy => ?_
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull _ b y _ hy]
    exact h _ (𝟙 Y) y i i' hy.1 hy.2
end GlobalTheory.GeneratorLaw
