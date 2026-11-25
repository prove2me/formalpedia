-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.rep_rv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:08.019799+00:00
-- url     : https://prove2.me/submissions/20401f5e-23f7-4840-9aa9-5f22151a0ec6

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
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} (O : κ → RigLB B) {G : Over S} (q : G ⟶ B)
  (u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ)
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution (k : κ) (Y : Over S) : Rep (O k).L (fun _ _ h => h (1 : Y ⟶ B).left)
    (fun Z r z J => rv O k Z (r ≫ Y.hom) z J) :=
  Rep.pull (σ := fun _ _ h => h (eSec B))
    ⟨PUnit, inferInstance, _, _, (O k).rig, (O k).rigGen, fun V _ h => by simp, fun _ _ _ _ _ => rfl⟩ Y.hom
end GlobalTheory.GeneratorLaw
