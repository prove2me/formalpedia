-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.rep_nv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:45.853805+00:00
-- url     : https://prove2.me/submissions/93c4df9e-05a0-49c3-9fc3-1ee4f79f8911

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_mul
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_family
import Theorems.Thm_GlobalTheory_GeneratorLaw_rep_rv

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
variable {O q u}
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k)) (k : κ) {Y : Over S} (x : Y ⟶ G) :
    Rep (O k).L (fun _ _ h => (h (x ≫ q).left)⁻¹ * h (1 : Y ⟶ B).left)
      (fun Z r z J => cv O q u k Z (r ≫ x.left) z J * rv O k Z (r ≫ Y.hom) z J) :=
  ((Rep.family (hu k)).pull x.left).mul (rep_rv O k Y)
end GlobalTheory.GeneratorLaw
