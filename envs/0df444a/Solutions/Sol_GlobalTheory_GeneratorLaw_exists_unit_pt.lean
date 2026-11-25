-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.exists_unit_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:16.887656+00:00
-- url     : https://prove2.me/submissions/156e2616-af25-4b18-8e42-249d4fae44a8

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_congr
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_unit
import Theorems.Thm_GlobalTheory_GeneratorLaw_exists_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
theorem _root_.solution (hU : GenScheme.Univ (fun k => (O k).L) q.left u) {Y : Over S}
    (a : κ → Γ(Y.left, ⊤)ˣ) :
    ∃ g : Y ⟶ G, g ≫ q = 1 ∧ ∀ (W : Over S) (r : W ⟶ Y), nv O q u (r ≫ g) = av O a r := by
  obtain ⟨g, h₁, h₂⟩ := exists_pt hU (1 : Y ⟶ B) _
    fun k => (Rep.unit (a k)).congr fun V _ h => (inv_mul_cancel _).symm
  exact ⟨g, h₁, fun W r => funext₃ (h₂ W r)⟩
end GlobalTheory.GeneratorLaw
