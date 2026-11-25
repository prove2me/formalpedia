-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:35.636801+00:00
-- url     : https://prove2.me/submissions/d3e39662-221b-4eb8-9b9a-cd0facbefeb2

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_exists_family
import Theorems.Thm_GlobalTheory_GeneratorLaw_gm_appLE
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
theorem _root_.solution {X G Y : Scheme.{0}} {N : κ → LB X} (hN : ∀ k, (N k).IsLB) {q : G ⟶ X}
    {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ} (hU : GenScheme.Univ N q u) (b : Y ⟶ X)
    (F : ∀ k, Vals (N k) Y) (h : ∀ k, Rep (N k) (fun _ _ h => (h b)⁻¹) (F k)) :
    ∃ g : Y ⟶ G, g ≫ q = b ∧ ∀ k Z (r : Z ⟶ Y) z J, Good (N k) z J →
      gm (r ≫ g) z (q ⁻¹ᵁ (N k).U (J ((r ≫ g) ≫ q))) (u k _) = F k Z r z J := by
  choose s hs hv using fun k => Rep.exists_family (hN k) (h k)
  obtain ⟨g, ⟨rfl, hgs⟩, -⟩ := hU Y b s hs
  refine ⟨g, rfl, fun k Z r z J hJ => ?_⟩
  have e : ∀ i, s k i = GenScheme.pb g (q ⁻¹ᵁ (N k).U i) ((g ≫ q) ⁻¹ᵁ (N k).U i) le_rfl (u k i) :=
    fun i => Units.ext (hgs k i).symm
  rw [← hv k Z r z J hJ, Category.assoc, e]
  exact (gm_appLE r g z _ ((g ≫ q) ⁻¹ᵁ (N k).U (J (r ≫ g ≫ q))) le_rfl (hJ (r ≫ g ≫ q)) _).symm
end GlobalTheory.GeneratorLaw
