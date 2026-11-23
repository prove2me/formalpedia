-- Prove2me | solution 1 for GlobalTheory.WeightGen.HasGen.of_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:57.324948+00:00
-- url     : https://prove2.me/submissions/5a185684-d131-4d63-a676-79696bbb1a44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}
namespace GlobalTheory.WeightGen
namespace HasGen
theorem _root_.solution (h : a ≫ q = p ≫ q) {N : LB B} {c : GermFn P} {A : Type} (W : A → B.Opens)
    (hW : ∀ x, ∃ α, x ∈ W α) (F : N.ι → A → GermFn G)
    (rep : ∀ j α, ∃ y : Γ(G, q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z),
      q (r z) ∈ N.U j → q (r z) ∈ W α → gm r z _ y = F j α Z r z)
    (tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (j j' : N.ι) (α α' : A), q (r z) ∈ N.U j →
      q (r z) ∈ N.U j' → q (r z) ∈ W α → q (r z) ∈ W α' →
      F j' α' Z r z = gm (r ≫ q) z _ (N.g j j') * F j α Z r z)
    (wt : ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : N.ι) (α : A), q (p (r z)) ∈ N.U j →
      q (p (r z)) ∈ W α → F j α Z (r ≫ a) z = c Z r z * F j α Z (r ≫ p) z) :
    HasGen q a p N c := by
  choose y hy using rep
  have glue : ∀ j, ∃ s : Γ(G, q ⁻¹ᵁ N.U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (α : A),
      q (r z) ∈ N.U j → q (r z) ∈ W α → gm r z _ s = F j α Z r z := by
    intro j
    obtain ⟨s, hs⟩ := glue_unit (q ⁻¹ᵁ N.U j) (fun α => q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α)
      (fun _ => inf_le_left) (fun x hx => by
        obtain ⟨α, hα⟩ := hW (q x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hx, hα⟩) (y j) (fun α α' x hx => by
        have e₁ := tr _ (𝟙 G) x j j α α' hx.1.1 hx.1.1 hx.1.2 hx.2.2
        have e₂ := tr _ (𝟙 G) x j j α α hx.1.1 hx.1.1 hx.1.2 hx.1.2
        exact (hy j α _ (𝟙 G) x hx.1.1 hx.1.2).trans ((e₂.trans e₁.symm).trans
          (hy j α' _ (𝟙 G) x hx.1.1 hx.2.2).symm))
    refine ⟨s, fun Z r z α h₁ h₂ => ?_⟩
    have hm : r z ∈ q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hm s).symm.trans ((congrArg (gm r z _) (hs α)).trans
      (hy j α Z r z h₁ h₂))
  choose s hs using glue
  refine ⟨s, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · obtain ⟨α, hα⟩ := hW (q (r z))
    rw [hs j Z r z α h₁ hα, hs j' Z r z α h₂ hα]
    exact tr Z r z j j' α α h₁ h₂ hα hα
  · obtain ⟨α, hα⟩ := hW (q (p (r z)))
    rw [hs j Z (r ≫ p) z α h₁ hα, hs j Z (r ≫ a) z α ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _)
      ((pt_eq h (r z)).symm ▸ hα : q (a (r z)) ∈ _)]
    exact wt Z r z j α h₁ hα
end HasGen
end GlobalTheory.WeightGen
