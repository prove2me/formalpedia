-- Prove2me | solution 1 for GlobalTheory.app_comp_eq_zero_of_germ_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:27:32.720714+00:00
-- url     : https://prove2.me/submissions/f4754a5e-d6f7-4a18-89ba-a735fd59febe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecDivOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AppCompEqZeroOfGermDvd
import Theorems.Thm_GlobalTheory_ThickeningDivisible_gs_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_stalkMap


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U))
    (h : ∀ y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) : ((b ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz ↦ ?_
  have hz' : b z ∈ a ⁻¹ᵁ U := hz
  have key : ∀ {W : Scheme.{0}} (c : Y ⟶ W) (V : W.Opens) (g : Γ(W, V)), c (b z) ∈ V →
      gs (b ≫ c) z V g = (b.stalkMap z).hom (gs c (b z) V g) := fun c V g hV ↦ by
    rw [← gs_pull b c z V hV, gs_stalkMap b z _ hV, gs_pull (𝟙 Y) c (b z) V hV, Category.id_comp]
  obtain ⟨t, ht⟩ := h (b z) hz'
  have h0 : (b.stalkMap z).hom (cst (a ≫ p) (b z) r) = 0 :=
    (key (a ≫ p) ⊤ _ trivial).symm.trans (hr z)
  rw [gs_pull (𝟙 Z) (b ≫ a) z U hz, Category.id_comp, key a U f hz', ht, map_mul, h0, zero_mul,
    ThickeningDivisible.gs_zero]
end GlobalTheory
