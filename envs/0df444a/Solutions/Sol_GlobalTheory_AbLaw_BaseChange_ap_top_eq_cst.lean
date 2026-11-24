-- Prove2me | solution 1 for GlobalTheory.AbLaw.BaseChange.ap_top_eq_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:00.231709+00:00
-- url     : https://prove2.me/submissions/45195083-34be-49c3-b54e-743ad31bb2d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsProjByBaseChange
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_cst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.BaseChange
namespace GlobalTheory.AbLaw.BaseChange
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {W : X.Opens} (h : W ≤ f ⁻¹ᵁ ⊤) (d : Γ(Spec (CommRingCat.of R), ⊤)) :
    ∃ r, ap f h d = cst f W r := by
  obtain ⟨r, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of R))) (W := ⊤) rfl).2 d
  exact ⟨r, by rw [ap_cst, Category.comp_id]⟩
end GlobalTheory.AbLaw.BaseChange
