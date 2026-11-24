-- Prove2me | solution 1 for GlobalTheory.TwistTranslate.gen_of_pull_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:09.56896+00:00
-- url     : https://prove2.me/submissions/01c32de2-5d21-4b50-bd8f-c051933857c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TwistedPowTranslate
import Theorems.Thm_GlobalTheory_TwistTranslate_exists_gen_of_sec
import Theorems.Thm_GlobalTheory_TwistTranslate_gen_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_exists_sec_of_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistTranslate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.TwistTranslate
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (W : Y.Opens) (hW : ∀ y, y ∈ W)
    (c : LB.Gen ((LB.LinComb L φ ε).pull W.ι)) (hc : c.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := Y) W.ι c hc
  let e := IsOpenImmersion.lift W.ι (𝟙 Y)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; exact hW _)
  have he : e ≫ W.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine gen_congr hL ?_ (exists_gen_of_sec hL (pullSec s e) fun y J hJ => ?_)
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ
end GlobalTheory.TwistTranslate
