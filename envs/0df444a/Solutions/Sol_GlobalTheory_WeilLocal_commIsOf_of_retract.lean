-- Prove2me | solution 1 for GlobalTheory.WeilLocal.commIsOf_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:14:39.346095+00:00
-- url     : https://prove2.me/submissions/8fa35cfb-cb69-4062-866f-1d41018d7ee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsIffOfIsGrpPullbackComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsLocalOnBaseOfOpenCover
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
import Theorems.Thm_GlobalTheory_CommPairing_exists_pull
import Theorems.Thm_GlobalTheory_CommPairing_whisker_translT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.WeilLocal
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
private theorem gm_comp_global_eq_gm_units_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (c : Γ(X, ⊤)ˣ) :
    gm (f ≫ g) z ⊤ c = gm f z ⊤ (Units.map g.appTop.hom.toMonoidHom c) := by
  unfold gm pullU
  rw [dif_pos (show (f ≫ g) z ∈ (⊤ : X.Opens) from trivial), dif_pos (show f z ∈ (⊤ : Y.Opens) from trivial)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl
end GlobalTheory.WeilLocal
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.WeilLocal
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilLocal
theorem _root_.solution (hL : L.IsLB) {T T' : Over S} (g : T' ⟶ T) (h : T ⟶ T') (w : g ≫ h = 𝟙 T')
    {c : Γ(T.left, ⊤)ˣ} (θx' θy' : ThetaGrp A L k T')
    (H : ∀ θx θy : ThetaGrp A L k T, θx.pt = h ≫ θx'.pt → θy.pt = h ≫ θy'.pt → CommIsOf A L k θx θy c) :
    CommIsOf A L k θx' θy' (Units.map g.left.appTop.hom.toMonoidHom c) := by
  obtain ⟨θx, hx, hxv⟩ := exists_pull hL h θx'
  obtain ⟨θy, hy, hyv⟩ := exists_pull hL h θy'
  have Hc := (commIsOf_iff hL θx θy c).1 (H θx θy hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  have e := Hc Z (r ≫ (g ▷ A).left) z J hJ
  have e1 : r ≫ (g ▷ A).left ≫ (h ▷ A).left = r := by
    rw [← Over.comp_left, ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.comp_id]
  have e2 : ∀ x : T' ⟶ A, r ≫ (g ▷ A).left ≫ (translT A (h ≫ x)).left ≫ (h ▷ A).left = r ≫ (translT A x).left := by
    intro x
    rw [← Over.comp_left _ _ _ (translT A (h ≫ x)), whisker_translT, Over.comp_left, ← Category.assoc (g ▷ A).left,
      ← Over.comp_left _ _ _ (g ▷ A), ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.id_comp]
  have e3 : r ≫ (g ▷ A).left ≫ (fst T A).left = (r ≫ (fst T' A).left) ≫ g.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left, Category.assoc]
  rw [hxv _ _ _ _ hJ, hxv _ _ _ _ hJ, hyv _ _ _ _ hJ, hyv _ _ _ _ hJ, hx, hy] at e
  simp only [Category.assoc] at e
  rw [e1, e2, e2, e3, gm_comp_global_eq_gm_units_map] at e
  exact e
end GlobalTheory.WeilLocal
