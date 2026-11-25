-- Prove2me | solution 1 for GlobalTheory.CommPairing.weilIs_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:21.087081+00:00
-- url     : https://prove2.me/submissions/013d3621-fb30-479e-9129-96c1e50e1433

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_change
import Theorems.Thm_GlobalTheory_CommPairing_exists_commIsOf_pull

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommPairing
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H (h.left p)
  have w : (h.left ∣_ V) ≫ V.ι = (h.left ⁻¹ᵁ V).ι ≫ h.left := morphismRestrict_ι _ _
  let h' : overRes (h.left ⁻¹ᵁ V) ⟶ overRes V := Over.homMk (h.left ∣_ V) (by
    show (h.left ∣_ V) ≫ V.ι ≫ T.hom = (h.left ⁻¹ᵁ V).ι ≫ T'.hom
    rw [← Category.assoc, w, Category.assoc, Over.w h])
  have w' : h' ≫ overResι V = overResι (h.left ⁻¹ᵁ V) ≫ h := Over.OverMorphism.ext w
  obtain ⟨θx', θy', hx', hy', H'⟩ := exists_commIsOf_pull hL h' (hc θx θy hx hy)
  rw [hx, ← Category.assoc, w', Category.assoc] at hx'
  rw [hy, ← Category.assoc, w', Category.assoc] at hy'
  have e : Units.map h'.left.appTop.hom.toMonoidHom (unitRes V c) =
      unitRes (h.left ⁻¹ᵁ V) (Units.map h.left.appTop.hom.toMonoidHom c) := by
    apply Units.ext
    have := congrArg (fun q => q.appTop.hom c.val) w
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  rw [e] at H'
  exact ⟨h.left ⁻¹ᵁ V, hp, ⟨θx', θy', hx', hy'⟩, fun a b ha hb =>
    commIsOf_change hG hA hL (ha.trans hx'.symm) (hb.trans hy'.symm) H'⟩
end GlobalTheory.CommPairing
