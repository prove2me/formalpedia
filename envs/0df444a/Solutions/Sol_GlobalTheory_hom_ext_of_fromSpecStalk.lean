-- Prove2me | solution 1 for GlobalTheory.hom_ext_of_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:52.907751+00:00
-- url     : https://prove2.me/submissions/6db3adeb-a3cb-4564-85d8-9da51f89b484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : ∀ x, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  have key : ∀ x : X, ∃ e : f x = g x, f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ g.stalkMap x := by
    intro x
    have e1 : (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm ⟨f x, f.stalkMap x, inferInstance⟩ =
        (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm ⟨g x, g.stalkMap x, inferInstance⟩ := by
      simp only [SpecToEquivOfLocalRing_symm_apply]
      rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk, h x]
    exact SpecToEquivOfLocalRing_eq_iff.mp ((Equiv.injective _) e1)
  have hc : ∀ (U : Y.Opens) (s : Γ(Y, U)) (y y' : Y) (e : y = y') (hy : y ∈ U) (hy' : y' ∈ U),
      (Y.presheaf.stalkCongr (Inseparable.of_eq e)).hom (Y.presheaf.germ U y hy s) =
        Y.presheaf.germ U y' hy' s := by
    rintro U s y _ rfl hy hy'
    simp
  refine Scheme.Hom.ext ?_ fun U => ?_
  · ext x
    exact (key x).1
  · ext s
    apply TopCat.Presheaf.section_ext X.sheaf
    intro x hx
    obtain ⟨e, he⟩ := key x
    have hfx : f x ∈ U := e ▸ hx
    change X.presheaf.germ _ x hx _ = X.presheaf.germ _ x hx _
    rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply,
      ← Scheme.Hom.germ_stalkMap_apply f U x hfx, ← Scheme.Hom.germ_stalkMap_apply g U x hx, he,
      CommRingCat.comp_apply, hc U s (f x) (g x) e hfx hx]
end GlobalTheory
