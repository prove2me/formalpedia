-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.sval_isActOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:50.062917+00:00
-- url     : https://prove2.me/submissions/3e89c29f-b6f7-440f-a595-8a297b080cbd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {k : ℤ} {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)} (h : IsActOf A L k θ s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal s' r z J =
      (thetaVal θ.φ r z J).val *
        secVal s (r ≫ (translT A θ.pt).left) z J := by
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  refine Eq.trans ?_ (congrArg (_ * ·) (sval_of (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s
    (r ≫ (translT A θ.pt).left) z J (fun _ => J (r ≫ (translPt A θ.pt).left))
    (fun _ => by rw [Category.assoc, e])).symm)
  have hm := hJ.mem ![(snd T A).left, (translPt A θ.pt).left] r
  refine (gs_res r z (chart_le_zero A L _ _) hm _).symm.trans ((congrArg (gs r z _)
    (h fun b => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] b))).trans ((gs_mul r z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hm _) ((gs_res r z _ hm _).trans (gs_pull r _ z _ ?_ _)))))
  exact chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) _ hm
end GlobalTheory.TorsionFixedAut
