-- Prove2me | solution 1 for GlobalTheory.ThetaAct.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:37.364803+00:00
-- url     : https://prove2.me/submissions/4ee691ac-a2f3-44a6-be56-586195c00ffb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Theorems.Thm_GlobalTheory_CommPairing_surj_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_linComb_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ratio_glue


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
open GlobalTheory GlobalTheory.ThetaAct
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaAct
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) : ∃ c : Γ(T.left, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        (tval θ' r z J).val = gs (r ≫ (fst T A).left) z ⊤ c.val * (tval θ r z J).val := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  obtain ⟨ρ, hρ⟩ := TLinPf.ratio_glue _ (TLinPf.linComb_cover L hL _ _) u' u hu' hu
  obtain ⟨c, hc⟩ := surj_fst hG hA T ρ.val
  obtain ⟨d, hd⟩ := surj_fst hG hA T ρ.inv
  have inj : Function.Injective (fst T A).left.appTop.hom := by
    have e : (ptSecT A a).left ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
    refine Function.LeftInverse.injective (g := (ptSecT A a).left.appTop.hom) fun b => ?_
    have := congrArg (fun q => q.appTop.hom b) e
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
      CommRingCat.hom_id, RingHom.id_apply] using this
  have hcd : c * d = 1 := inj (by rw [map_mul, map_one, hc, hd]; exact ρ.val_inv)
  refine ⟨⟨c, d, hcd, by rw [_root_.mul_comm]; exact hcd⟩, fun Z r z J hJ => ?_⟩
  have hm := hJ.mem ![(snd T A).left, (translPt A a).left] r
  refine (congrArg Units.val ((congrArg (gm r z _) (hρ _)).trans (map_mul _ _ _))).trans
    ((Units.val_mul _ _).trans (congrArg (· * _) ?_))
  exact (congrArg Units.val (gm_res r z le_top hm _)).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) hc.symm).trans (gs_pull r _ z ⊤ trivial c)))
end GlobalTheory.ThetaAct
