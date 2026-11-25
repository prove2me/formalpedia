-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.expT_zeroU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:34:54.945928+00:00
-- url     : https://prove2.me/submissions/6c276f3f-59e6-4cd3-956c-86bdbda6d02d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_RelModel_sval_const
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
import Theorems.Thm_GlobalTheory_UnifZero_scal_specMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
namespace GlobalTheory.UU.RelModel
theorem _root_.solution [IsHausdorff I R] {σ : (zeroU R I).SecGT (𝟙_ _) k} {f} (h : (zeroU R I).ExpT (𝟙_ _) k σ f) {a b : R}
    (ha : SecConst σ (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left a))
    (hb : SecConst (f PUnit.unit) (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left b)) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := I) _ fun e => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ((scal_bijective (𝟙 _)).1 ?_))
  rw [← scal_specMap, ← scal_specMap, Category.id_comp]
  refine fn_ext fun z _ => ?_
  obtain ⟨s, hs⟩ := h e
  let x : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e (𝟙_ _)).left :=
    pullback.lift (thick R I e) (𝟙 _) (by simp)
  let r : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (𝟙_ _ ⊗ 𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    pullback.lift (thick R I e) (thick R I e) rfl
  have hr : r ≫ (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left = thick R I e := pullback.lift_snd _ _ _
  have hx : x ≫ (fstG I e (𝟙_ _)).left = thick R I e := pullback.lift_fst _ _ _
  have hx' : x ≫ ((zeroU R I).gt e).pG.left = thick R I e :=
    (congrArg (x ≫ ·) (zeroGt_pG R I e)).trans (pullback.lift_fst _ _ _)
  obtain ⟨h₁, h₂⟩ := hs _ x r r (hr.trans hx.symm) (hr.trans hx'.symm) rfl z (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (fun _ => trivial) (fun _ => trivial)
  have w1 : gw ((zeroU R I).w e) x z PUnit.unit (fun _ => PUnit.unit) = 1 := map_one _
  have t1 : val (((zeroU R I).gt e).t PUnit.unit) x z (fun _ => PUnit.unit) = 1 :=
    (congrArg _ (gv_one _)).trans (map_one _)
  have va := sval_const ha r z (fun _ => PUnit.unit)
  have vb := sval_const hb r z (fun _ => PUnit.unit)
  erw [hr] at va vb
  refine va.symm.trans (Eq.trans ?_ vb)
  erw [w1, Units.val_one, one_pow, _root_.one_mul] at h₂
  refine h₂.trans ((Finset.sum_eq_single PUnit.unit (fun _ _ hb => absurd rfl hb) fun hn => ?_).trans ?_)
  · erw [h₁ _ hn, zero_mul]
  · exact (congrArg (_ * Units.val ·) t1).trans (_root_.mul_one _)
end GlobalTheory.UU.RelModel
