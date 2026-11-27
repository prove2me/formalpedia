-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.acts_zeroU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:48.944683+00:00
-- url     : https://prove2.me/submissions/128c9fa5-95b4-41b6-94f0-465c06cdfc4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_RelModel_expF_zeroU
import Theorems.Thm_GlobalTheory_UnifZero_exists_secConst
import Theorems.Thm_GlobalTheory_UnifZero_resTop_inj
import Theorems.Thm_GlobalTheory_UnifZero_resTop_mul
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
import Theorems.Thm_GlobalTheory_UnifZero_scal_mul
import Theorems.Thm_GlobalTheory_UnifZero_scal_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_InhTate_map_map


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
theorem _root_.solution [IsHausdorff I R] (g : GtPtF (zeroData R I).toPre F) : (zeroU R I).Acts F k PUnit.unit g 1 := by
  refine ⟨one_pow k, fun θ _ => ?_⟩
  let pA : (TFK (R := R) F ⊗ (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))).A).left ⟶ Spec (CommRingCat.of F) :=
    (fst (TFK (R := R) F) (𝟙_ _)).left
  let pB : (DegPre.BF (zeroData R I).toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) (𝟙_ _)).left
  have iA : IsIso pA := (inferInstance : IsIso (pullback.fst (TFK (R := R) F).hom (𝟙 _)))
  have iB : IsIso pB := (inferInstance : IsIso (pullback.fst (TF (R := R) F).hom (𝟙 _)))
  have hf : (DegPre.zF (zeroData R I).toPre F).left ≫ pB = 𝟙 _ :=
    congrArg Over.Hom.left (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[(zeroData R I).toPre.P.A]))
  have hz : IsIso (DegPre.zF (zeroData R I).toPre F).left := IsIso.of_isIso_fac_right hf
  have tB : DegPre.trPt (zeroData R I).toPre F g.b = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)
  have tA : translT _ θ.pt = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)
  obtain ⟨v, hv⟩ := exists_isConst θ.φ
  obtain ⟨a, ha⟩ := (scal_bijective pA).2 v.val
  have a0 : a ≠ 0 := by
    rintro rfl
    have : (1 : F) = 0 := (scal_bijective pA).1 (by
      have : scal pA (1 : F) = 1 := by simp only [scal, map_one]
      rw [this, ← v.mul_inv, ← ha, scal_zero, zero_mul])
    exact one_ne_zero this
  obtain ⟨ga, hga⟩ := exists_isConst (g.s PUnit.unit)
  have ga1 : ga = 1 := eq_of_corr hga (isConst_oneGen _) g.s_zero
  refine ⟨cg _ _ (unitOn (Units.mk0 a a0)), cg_isGen _ _ _, fun t t' s s' e e' act α u _ hu => ?_⟩
  obtain ⟨x₀, hx⟩ := exists_secConst t
  obtain ⟨x, rfl⟩ := (scal_bijective pA).2 x₀
  obtain ⟨x₀', hx'⟩ := exists_secConst t'
  obtain ⟨x', rfl⟩ := (scal_bijective pA).2 x₀'
  obtain ⟨y₀, hy⟩ := exists_secConst (s PUnit.unit)
  obtain ⟨y, rfl⟩ := (scal_bijective pB).2 y₀
  obtain ⟨y₀', hy'⟩ := exists_secConst (s' PUnit.unit)
  obtain ⟨y', rfl⟩ := (scal_bijective pB).2 y₀'
  obtain rfl := expF_zeroU R I F k e hx hy
  obtain rfl := expF_zeroU R I F k e' hx' hy'
  have xx : x' = a * x := by
    have := act (fun _ => PUnit.unit)
    erw [hx, hx', hv, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, tA] at this
    refine (scal_bijective pA).1 (resTop_inj (wchart_triv _ _) (this.trans ?_))
    rw [scal_mul, resTop_mul, ha]
    rfl
  obtain ⟨b, hb⟩ := exists_isConst u
  have bb : b = pullTop pB (unitOn (Units.mk0 a a0)) := pullTop_injective (DegPre.zF (zeroData R I).toPre F).left (by
    refine (eq_of_corr (isConst_pullGen hb _) (isConst_mulGen (hga.of_eq ga1) (cg_isConst _ _ _)) hu).trans ?_
    rw [_root_.one_mul]
    ext
    exact (congrArg (fun f => f.appTop.hom (unitOn (Units.mk0 a a0)).val) hf).symm)
  intro j₁ j₂ j₃ _
  erw [hy, hy', hb, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, tB, xx, bb, scal_mul, resTop_mul, mul_comm]
  refine congrArg₂ (· * ·) rfl ?_
  exact (map_map _ _ _).symm
end GlobalTheory.UU.RelModel
