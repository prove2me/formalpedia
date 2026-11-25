-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.fe_zeroUq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:22:48.046711+00:00
-- url     : https://prove2.me/submissions/e2b76a9e-9d9e-4523-9a19-6dc663e86e02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_RelModel_sval_cs_one
import Theorems.Thm_GlobalTheory_UU_RelModel_expF_one
import Theorems.Thm_GlobalTheory_ToricData_pullTop_unitOn
import Theorems.Thm_GlobalTheory_ToricData_unitOn_pow
import Theorems.Thm_GlobalTheory_UnifZero_exists_secConst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_InhTate_isConst_powGen


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
theorem _root_.solution (q : (FractionRing R)ˣ) : (zeroUq R I q).FE F (k + 1) ↔ q ^ k = 1 := by
  have hf : (DegPre.zF (toricPre R PUnit fun _ => q) F).left ≫
      (fst (TF (R := R) F) (toricPre R PUnit fun _ => q).P.A).left = 𝟙 _ :=
    congrArg Over.Hom.left (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[(toricPre R PUnit fun _ => q).P.A]))
  have hi : IsIso (fst (TF (R := R) F) (toricPre R PUnit fun _ => q).P.A).left :=
    (inferInstance : IsIso (pullback.fst (TF (R := R) F).hom (𝟙 _)))
  have hz : IsIso (DegPre.zF (toricPre R PUnit fun _ => q) F).left := IsIso.of_isIso_fac_right hf
  have ht : ∀ mu, DegPre.trF (toricPre R PUnit fun _ => q) F mu = 𝟙 _ := fun mu =>
    CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)
  have hm : ∀ mu α, IsConst (DegPre.famMult (toricPre R PUnit fun _ => q) F (k + 1) mu α)
      (pullTop (jFK (R := R) F) (unitOn (q ^ k))) := fun mu α =>
    (isConst_pullGen (isConst_mulGen (isConst_mulGen (isConst_powGen (psi_isConst _ mu) (k + 1))
      (tau_isConst _ mu α)) (isConst_powGen (rigK_isConst _) (k + 1))) _).of_eq (by
        congr 1
        rw [one_pow, _root_.mul_one, ← unitOn_pow, ← unitOn_mul]
        congr 1
        show q ^ (k + 1) * (q * q⁻¹ * q⁻¹) = _
        group)
  constructor
  · intro h
    let v := pullTop (fst (TF (R := R) F) (toricPre R PUnit fun _ => q).P.A).left (pullTop (jFK (R := R) F) (unitOn (q ^ k)))
    have hv : pullTop (DegPre.zF (toricPre R PUnit fun _ => q) F).left v = pullTop (jFK (R := R) F) (unitOn (q ^ k)) := by
      ext
      exact congrArg (fun f => f.appTop.hom (pullTop (jFK (R := R) F) (unitOn (q ^ k))).val) hf
    have H := h _ _ (expF_one R I F (k + 1)) PUnit.unit PUnit.unit (cg _ _ v) (cg_isGen _ _ _)
      (corr_of_isConst ((isConst_pullGen (cg_isConst _ _ v) _).of_eq hv) (hm _ _))
    have v1 : v = 1 := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt (toricPre R PUnit fun _ => q).P.isLB z
      have e := (secRel_iff (toricPre R PUnit fun _ => q).P.isLB _ _ _ _ _ _ _ _ _ _).1 H _ (𝟙 _) z J hJ
      erw [sval_cs_one, sval_cs_one, _root_.one_mul] at e
      rw [map_one]
      exact (gm_res _ z _ (hJ.mem _ _) v).symm.trans (Units.ext e.symm)
    rw [v1, map_one, pullTop_unitOn, ← unitOn_one, unitOn_inj] at hv
    exact Units.map_injective (algebraMap (FractionRing R) F).injective (hv.symm.trans (map_one _).symm)
  · intro h t s _ mu α u _ hu
    obtain ⟨v, hv⟩ := exists_isConst u
    obtain ⟨c, hc⟩ := exists_secConst (s α)
    have hv1 : v = 1 := pullTop_injective (DegPre.zF (toricPre R PUnit fun _ => q) F).left
      ((eq_of_corr (isConst_pullGen hv _) (hm mu α) hu).trans (by rw [h, unitOn_one, map_one, map_one]))
    refine secRel_of hc hc _ (hv.of_eq hv1) ?_
    rw [ht, Over.id_left, Scheme.Hom.id_appTop]
    rfl
end GlobalTheory.UU.RelModel
