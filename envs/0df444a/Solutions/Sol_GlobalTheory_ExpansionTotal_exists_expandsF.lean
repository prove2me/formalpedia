-- Prove2me | solution 1 for GlobalTheory.ExpansionTotal.exists_expandsF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:29.663037+00:00
-- url     : https://prove2.me/submissions/b624a902-0523-4ff8-86e1-637297737987

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal
import Theorems.Thm_GlobalTheory_ExpansionTotal_toBK_prB
import Theorems.Thm_GlobalTheory_ExpansionTotal_exists_famPull
import Theorems.Thm_GlobalTheory_ExpansionTotal_secLin_of_secScal
import Theorems.Thm_GlobalTheory_ExpansionTotal_sval_fam_sum
import Theorems.Thm_GlobalTheory_ExpansionTotal_exists_toFrac
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_exists_sum
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_move
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_pullOver
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_iff
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_sum__11871ebd81a9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)
namespace GlobalTheory.ExpansionTotal
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (hk : 1 ≤ k) (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  have e₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  obtain ⟨σ', hσ'⟩ := exists_move A.isLB U.LG.isLB hw
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k : ℤ) (U.genF F).left e₁
    (g₂ := UnifPre.gFK (G := G) F) rfl t
  have H : IsPullback (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
      (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (pullback.snd G.hom (jK R))
      (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))) :=
    (IsPullback.of_hasPullback _ _).flip
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := by
    have := A.isAb.proper
    have : IsIso U.gen.hom.left := ((Over.forget _).mapIso U.gen).isIso_hom
    have : IsLocallyNoetherian ((Over.pullback (jK R)).obj G).left :=
      LocallyOfFiniteType.isLocallyNoetherian (U.gen.hom.left ≫ A.A.hom)
    have : CompactSpace ((Over.pullback (jK R)).obj G).left :=
      QuasiCompact.compactSpace_of_compactSpace (U.gen.hom.left ≫ A.A.hom)
    have : IsNoetherian ((Over.pullback (jK R)).obj G).left := {}
    infer_instance
  obtain ⟨n, c, v, hv⟩ := (isExtension_pullOver H U.LG.isLB (I := Fin 1)
    (φ := fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))
    (φ' := fun _ => UnifPre.gFK (G := G) F) (fun _ => rfl)).exists_sum σ'
  choose S hS using fun i => ((U.expand k hk).1 (v i)).exists
  choose r hr σ f hσ hf he using hS
  obtain ⟨θ, hθ⟩ := exists_toFrac (R := R) F
  choose S' hS' using fun i => exists_famPull θ D.toPre hθ k (S i)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hg : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom g) := (Spec.map_comp _ _).symm
  have hd : ∀ i, c i * (g (r i))⁻¹ * g (r i) = c i := fun i => inv_mul_cancel_right₀
    ((map_ne_zero_iff g ((algebraMap (FractionRing R) F).injective.comp
      (IsFractionRing.injective R (FractionRing R)))).2 (hr i)) _
  refine ⟨∑ i, c i • S' i, σ', (isoRelM_iff w _ k _ e₁ _ (Category.id_comp _) t σ').2 fun y i₂ i₁ a₂ a₁ => ?_,
    n, fun i => c i * (g (r i))⁻¹, σ, f, he, ?_, fun α => ?_⟩
  · rw [Category.comp_id]
    exact hσ' _ (𝟙 _) y i₂ i₁ a₂ a₁
  · refine secLin_of_secScal U.LG.isLB (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left rfl g
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) H.w).trans
        ((Category.assoc _ _ _).trans (congrArg _ hg)))) hd hσ fun y J hJ => ?_
    refine (congrArg (fun x => sval x _ y J) hv).trans ((sval_sum' hJ _ _ _).trans
      (Finset.sum_congr rfl fun i _ => (sval_smul' hJ _ _ _).trans (congrArg _ ?_)))
    exact sval_pullOver H.w (fun _ => rfl) (v i) _ hJ
  · refine secLin_of_secScal D.toPre.P.isLB (toBK θ D.toPre).left
      (congrArg (fun q => q.left) (toBK_prB θ D.toPre)).symm g
      ((Over.w _).trans ((Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm.trans (congrArg _ hg))) hd
      (fun i => hf i α) fun y J hJ => ?_
    refine (sval_fam_sum D.toPre c S' α _ y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
    exact hS' i α _ _ y J hJ
end GlobalTheory.ExpansionTotal
