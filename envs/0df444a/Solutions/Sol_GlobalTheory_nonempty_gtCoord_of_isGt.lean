-- Prove2me | solution 1 for GlobalTheory.nonempty_gtCoord_of_isGt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:51:35.794202+00:00
-- url     : https://prove2.me/submissions/7c5b6a99-2e0d-498f-b6ea-89906337980a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_iso
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_exists_gen
import Theorems.Thm_GlobalTheory_WeightGen_wt_add
import Theorems.Thm_GlobalTheory_WeightGen_act_q
import Theorems.Thm_GlobalTheory_WeightGen_act_q_left
import Theorems.Thm_GlobalTheory_WeightGen_hasGen
import Theorems.Thm_GlobalTheory_WeightGen_exists_const
import Theorems.Thm_P2M_GlobalTheory_WeightGen_comp_O__ce33ccf541f8
import Theorems.Thm_GlobalTheory_WeightGen_exists_normalised
import Theorems.Thm_GlobalTheory_WeightGen_unit_fst
import Theorems.Thm_GlobalTheory_WeightGen_val_charGen
import Theorems.Thm_GlobalTheory_SplitTorus_charUnit_val
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_appTop_chi
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_comp
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open GlobalTheory
open WeightGen
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : E.B ≅ thickObj R I e D.P.A) (xe : D.X ≃+ E.X), IsMonHom β.hom → (∀ χ : D.X, ∃ w : LB.Iso (E.O (xe χ)).L (LB.LinComb D.P.L (fun k => ((Over.map (thick R I e)).map β.hom ≫ D.prBe I e).left ≫ D.Oφ (𝟙 _) χ k) Oε), w.IsGen) → E.IsGt (thickObj R I e G) → Nonempty (GtCoord I D e G) := by
  intro hG R _ _ I D e G _ _ E β xe hβ hw ⟨d⟩
  have hL := D.P.isLB
  have := d.q_hom
  have := d.i_hom
  have := d.q_flat
  have := d.q_surjective
  have := d.q_affine
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  let F := Over.map (thick R I e)
  let κ : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ≅ splitTorus _ E.X :=
    { hom := SplitTorus.torusMap _ xe.symm.toAddMonoidHom
      inv := SplitTorus.torusMap _ xe.toAddMonoidHom
      hom_inv_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]
        congr 1; ext; simp
      inv_hom_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]
        congr 1; ext; simp }
  have : IsMonHom κ.hom := SplitTorus.isMonHom_torusMap _
  have hκ : ∀ χ, pullU κ.hom.left ⊤ (charUnit _ E.X (xe χ)) = charUnit _ D.X χ := fun χ => by
    apply Units.ext
    rw [SplitTorus.charUnit_val]
    refine Eq.trans ?_ ((SplitTorus.torusMap_appTop_chi xe.symm.toAddMonoidHom (xe χ)).trans
      (congrArg _ (xe.symm_apply_apply χ)))
    rw [← SplitTorus.charUnit_val]
    rfl
  have unit_q : F.map η[thickObj R I e G] ≫ F.map (d.q ≫ β.hom) ≫ D.prBe I e = 1 := by
    rw [← F.map_comp_assoc, IsMonHom.one_hom]
    exact Over.OverMorphism.ext (unit_fst (thick R I e) D.P.A)
  obtain ⟨t, g, m, u, w⟩ := exists_normalised D (F.map (d.q ≫ β.hom) ≫ D.prBe I e)
    (F.map (toUnit _)) (F.map η[thickObj R I e G])
    (by rw [← F.map_comp, comp_toUnit, toUnit_unit, F.map_id]) unit_q
    (F.map (act d)) (F.map (snd _ _))
    (by rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Category.assoc (act d), act_q d,
      Category.assoc])
    (by rw [← F.map_comp, ← F.map_comp, comp_toUnit, comp_toUnit])
    (exists_const d hG) (fun χ => wt E.X (thickObj R I e G) (xe χ))
    (fun χ χ' Z r z => by rw [map_add]; exact wt_add _ _ _ _ Z r z)
    (fun χ => by
      obtain ⟨w, hw⟩ := hw χ
      refine ((hasGen d (xe χ)).iso (act_q_left d) (exists_chart (E.O (xe χ)).isLB) w hw).exists_gen
        (act_q_left d) _ _ (fun k => ?_) (fun k => by fin_cases k <;> rfl) hL
      have := comp_Oφ D (F.map (d.q ≫ β.hom) ≫ D.prBe I e) (𝟙 _) χ k
      rw [Category.comp_id] at this
      refine this.symm.trans ?_
      rw [F.map_comp, Category.assoc, Over.comp_left, Category.assoc]
      rfl)
  refine ⟨{ q := d.q ≫ β.hom
            q_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surj := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            i := κ.hom ≫ d.i
            i_hom := inferInstance
            isKernel := d.isKernel.of_iso κ.symm (Iso.refl _) (Iso.refl _) β (by simp)
              (toUnit_unique _ _) (by simp) (by simp)
            t := t
            t_gen := g
            t_mul := m
            t_unit := fun χ => corr_of_val hL fun y J hJ => ?_
            t_weight := fun χ => corr_of_val hL fun y J hJ => ?_ }⟩
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact u χ y J hJ
  · have k := w χ _ (κ.hom ▷ thickObj R I e G).left y J hJ
    have k₁ : κ.hom ▷ thickObj R I e G ≫ act d =
        lift (fst _ (thickObj R I e G) ≫ κ.hom ≫ d.i) (snd _ _) ≫ μ[thickObj R I e G] := by
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    have k₂ : κ.hom ▷ thickObj R I e G ≫ snd _ _ = snd _ _ := whiskerRight_snd _ _
    have k₃ : (κ.hom ▷ thickObj R I e G).left ≫ (fst _ _ : _ ⟶ splitTorus _ E.X).left =
        (fst _ (thickObj R I e G)).left ≫ κ.hom.left :=
      congrArg (fun g => g.left) (whiskerRight_fst κ.hom (thickObj R I e G))
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
      (congrArg _ (val_pull hJ _ _ _))).symm)
    rw [Category.id_comp, Category.id_comp]
    have l₁ : (κ.hom ▷ thickObj R I e G).left ≫ (F.map (act d)).left =
        (lift (fst _ (thickObj R I e G) ≫ κ.hom ≫ d.i) (snd _ _) ≫ μ[thickObj R I e G]).left :=
      congrArg (fun g => g.left) k₁
    have l₂ : (κ.hom ▷ thickObj R I e G).left ≫ (F.map (snd _ _)).left =
        (snd _ (thickObj R I e G)).left := congrArg (fun g => g.left) k₂
    have l₃ : wt E.X (thickObj R I e G) (xe χ) _ (κ.hom ▷ thickObj R I e G).left y =
        val (charGen D.X (thickObj R I e G) D.P.L χ) (𝟙 _) y J := by
      rw [val_charGen, Category.id_comp, ← hκ]
      refine Eq.trans ?_ (gm_pull (fst _ (thickObj R I e G)).left κ.hom.left y ⊤ trivial _).symm
      rw [← k₃]
      rfl
    exact (congrArg (fun g => val (t χ) g y J) l₁).symm.trans (k.trans
      (congrArg₂ (· * ·) l₃ (congrArg (fun g => val (t χ) g y J) l₂)))
end GlobalTheory
