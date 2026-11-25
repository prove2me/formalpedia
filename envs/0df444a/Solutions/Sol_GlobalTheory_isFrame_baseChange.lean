-- Prove2me | solution 1 for GlobalTheory.isFrame_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:12.492916+00:00
-- url     : https://prove2.me/submissions/23259ca9-2426-4a10-969d-74752e6fa49c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsFrameRawChartBaseChange
import Theorems.Thm_GlobalTheory_FrameBaseChange_gm_unit_map
import Theorems.Thm_GlobalTheory_FrameBaseChange_val_scale
import Theorems.Thm_GlobalTheory_FrameBaseChange_psIn_map
import Theorems.Thm_GlobalTheory_FrameBaseChange_point_bc
import Theorems.Thm_GlobalTheory_FrameBaseChange_val_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetBC_psJet


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open FrameBaseChange
open MvPolynomial (X C)
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S), RIsFrame x0 d x F act ph1 ph2 sy ad e → RIsFrame (spMap ψ ≫ x0) d x' (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => MvPowerSeries.map ψ (ad a)) e' := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx e e' he he' hc ph1 ph2 sy ad hF
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  refine ⟨he', ?_, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.ph1 m
    refine ⟨Units.map (jetBC ψ (Fin 3 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 3 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 3))
          (lift (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 3)) (rjpt (spMap ψ ≫ x0) d x' m (2 : Fin 3))) =
          rjBC ψ x0 d m 3 ≫ lift (rjpt x0 d x m (0 : Fin 3)) (lift (rjpt x0 d x m (1 : Fin 3)) (rjpt x0 d x m (2 : Fin 3))) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      refine (val_pull hJ _ _ _).trans ?_
      rw [hlift, Over.comp_left, ← Category.assoc]
      refine Eq.trans (val_pull hJ _ _ _).symm ((val_corr hJ hcr _).trans ((val_scale hJ _ _ _).trans ?_))
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [gm_unit_map]
        rfl
      · simp only [val_mul hJ, val_inv]
        refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) (congrArg Inv.inv ?_) (congrArg Inv.inv ?_)) <;>
          exact (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.ph2 m
    refine ⟨Units.map (jetBC ψ (Fin 3 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 3 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 3))
          (lift (rjpt (spMap ψ ≫ x0) d x' m (2 : Fin 3)) (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 3))) =
          rjBC ψ x0 d m 3 ≫ lift (rjpt x0 d x m (1 : Fin 3)) (lift (rjpt x0 d x m (2 : Fin 3)) (rjpt x0 d x m (0 : Fin 3))) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      refine (val_pull hJ _ _ _).trans ?_
      rw [hlift, Over.comp_left, ← Category.assoc]
      refine Eq.trans (val_pull hJ _ _ _).symm ((val_corr hJ hcr _).trans ((val_scale hJ _ _ _).trans ?_))
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [gm_unit_map]
        rfl
      · simp only [val_mul hJ, val_inv]
        refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) (congrArg Inv.inv ?_) (congrArg Inv.inv ?_)) <;>
          exact (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.sy m
    refine ⟨Units.map (jetBC ψ (Fin 2 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 2 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      refine ((val_corr hJ (hc m) _).trans (val_pull hJ _ _ _)).trans ?_
      refine ((val_corr hJ hcr _).trans (val_scale hJ _ _ _)).trans ?_
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [← map_inv, gm_unit_map]
        rfl
      · refine (val_subst (hc m) hJ _ _ ?_ _).symm
        intro i j
        fin_cases i <;> simp
  · intro a
    obtain ⟨wL, hwL, hm⟩ := hF.ad a
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hcr⟩ := hm m
    refine ⟨Units.map (jetBC ψ (Fin 2 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 2 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2)) (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2)) =
          rjBC ψ x0 d m 2 ≫ lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2)) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      have h3 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ hcr (𝟙 _ ≫ (rjBC ψ x0 d m 2).left)).trans (val_scale hJ _ _ _))
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (h3.trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)))
      · refine congrArg₂ (· * ·) ?_ (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _)
        refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
        show val wL (𝟙 _ ≫ (lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2)) (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2))).left) y J =
          val wL ((𝟙 _ ≫ (rjBC ψ x0 d m 2).left) ≫ (lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2))).left) y J
        rw [hlift, Over.comp_left, Category.assoc]
      · refine congrArg₂ (· * ·) ?_ (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
        rw [gm_unit_map]
        rfl
end GlobalTheory
