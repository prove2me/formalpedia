-- Prove2me | solution 1 for GlobalTheory.rawChart_baseChange_rig_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:04.392595+00:00
-- url     : https://prove2.me/submissions/0534e011-f6d3-4ef0-94e9-49a56b995d58

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RawChartBaseChangeRigGerm
import Theorems.Thm_P2M_GlobalTheory_RawChartGermBC_appTop_to__spMap_21b8af0e1797
import Theorems.Thm_GlobalTheory_RawChartGermBC_isPullSec_whisker_comp
import Theorems.Thm_GlobalTheory_RawChartGermBC_aug_rjBC
import Theorems.Thm_GlobalTheory_RawChartGermBC_base_rjBC
import Theorems.Thm_GlobalTheory_RawChartGermBC_overAt_hom_bc
import Theorems.Thm_GlobalTheory_RawChartGermBC_val_genPow
import Theorems.Thm_GlobalTheory_RawChartGermBC_val_reL_bc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_rigT
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_exists_pullSec
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isPullSec_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isPullSec_unique
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_isValueAt_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open RawChartGermBC
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (wP : PrimTy H Xo), wP.IsGen → (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP 0) (homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) 0 →ₐ[S'] S')).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap ψ ≫ x0) S') 1)) ∧ ∀ (k : ℕ) (Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (Fs' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap ψ ≫ x0)))) (f : MvPowerSeries (Fin 1 × Fin d) S), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC ψ x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs Fs' → RIsGerm x0 d x act e wP k Fs f → RIsGerm (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP k Fs' (MvPowerSeries.map ψ f) := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d _ act x x' hx e e' hge hge' he wP hwP
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx
  refine ⟨fun hrig => ?_, fun k Fs Fs' f hpull hgerm => ?_⟩
  · refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP 0 _ y hJ).trans ?_
    rw [Category.assoc, aug_rjBC ψ x0 d 0 1, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ?_
    refine (val_corr hJ hrig _).trans ?_
    rw [GermB.val_rigT _ _ _ _ _ _ _ hJ, GermB.val_rigT _ _ _ _ _ _ _ hJ, overAt_hom_bc ψ x0]
    simp only [Category.id_comp]
  · intro m
    obtain ⟨F0, τ0, hF0, hτ0, hv0⟩ := hgerm m
    obtain ⟨F1, hF1⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBase (spMap ψ ≫ x0) d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs'
    obtain ⟨F2, hF2⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBC ψ x0 d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F0
    have hA := isPullSec_whisker_comp _ _ (k : ℤ) (rjBase x0 d m 1) (rjBC ψ x0 d m 1) hF0 hF2
    have hB := isPullSec_whisker_comp _ _ (k : ℤ) (ptBC ψ x0) (rjBase (spMap ψ ≫ x0) d m 1) hpull hF1
    have hB' := (LBPull.isPullSec_congr Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (congrArg (· ▷ Xo.univ.t.G) (base_rjBC ψ x0 d m 1)) _ (whiskerRight_snd _ _) Fs F1).1 hB
    have h12 : F1 = F2 := LBPull.isPullSec_unique _ _ _ hB' hA
    subst h12
    have hv := LBPull.isValueAt_pull Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (rjBC ψ x0 d m 1) (x m) hF2 hv0
    have hvb : (rjBC ψ x0 d m 1).left.appTop.hom (toΓ _ (psJet m f)) =
        toΓ _ (psJet m (MvPowerSeries.map ψ f)) := by
      rw [← PullbackSections.jetBC_psJet]
      exact appTop_toΓ_spMap (jetBC ψ (Fin 1 × Fin d) m) (psJet m f)
    rw [hvb] at hv
    refine ⟨F1, LB.pullGen Xo.univ.t.PP.L _ _ τ0 (rjBC ψ x0 d m 1).left, hF1, ?_, hv⟩
    refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_corr hJ hτ0 _).trans ?_
    rw [val_genPow, val_genPow, val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP m _ y hJ]
end GlobalTheory
