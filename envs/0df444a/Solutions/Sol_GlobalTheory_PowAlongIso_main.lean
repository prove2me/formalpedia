-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:17.365815+00:00
-- url     : https://prove2.me/submissions/4d0492e5-cb17-436c-adcd-102f5f6a113e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_GlobalTheory_PowAlongIso_exists_box_comp
import Theorems.Thm_GlobalTheory_PowAlongIso_box_maps_pull
import Theorems.Thm_GlobalTheory_PowAlongIso_exists_mapsAt
import Theorems.Thm_GlobalTheory_PowAlongIso_sq_pull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.PowAlongIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)
namespace GlobalTheory.PowAlongIso
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (U : Unif I D A G) (U' : Unif I D A G'), IsMonHom ε.hom → SameUnif ε U.toUnifPre U'.toUnifPre → ∀ (j : ℕ) (D₀ : DegData R I) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif I D₀ A₀ G₀) (pD : IsPowDeg D.toPre D₀.toPre j) (pA : IsPowPolAV A A₀ j) (pG : IsPowGrp G G₀ j) (pG' : IsPowGrp G' G₀ j), (∀ i, ε.hom ≫ pG.pr i = pG'.pr i) → Nonempty (UnifPowOf3 pD pA pG U U₀) → Nonempty (UnifPowOf3 pD pA pG' U' U₀) := by
  intro R _ _ I D A G G' _ _ _ _ ε U U' hε ⟨hgen, v, ⟨hv, hvr⟩, hS⟩ j D₀ A₀ G₀ _ _ U₀ pD pA pG pG' hpr ⟨P⟩
  have hpr' : ∀ i, (pG'.pr i).left = ε.hom.left ≫ (pG.pr i).left := fun i => congrArg (fun q => q.left) (hpr i).symm
  obtain ⟨wL, wL_gen, hT⟩ := exists_box_comp U₀.LG.isLB U.LG.isLB U'.LG.isLB hpr' P.wL P.wL_gen v hv
  have he : eSec G' ≫ ε.hom.left = eSec G := congrArg (fun q => q.left) (IsMonHom.one_hom ε.hom)
  have hρ : ∀ e i, ((Over.pullback (thick R I e)).map (pG'.pr i)).left =
      ((Over.pullback (thick R I e)).map ε.hom).left ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left :=
    fun e i => by rw [← hpr, Functor.map_comp, Over.comp_left]
  have hp : ∀ e, (U'.gt e).pG =
      (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map ε.hom) ≫ (U.gt e).pG := fun e => by
    rw [GtCoord.pG, (hS e).1, Functor.map_comp, Category.assoc]
  have hO : ∀ e x k, D.toPre.Oφ (U'.gt e).pG x k =
      ((Over.pullback (thick R I e)).map ε.hom).left ≫ D.toPre.Oφ (U.gt e).pG x k := fun e x k => by
    rw [hp]
    exact (WeightPf.Oφ_comp ((Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map ε.hom)) (U.gt e).pG x k).symm
  refine ⟨⟨⟨⟨fun i => ?_, wL, wL_gen, exists_mapsAt U.LG.isLB hpr' hT he hvr _ P.wL_rig, fun e i => ?_⟩,
    fun e x => ?_⟩, fun e => ?_⟩⟩
  · rw [hgen, Category.assoc, P.gen_pr, ← hpr, Functor.map_comp, Category.assoc]
  · rw [(hS e).1, Category.assoc, P.q_pr, ← hpr, Functor.map_comp, Category.assoc]
  · obtain ⟨hψ, H⟩ := P.t_pr e x
    refine ⟨fun i k => ?_, box_maps_pull (Y := (thickObj R I e G).left) (Y' := (thickObj R I e G').left)
      (Y₀ := (thickObj R I e G₀).left) D.toPre.P.isLB pD.w (hO e x) (hρ e) hψ _ ((U.gt e).t_gen x)
      ((U'.gt e).t_gen x) ((hS e).2.1 x) _ H⟩
    exact (congrArg (· ≫ (pD.pw.pr i).left) (hO e x k)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (hψ i k)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hρ e i).symm))))
  · exact sq_pull (T := (thickObj R I e G₀).left) (T' := (thickObj R I e G).left) (T'' := (thickObj R I e G').left)
      U.LG.isLB hpr' hT (congrArg (fun q => q.left) (hp e)) (pullback.lift_fst _ _ _) (hρ e) (hS e).2.2 (P.w_pr e)
end GlobalTheory.PowAlongIso
