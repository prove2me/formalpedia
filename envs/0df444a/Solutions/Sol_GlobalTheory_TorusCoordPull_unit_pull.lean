-- Prove2me | solution 1 for GlobalTheory.TorusCoordPull.unit_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:35:40.916904+00:00
-- url     : https://prove2.me/submissions/7187712c-da28-4453-923e-a46583bc1d3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
import Theorems.Thm_P2M_GlobalTheory_TorusCoordPull_exists_good__38f148e1dff0
import Theorems.Thm_GlobalTheory_TorusCoordPull_val_unit_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusCoordPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {S S' : Scheme.{0}} {j : S ⟶ Spec (CommRingCat.of R)}
  {j' : S' ⟶ Spec (CommRingCat.of R')} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
  [IsCommMonObj G'] (p : (Over.map j).obj G ⟶ D.P.A) (p' : (Over.map j').obj G' ⟶ D'.P.A) (h : G'.left ⟶ G.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
  {σ : S' ⟶ S} (gp : IsGrpPullback G' G σ h) {χ : D'.X}
  {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe χ)) Oinvε)} {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε)}
  (H : PMaps hD.w (D'.Oφ p' χ) (D.Oφ p (hD.xe χ)) Oinvε a t h)
include hp gp H
namespace GlobalTheory.TorusCoordPull
theorem _root_.solution (e₂ : (Over.map j').map η[G'] ≫ p' = 1)
    (hu : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec G)) (LB.oneGen D.P.L)) :
    LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (eSec G')) (LB.oneGen D'.P.L) := by
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
  have e₁ : eSec G' ≫ h = σ ≫ eSec G := (cubeMapOf gp).e_comm
  have e₄ : val t (σ ≫ eSec G) y J = 1 :=
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ hu σ).trans (val_one _))
  have e₃ := val_unit_pull hD p p' h hp H ((Over.map j').map η[G']) e₂ (y := y) hJ hJ'
  have e₅ : val a (eSec G') y J' = 1 :=
    e₃.symm.trans ((congrArg (fun r => val t r y J) e₁).trans e₄)
  exact (val_pull hJ' _ _ _).trans ((congrArg (fun r => val a r y J') (Category.id_comp _)).trans
    (e₅.trans (val_one _).symm))
end GlobalTheory.TorusCoordPull
