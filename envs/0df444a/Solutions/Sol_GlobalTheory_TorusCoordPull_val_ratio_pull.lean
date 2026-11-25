-- Prove2me | solution 1 for GlobalTheory.TorusCoordPull.val_ratio_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:09.332377+00:00
-- url     : https://prove2.me/submissions/e4fe18ac-6963-4495-b19c-5aab9a670fb8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
import Theorems.Thm_GlobalTheory_TorusCoordPull_val_of_pmaps
import Theorems.Thm_P2M_GlobalTheory_TorusCoordPull_O__pull_be9eb376d61b
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a


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
  {D' : DegPre R'}
variable (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
include hp
namespace GlobalTheory.TorusCoordPull
theorem _root_.solution {x : D'.X} {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe x)) Oinvε)}
    {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' x) Oinvε)}
    (H : PMaps hD.w (D'.Oφ p' x) (D.Oφ p (hD.xe x)) Oinvε a t h) {T₀ : Over (Spec (CommRingCat.of R'))}
    (ρ ρ' : T₀ ⟶ T') (hρ : ρ ≫ p' = ρ' ≫ p') {y : T₀.left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (u : (T₀.left.presheaf.stalk y)ˣ) (hu : val t (ρ.left ≫ h) y J = u * val t (ρ'.left ≫ h) y J) :
    val a ρ.left y J' = u * val a ρ'.left y J' := by
  rw [val_of_pmaps (Oφ_pull hD p p' h hp x) H ρ.left hJ hJ',
    val_of_pmaps (Oφ_pull hD p p' h hp x) H ρ'.left hJ hJ'] at hu
  simp only [WeightPf.Oφ_comp, hρ] at hu
  rw [mul_left_comm] at hu
  exact mul_left_cancel hu
end GlobalTheory.TorusCoordPull
