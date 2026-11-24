-- Prove2me | solution 1 for GlobalTheory.WeightVal.val_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:39.500796+00:00
-- url     : https://prove2.me/submissions/2ff15659-d5c7-472d-94da-858cdf88c498

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.WeightVal
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace GlobalTheory.WeightVal
theorem _root_.solution (β : D.X) {W : Scheme.{0}} (ρ : W ⟶ (WeightPf.Te D I e ⊗ thickObj R I e G).left) (w : W) {J}
    (hJ : Good D.P.L w J) :
    (val (g.t β) (ρ ≫ (WeightPf.act g).left) w J).val =
      gs ρ w ⊤ (TorusInj.chiP D.X (thickObj R I e G) β) *
        (val (g.t β) (ρ ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left) w J).val := by
  have E := val_corr hJ (g.t_weight β) ρ
  rw [val_mul hJ, val_pull hJ, val_pull hJ] at E
  refine (congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  have hm := hJ.mem (L := D.P.L) (K := PEmpty) (Y := (WeightPf.Te D I e ⊗ thickObj R I e G).left)
    PEmpty.elim ρ
  exact (congrArg Units.val ((gm_res ρ w _ hm _).trans
    (gm_pull ρ (fst (WeightPf.Te D I e) (thickObj R I e G)).left w ⊤ trivial (charUnit _ D.X β)))).trans
      ((gs_unit _ w ⊤ trivial _).symm.trans
      (gs_pull ρ (fst (WeightPf.Te D I e) (thickObj R I e G)).left w ⊤ trivial _).symm)
end GlobalTheory.WeightVal
