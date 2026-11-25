-- Prove2me | solution 1 for GlobalTheory.ConvOfProd.exists_sub_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:01:02.708163+00:00
-- url     : https://prove2.me/submissions/7d9d8bbb-947f-4e36-a2f5-00b2e22264ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSubSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add


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
open GlobalTheory.UU
open GlobalTheory GlobalTheory.ConvOfProd
namespace GlobalTheory.ConvOfProd
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Ix : Type}
    (S : LB.Sec (LB.LinComb L φ ε)) (p : Ix → LB.Sec (LB.LinComb L φ ε)) (s : Finset Ix) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval S r z J - ∑ i ∈ s, sval (p i) r z J := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, fun Z r z J _ => by rw [Finset.sum_empty, sub_zero]⟩
  | insert i s hi ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i)), fun Z r z J hJ => ?_⟩
    have hm := hJ.mem φ r
    have e : sval (DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i))) r z J = sval d r z J - sval (p i) r z J := by
      refine (gs_add r z _ hm _ _).trans ?_
      rw [sub_eq_add_neg]
      congr 1
      refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (congrArg Neg.neg (gs_eq r z _ hm _)).symm)
      exact (congrArg _ (map_neg _ _)).trans (map_neg _ _)
    rw [e, hd Z r z J hJ, Finset.sum_insert hi]
    ring
end GlobalTheory.ConvOfProd
