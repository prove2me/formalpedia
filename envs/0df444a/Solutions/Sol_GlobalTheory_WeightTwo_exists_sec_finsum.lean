-- Prove2me | solution 1 for GlobalTheory.WeightTwo.exists_sec_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:36.876346+00:00
-- url     : https://prove2.me/submissions/5ed0ce3a-947c-4b9f-8eee-7e56459c06df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecFinsum
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


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
open GlobalTheory GlobalTheory.WeightTwo
namespace GlobalTheory.WeightTwo
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {I : Type} (s : Finset I) (d : I → LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval t r z J = ∑ i ∈ s, sval (d i) r z J := by
  refine ⟨⟨fun j => ∑ i ∈ s, (d i).f j, fun j j' => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (d i).compat j j'
  · exact DVR.gs_fsum r z _ (hJ.mem φ r) _ _
end GlobalTheory.WeightTwo
