-- Prove2me | solution 1 for GlobalTheory.ConvOfProd.sum_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:51.171362+00:00
-- url     : https://prove2.me/submissions/cae73e76-604a-49b1-b29a-0af62d1a8ef4

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
theorem _root_.solution {X A : Type} [AddCommGroup X] [CommRing A] (s s' S : Finset X) (F G : X → A)
    (hG : ∀ v ∉ s', G v = 0) (hS : ∀ β ∈ s, ∀ v ∈ s', β + v ∈ S) :
    ∑ α ∈ S, ∑ β ∈ s, F β * G (α - β) = (∑ β ∈ s, F β) * ∑ v ∈ s', G v := by
  classical
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_bij_ne_zero (fun v _ _ => β + v) (fun v h _ => hS β hβ v h)
    (fun a _ _ b _ _ e => add_left_cancel e) (fun α _ h => ?_) (fun v _ _ => by rw [add_sub_cancel_left])
  exact ⟨α - β, by by_contra hn; exact h (hG _ hn), h, add_sub_cancel β α⟩
end GlobalTheory.ConvOfProd
