-- Prove2me | solution 1 for GlobalTheory.UU.SecMod.sval_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:03.698666+00:00
-- url     : https://prove2.me/submissions/0ca2fd9b-ba06-489f-aa8a-93533dbb6a56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
import Theorems.Thm_GlobalTheory_UU_SecMod_sval_add
import Theorems.Thm_GlobalTheory_UU_SecMod_sval_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sval_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.UU
open GlobalTheory.UU.SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ
namespace GlobalTheory.UU.SecMod
theorem _root_.solution {I : Type*} (S : Finset I) (s : I → SecMod p (LB.LinComb L φ ε)) :
    sval (∑ i ∈ S, s i).sec r z J = ∑ i ∈ S, sval (s i).sec r z J := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, sval_zero hJ]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sval_add hJ, ih]
end GlobalTheory.UU.SecMod
