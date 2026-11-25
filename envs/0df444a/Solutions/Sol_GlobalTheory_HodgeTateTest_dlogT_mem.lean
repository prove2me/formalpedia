-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.dlogT_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:12.272802+00:00
-- url     : https://prove2.me/submissions/ae0743cd-e397-40c9-a1e7-cdd16fc562e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_HodgeTateTest_fst_eq
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_mul
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_ptMap
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]
namespace GlobalTheory.HodgeTateTest
theorem _root_.solution : dlogT ∈ omega (GmO O) := by
  refine ⟨fun x y h => ?_, fun a x h => ?_⟩
  · show (unitOf (x.1 * y.1) : DualNumber O).snd = _
    rw [unitOf_mul, Units.val_mul, DualNumber.snd_mul, fst_eq, fst_eq, dlogT, dlogT]
    ring
  · show (unitOf (ptMap (dualScale a) ≫ x.1) : DualNumber O).snd = _
    rw [unitOf_ptMap]
    simp [dualScale, dlogT]
end GlobalTheory.HodgeTateTest
