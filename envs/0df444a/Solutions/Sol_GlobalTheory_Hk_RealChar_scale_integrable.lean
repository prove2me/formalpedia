-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.scale_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:38.84404+00:00
-- url     : https://prove2.me/submissions/8adbc1d1-a327-4fbe-a195-901039ec0e9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_integrableOn_kerW
import Theorems.Thm_GlobalTheory_Hk_RealChar_scale_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {y n : ℝ} (hy : 0 < y) (hn : 0 < n) :
    IntegrableOn (fun w => Real.exp (-(y / w)) * Real.exp (-(w * n)) / w) (Set.Ioi 0) := by
  have h : IntegrableOn (fun w => kerW (y * n) (w * n)) (Set.Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_right_iff (kerW (y * n)) 0 hn, zero_mul]
    exact integrableOn_kerW (by positivity)
  exact IntegrableOn.congr_fun (h.const_mul n) (fun w hw => (scale_eq y hn hw).symm) measurableSet_Ioi
end GlobalTheory.Hk.RealChar
