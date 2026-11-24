-- Prove2me | solution 1 for GlobalTheory.FormalCalc.constantCoeff_formalExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:16.206828+00:00
-- url     : https://prove2.me/submissions/693142ef-bc5c-4bfb-911f-af22a1049c0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_subst_of_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    constantCoeff (formalExp f) = 1 := by
  have h := constantCoeff_subst_of_zero (σ := Unit) (a := fun _ => f)
    (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (fun _ => hf) (PowerSeries.exp A)
  rw [formalExp, PowerSeries.subst, h, ← PowerSeries.constantCoeff_eq]
  simp
end GlobalTheory.FormalCalc
