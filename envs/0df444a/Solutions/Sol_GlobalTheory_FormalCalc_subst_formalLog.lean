-- Prove2me | solution 1 for GlobalTheory.FormalCalc.subst_formalLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:25.355194+00:00
-- url     : https://prove2.me/submissions/b602e721-472c-4e1f-8922-f0a3b6e9ed43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
omit [Algebra ℚ A] in
private theorem hasSubst_sub_one {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    PowerSeries.HasSubst (g - 1) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hg])
end GlobalTheory.FormalCalc
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    subst a (formalLog g) = formalLog (subst a g) := by
  rw [formalLog, formalLog, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (hasSubst_sub_one hg).const ha, subst_sub ha, subst_one' ha]
end GlobalTheory.FormalCalc
