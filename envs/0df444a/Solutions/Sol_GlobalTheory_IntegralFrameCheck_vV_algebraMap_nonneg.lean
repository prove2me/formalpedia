-- Prove2me | solution 1 for GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:44.465967+00:00
-- url     : https://prove2.me/submissions/6d01525d-caee-414f-b38e-583cf4e1f2a5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
import Theorems.Thm_Formalism_L2_Pj_valV_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
namespace GlobalTheory.IntegralFrameCheck
theorem _root_.solution (a : V) : 0 ≤ vV V (algebraMap V K' a) := by
  by_cases ha : algebraMap V K' a = 0
  · rw [ha]; simp [vV]
  · have hv : valV V (algebraMap V K' a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
    have := (WithZero.log_le_log (valV_ne_zero (V := V) ha) one_ne_zero).2 hv
    simp only [WithZero.log_one] at this
    simp only [vV]; omega
end GlobalTheory.IntegralFrameCheck
