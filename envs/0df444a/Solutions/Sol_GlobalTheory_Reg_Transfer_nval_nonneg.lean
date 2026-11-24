-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.nval_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:37.730298+00:00
-- url     : https://prove2.me/submissions/d80035d1-5954-4a7d-818e-74faeea814be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_vV_nonneg
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne
import Theorems.Thm_Formalism_L2_Pj_nval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution (e : ℕ) (w : V) : 0 ≤ nval V e (algebraMap V (FractionRing V) w) := by
  by_cases hw : w = 0
  · rw [hw, map_zero, nval_zero]
    exact le_top
  · have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
      intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
    rw [nval_of_ne hw']
    exact EReal.coe_nonneg.2 (div_nonneg (by exact_mod_cast vV_nonneg w hw) (Nat.cast_nonneg e))
end GlobalTheory.Reg.Transfer
