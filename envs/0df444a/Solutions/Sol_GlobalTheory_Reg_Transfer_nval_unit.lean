-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.nval_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:34.775883+00:00
-- url     : https://prove2.me/submissions/2789b29d-7b4f-4f8a-a396-71e98c3da170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_vV_unit
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne


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
theorem _root_.solution (e : ℕ) (u : V) (hu : u ∉ maximalIdeal V) : nval V e (algebraMap V (FractionRing V) u) = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ (maximalIdeal V).zero_mem)
  have hu' : algebraMap V (FractionRing V) u ≠ 0 := by
    intro h; apply hu0; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  rw [nval_of_ne hu', vV_unit u hu]
  simp
end GlobalTheory.Reg.Transfer
