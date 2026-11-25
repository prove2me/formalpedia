-- Prove2me | solution 1 for GlobalTheory.GaugeGermIntegral.invariant_deriv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:44.611148+00:00
-- url     : https://prove2.me/submissions/7cae4202-e350-482e-be67-7d548ecfede2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_intS_iff
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_second_deriv
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_ev_sgP
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_int_comb
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_SigmaDefect_ev_sgOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.GaugeGermIntegral
variable {K : Type} [Field K]
variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {V : VF K}
namespace GlobalTheory.GaugeGermIntegral
theorem _root_.solution (Y : FBChart K V O d) : GermIISt Y := by
  intro v hv
  rw [intS_iff, ev_sgP Y v _ (cc_pt 0)]
  convert neg_mem (int_comb v hv _ Y.intPh2) using 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := second_deriv Y.B Y.h Y.gauge i
  rw [GlobalTheory.SigmaDefect.ev_sgOf _ _ _ (cc_pt 0)]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, e]
  ring
end GlobalTheory.GaugeGermIntegral
