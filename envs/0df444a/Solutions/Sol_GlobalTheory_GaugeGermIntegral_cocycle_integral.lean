-- Prove2me | solution 1 for GlobalTheory.GaugeGermIntegral.cocycle_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:09.026808+00:00
-- url     : https://prove2.me/submissions/b7d41b56-cc55-4ba3-a60f-3e51e90fc4da

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_intS_iff
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_map_self
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_FK_self
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_ev_sgP
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_int_comb
import Theorems.Thm_GlobalTheory_SigmaDefect_sgOf_defect
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (Y : FBChart K V O d) : GermISt Y := by
  intro v hv
  have hadd : addOf Y.B.G.F (pt K (n := 2) d 0) (pt K d 1) = Y.B.G.F := by
    funext i
    have e : (![pt K (n := 2) d 0, pt K d 1] : Fin 2 → Pt K 2 d) = fun j => pt K d j := by
      funext j
      fin_cases j <;> rfl
    rw [addOf, e, ev_pt]
  rw [intS_iff, hadd, ev_sgP Y v _ Y.B.G.const, ev_sgP Y v _ (cc_pt 0), ev_sgP Y v _ (cc_pt 1),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  convert int_comb v hv _ Y.intPh1 using 2 with i
  have e := GlobalTheory.SigmaDefect.sgOf_defect Y.B Y.h Y.gauge i
  rw [FB.toK, map_self, FK_self] at e
  rw [e]
  ring
end GlobalTheory.GaugeGermIntegral
