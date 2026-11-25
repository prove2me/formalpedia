-- Prove2me | solution 1 for GlobalTheory.GaugeGermIntegral.ev_sgP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:27.971021+00:00
-- url     : https://prove2.me/submissions/aa0b6769-962c-459d-94ee-d2515a7647e4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_C
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum


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
theorem _root_.solution (Y : FBChart K V O d) (v : Fin d → K) {n : ℕ} (a : Pt K n d)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    ev ![a] (Y.sgP v) = ∑ i, C (v i) * ev ![a] (sgOf K Y.h i) := by
  have h1 : CZ (![a] : Fin 1 → Pt K n d) := CZ.cons ha CZ.nil
  rw [FBChart.sgP, ev_neg h1, ev_sum h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : sgOf K Y.h i = -ev (n := 1) ![pt K d 0, 0] (pderiv K ((1 : Fin 2), i) Y.h) := rfl
  rw [ev_mul h1, ev_C h1, e, ev_neg h1, mul_neg]
end GlobalTheory.GaugeGermIntegral
