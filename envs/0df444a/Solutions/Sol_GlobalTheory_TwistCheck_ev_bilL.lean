-- Prove2me | solution 1 for GlobalTheory.TwistCheck.ev_bilL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:06.947933+00:00
-- url     : https://prove2.me/submissions/07b9ed73-25cf-4f6b-ad14-b5a79ea3ae3e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_BilLActRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply


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
open GlobalTheory GlobalTheory.TwistCheck
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace GlobalTheory.TwistCheck
theorem _root_.solution {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a) :
    ev a (bilL G cc) = ∑ i, ∑ l, C (cc i l) * (ev ![a 0] (logOf G i) * ev ![a 1] (logOf G l)) := by
  simp only [bilL, ev_sum ha, smul_eq_C_mul, ev_mul ha, ev_C ha, lg, ev_ev ha czX, ev_ev ha czY]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  congr 3 <;> funext j c <;> fin_cases j <;> simp [pt_apply, ev_X ha]
end GlobalTheory.TwistCheck
