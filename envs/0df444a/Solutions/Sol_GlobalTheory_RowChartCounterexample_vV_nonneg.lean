-- Prove2me | solution 1 for GlobalTheory.RowChartCounterexample.vV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:44.989432+00:00
-- url     : https://prove2.me/submissions/1100c5ca-4a5d-4e60-a0a0-92b4c7c3f3a3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_ImaginaryRootConj

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
open GlobalTheory GlobalTheory.RowChartCounterexample
open Formalism.L2.FormalSeriesBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {C : Type} [Field C]
namespace GlobalTheory.RowChartCounterexample
theorem _root_.solution (T : CDVR) (a : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
  unfold vV
  by_cases ha : valV T.V (algebraMap T.V T.Fr a) = 0
  · simp [ha]
  have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  have := (WithZero.log_le_log ha one_ne_zero).2 h1
  simp at this
  omega
end GlobalTheory.RowChartCounterexample
