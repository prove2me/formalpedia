-- Prove2me | solution 1 for GlobalTheory.RowChartCounterexample.embOK_eOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:01.741457+00:00
-- url     : https://prove2.me/submissions/f828997d-fdcd-4b99-bef6-eeb6a296c0a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_ImaginaryRootConj
import Theorems.Thm_GlobalTheory_RowChartCounterexample_embOK_vl_ne
import Theorems.Thm_GlobalTheory_RowChartCounterexample_vV_nonneg

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
theorem _root_.solution {T : CDVR} {V : VF C} {ι : T.Fr →+* C} (h : EmbOK T V ι) :
    0 < eOf T V ∧ ((eOf T V : ℕ) : ℤ) = vV T.V ((V.l : ℕ) : T.Fr) := by
  have h0 : 0 ≤ vV T.V ((V.l : ℕ) : T.Fr) := by
    have := vV_nonneg T (V.l : T.V)
    rwa [map_natCast] at this
  have h1 := embOK_vl_ne h
  unfold eOf
  omega
end GlobalTheory.RowChartCounterexample
