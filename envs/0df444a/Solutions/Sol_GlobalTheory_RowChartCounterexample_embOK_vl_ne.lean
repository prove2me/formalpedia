-- Prove2me | solution 1 for GlobalTheory.RowChartCounterexample.embOK_vl_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:41.335106+00:00
-- url     : https://prove2.me/submissions/71b6c7fe-fe1b-4f55-8686-6b0f8e17d3b7

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
theorem _root_.solution {T : CDVR} {V : VF C} {ι : T.Fr →+* C} (h : EmbOK T V ι) :
    vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by
  intro h0
  have hl : ((V.l : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 V.l_prime.ne_zero
  have := h _ hl
  rw [map_natCast, V.v_l, h0] at this
  simp at this
end GlobalTheory.RowChartCounterexample
