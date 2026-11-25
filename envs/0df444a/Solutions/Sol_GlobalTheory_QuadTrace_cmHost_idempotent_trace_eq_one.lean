-- Prove2me | solution 1 for GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:07.152364+00:00
-- url     : https://prove2.me/submissions/9ab4bd90-e8f8-40c2-962a-9525a2bd69c3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CmHostIdempotentTraceEqOne
import Theorems.Thm_GlobalTheory_QuadTrace_bar_rt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField
open GlobalTheory GlobalTheory.QuadTrace
namespace GlobalTheory.QuadTrace
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.HostTraceIdentity H := by
  intro E _ _ _ H _ hstar
  rw [hstar]
  have hb := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, bar_rt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2
end GlobalTheory.QuadTrace
