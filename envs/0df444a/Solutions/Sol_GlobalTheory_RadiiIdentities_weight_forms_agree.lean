-- Prove2me | solution 1 for GlobalTheory.RadiiIdentities.weight_forms_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:26.059032+00:00
-- url     : https://prove2.me/submissions/b94b9ad7-d32a-4f01-88b8-8f4e2a2d0ffe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities
namespace GlobalTheory.RadiiIdentities
theorem _root_.solution : WeightConditionIff := by
  intro C _ v l i n0 h1
  have e1 : rho l + 1 / (2 * (l : ℝ) ^ i) - 1 / (8 * (l : ℝ) ^ i) =
      rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  have e2 : rho l + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) = rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  simp only [HM1, WeightCond, r1, r2, del, e1, e2]
end GlobalTheory.RadiiIdentities
