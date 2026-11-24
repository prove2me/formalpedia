-- Prove2me | solution 1 for GlobalTheory.SW.SiegelSum.summable_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:24.689801+00:00
-- url     : https://prove2.me/submissions/16f8a96b-a12f-4d50-900d-90f12e33a6dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Theorems.Thm_GlobalTheory_SummableProdPi_summable_prod_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum
namespace GlobalTheory.SW.SiegelSum
theorem _root_.solution {J A : Type} [Fintype J] (f : J → A → ℝ) (h0 : ∀ j a, 0 ≤ f j a)
    (hs : ∀ j, Summable (f j)) : Summable fun n : J → A => ∏ j, f j (n j) := by
  first
  | exact @_root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | (apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi ..)
end GlobalTheory.SW.SiegelSum
