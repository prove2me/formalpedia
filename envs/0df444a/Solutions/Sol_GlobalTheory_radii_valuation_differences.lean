-- Prove2me | solution 1 for GlobalTheory.radii_valuation_differences
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:23.104835+00:00
-- url     : https://prove2.me/submissions/f455eb00-94da-4b7e-a6f9-4cae6715d99e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Theorems.Thm_GlobalTheory_RadiiIdentities_exponent_integral
import Theorems.Thm_GlobalTheory_RadiiIdentities_radii_sum
import Theorems.Thm_GlobalTheory_RadiiIdentities_slope_identity
import Theorems.Thm_GlobalTheory_RadiiIdentities_val_other_prime
import Theorems.Thm_GlobalTheory_RadiiIdentities_weight_forms_agree
import Theorems.Thm_GlobalTheory_RadiiIdentities_binomial_differences

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
open RadiiIdentities
namespace GlobalTheory
theorem _root_.solution :
    Formalism.L2.FormalSeriesBounds.EInt ∧ I1 ∧ I2 ∧ ValOther ∧ WeightConditionIff ∧ F5 :=
  ⟨exponent_integral, radii_sum, slope_identity, val_other_prime, weight_forms_agree,
    binomial_differences⟩
end GlobalTheory
