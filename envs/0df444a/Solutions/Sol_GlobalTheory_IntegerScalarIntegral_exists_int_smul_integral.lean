-- Prove2me | solution 1 for GlobalTheory.IntegerScalarIntegral.exists_int_smul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:57.236132+00:00
-- url     : https://prove2.me/submissions/e652e80c-3b7b-486e-bdbc-9564f8eda0e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntSmulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IntegerScalarIntegral
open NumberField
namespace GlobalTheory.IntegerScalarIntegral
theorem _root_.solution {K : Type u_1} [Field K] [NumberField K] (c : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ c)
  exact hc.exists_integral_multiple
end GlobalTheory.IntegerScalarIntegral
