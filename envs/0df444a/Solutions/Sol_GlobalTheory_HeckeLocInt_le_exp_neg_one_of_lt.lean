-- Prove2me | solution 1 for GlobalTheory.HeckeLocInt.le_exp_neg_one_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:58.195527+00:00
-- url     : https://prove2.me/submissions/1bd40d3c-767e-4480-a292-e2df387ead0d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.HeckeLocInt
open Matrix
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.HeckeLocInt
theorem _root_.solution {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at hx ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
  exact WithZero.exp_le_exp.2 (by omega)
end GlobalTheory.HeckeLocInt
