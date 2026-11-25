-- Prove2me | solution 1 for GlobalTheory.DenseCompl.eq_zero_of_forall_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:44.022418+00:00
-- url     : https://prove2.me/submissions/db755261-3539-4a77-b41b-53b7326f6312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
import Theorems.Thm_GlobalTheory_DenseCompl_le_of_forall_le_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl
namespace GlobalTheory.DenseCompl
theorem _root_.solution {a : ℤᵐ⁰} (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ))) : a = 0 :=
  le_antisymm (le_of_forall_le_exp zero_le' fun n _ => h n) zero_le'
end GlobalTheory.DenseCompl
