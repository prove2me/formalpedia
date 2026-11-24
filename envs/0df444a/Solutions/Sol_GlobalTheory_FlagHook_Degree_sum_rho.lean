-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.sum_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:39.023063+00:00
-- url     : https://prove2.me/submissions/dceb4c46-471e-4522-bf10-bc27445e09fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree
namespace GlobalTheory.FlagHook.Degree
theorem _root_.solution (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id]
end GlobalTheory.FlagHook.Degree
