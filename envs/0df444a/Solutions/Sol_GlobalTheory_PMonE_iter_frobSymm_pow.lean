-- Prove2me | solution 1 for GlobalTheory.PMonE.iter_frobSymm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:18:41.278454+00:00
-- url     : https://prove2.me/submissions/e690a012-e261-4470-83d7-39163ca668f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (m : ℕ) (y : F) : (((frobeniusEquiv F p).symm)^[m] y) ^ p ^ m = y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]
end GlobalTheory.PMonE
