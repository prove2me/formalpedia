-- Prove2me | solution 1 for GlobalTheory.X_mem_germIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:50.010796+00:00
-- url     : https://prove2.me/submissions/2b741762-7269-42f3-b34c-0a84312b50cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_GlobalTheory_constDerivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] GlobalTheory.constDerivEval_X

set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution (i : σ) : (X i : MvPowerSeries σ R) ∈ germIdeal σ R := by
  simp [RingHom.mem_ker]
end GlobalTheory
