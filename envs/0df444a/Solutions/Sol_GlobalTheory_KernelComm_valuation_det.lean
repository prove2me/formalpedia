-- Prove2me | solution 1 for GlobalTheory.KernelComm.valuation_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:28:28.338886+00:00
-- url     : https://prove2.me/submissions/3abc3c81-44cd-4554-b9e7-6f2ff7713863

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_exists_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.KernelComm
theorem _root_.solution (q : Unif k) (P : Pair k n) {g : GL n k} (hg : g • P.ker = P.lat) :
    valuation k ((Matrix.GeneralLinearGroup.det g * q.unit : kˣ) : k) = 1 := by
  obtain ⟨d, hd, hdet⟩ := exists_det q P
  have := valuation_det_of_fix P.ker (h := d⁻¹ * g) (by rw [mul_smul, hg, ← hd, inv_smul_smul])
  rwa [map_mul, map_inv, hdet, inv_inv, mul_comm] at this
end GlobalTheory.KernelComm
