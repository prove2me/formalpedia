-- Prove2me | solution 1 for GlobalTheory.SuperCusp.val_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:50.902665+00:00
-- url     : https://prove2.me/submissions/214a825c-ee47-4fed-90de-966344bd38ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp
namespace GlobalTheory.SuperCusp
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] {P Q : Matrix n n k}
    (hP : ∀ p q, valuation k (P p q) ≤ 1) (hQ : ∀ p q, valuation k (Q p q) ≤ 1) (p q : n) :
    valuation k ((P * Q) p q) ≤ 1 :=
  Valuation.map_sum_le _ fun s _ => by rw [map_mul]; exact mul_le_one' (hP _ _) (hQ _ _)
end GlobalTheory.SuperCusp
