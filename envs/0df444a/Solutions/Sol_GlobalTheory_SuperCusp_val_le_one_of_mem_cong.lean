-- Prove2me | solution 1 for GlobalTheory.SuperCusp.val_le_one_of_mem_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:49.894022+00:00
-- url     : https://prove2.me/submissions/afd9fe21-3a25-4f0e-bc41-8f806b1ed2cd

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
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {κ : GL n k}
    (hκ : κ ∈ CentralExponent.cong n (1 : (ValueGroupWithZero k)ˣ) le_rfl) (p q : n) :
    valuation k ((κ : Matrix n n k) p q) ≤ 1 := by
  have h1 : valuation k (((κ : Matrix n n k) - 1) p q) ≤ 1 := by
    have := hκ p q
    exact_mod_cast this.le
  have h2 : valuation k ((1 : Matrix n n k) p q) ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have := Valuation.map_add_le _ h1 h2
  simpa using this
end GlobalTheory.SuperCusp
