-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.weight_rowW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:27.798781+00:00
-- url     : https://prove2.me/submissions/32080c2c-8d7b-4291-98e5-cb47c42f304a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}
namespace GlobalTheory.FockHighestWeight
theorem _root_.solution (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = ∑ s : Fin n, m (a, s) := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [rowW, Pi.single_apply]
end GlobalTheory.FockHighestWeight
