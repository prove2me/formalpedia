-- Prove2me | solution 1 for GlobalTheory.CoeffWord.unitri_monomial_of_lowerTri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:30.827122+00:00
-- url     : https://prove2.me/submissions/9ea09cdc-7990-4d6d-b4c1-8cfc24479ee0

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_GlobalTheory_CoeffWord_mem_positions
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
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution (m : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (c : R) :
    unitri R (positions r n) (monomial m c) = monomial (m.filter (· ∈ positions r n)) c := by
  classical
  rw [unitri, aeval_monomial, monomial_eq, Finsupp.prod_filter_index, Finsupp.support_filter,
    Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hv' : m v ≠ 0 := Finsupp.mem_support_iff.1 hv
  have h1 : ¬ v.1.val < v.2.val := fun h => hv' (hm v.1 v.2 h)
  by_cases h2 : v.1.val = v.2.val
  · simp [mem_positions, h2]
  · have h3 : v.2.val < v.1.val := by omega
    simp [mem_positions, h2, h3]
end GlobalTheory.CoeffWord
