-- Prove2me | solution 1 for GlobalTheory.CoeffWord.unitri_monomial_of_not
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:31.641825+00:00
-- url     : https://prove2.me/submissions/99bfb62a-27c7-426f-84ee-bc3a731a911f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_GlobalTheory_CoeffWord_mem_positions
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution (m : Fin r × Fin n →₀ ℕ) (hm : ¬ LowerTri m) (c : R) :
    unitri R (positions r n) (monomial m c) = 0 := by
  simp only [LowerTri, not_forall] at hm
  obtain ⟨a, s, h, h0⟩ := hm
  rw [unitri, aeval_monomial, Finsupp.prod,
    Finset.prod_eq_zero (i := (a, s)) (Finsupp.mem_support_iff.2 h0), mul_zero]
  have h1 : ¬ s.val < a.val := by omega
  simp [mem_positions, h.ne, h1, h0]
end GlobalTheory.CoeffWord
