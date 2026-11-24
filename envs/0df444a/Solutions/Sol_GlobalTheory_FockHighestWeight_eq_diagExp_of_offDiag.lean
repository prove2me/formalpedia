-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.eq_diagExp_of_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:27.853169+00:00
-- url     : https://prove2.me/submissions/19ce879e-716e-4d05-95e5-219ad85c9f72

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_GlobalTheory_FockHighestWeight_diagExp_apply
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
theorem _root_.solution {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ}
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hoff : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0) : m = diagExp r ν := by
  ext ⟨a, s⟩
  rw [diagExp_apply]
  split_ifs with h
  · rw [← hcol s, Finset.sum_eq_single a]
    · intro b _ hb
      apply hoff
      intro e
      exact hb (Fin.ext (e.trans h.symm))
    · simp
  · exact hoff a s h
end GlobalTheory.FockHighestWeight
