-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.eval_idFrame_eq_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:34.120804+00:00
-- url     : https://prove2.me/submissions/8c0ff062-0c21-44e2-9eff-f323d3e94f96

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_GlobalTheory_FockHighestWeight_diagExp_apply
import Theorems.Thm_GlobalTheory_FockHighestWeight_eq_diagExp_of_offDiag
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
theorem _root_.solution {R : Type*} [CommRing R] {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) R}
    (hcol : ∀ m ∈ F.support, ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) :
    eval (idFrame R r n) F = coeff (diagExp r ν) F := by
  rw [eval_eq', Finset.sum_eq_single (diagExp r ν)]
  · rw [Finset.prod_eq_one, mul_one]
    rintro ⟨a, s⟩ _
    rw [diagExp_apply, idFrame]
    split_ifs <;> simp
  · intro m hm hne
    have : ¬ ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0 :=
      fun h => hne (eq_diagExp_of_offDiag (hcol m hm) h)
    push Not at this
    obtain ⟨a, s, h1, h2⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ (a, s)), mul_zero]
    simp [idFrame, h1, h2]
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]
end GlobalTheory.FockHighestWeight
