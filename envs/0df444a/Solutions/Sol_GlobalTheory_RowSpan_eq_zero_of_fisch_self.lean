-- Prove2me | solution 1 for GlobalTheory.RowSpan.eq_zero_of_fisch_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:41.82487+00:00
-- url     : https://prove2.me/submissions/3079c515-1766-44e1-b60a-e1fa865d6a33

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_fisch_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
variable {σ : Type}
namespace GlobalTheory.RowSpan
theorem _root_.solution {P : MvPolynomial σ ℚ} (h : fisch P P = 0) : P = 0 := by
  by_contra h0
  have : 0 < fisch P P := by
    nth_rewrite 1 [P.as_sum]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_pos (fun m hm => ?_) (support_nonempty.2 h0)
    rw [fisch_monomial, mul_left_comm]
    have hf : 0 < (m.prod fun _ e => e.factorial : ℕ) := Finset.prod_pos fun i _ => Nat.factorial_pos _
    exact mul_pos (by exact_mod_cast hf) (mul_self_pos.2 (mem_support_iff.1 hm))
  exact this.ne' h
end GlobalTheory.RowSpan
