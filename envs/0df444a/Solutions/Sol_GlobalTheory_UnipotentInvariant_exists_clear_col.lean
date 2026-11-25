-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.exists_clear_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:07.924131+00:00
-- url     : https://prove2.me/submissions/f7a713e3-6091-4ef6-ab85-1767858d53be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_P2M_GlobalTheory_UnipotentInvariant_BiInvariant_what__0c48a7516dd9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (n : Fin p) (M : Matrix (Fin p) (Fin p) K) (hn : M n n ≠ 0) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      (∀ b, n < b → M' b n = 0) ∧ (∀ b k, b ≤ n → M' b k = M b k) ∧
      (∀ b k, M n k = 0 → M' b k = M b k) := by
  refine ⟨Matrix.of fun b k => M b k +
      if b ∈ Finset.Ioi n then (- M b n / M n n) * M n k else 0, fun f hf => ?_, ?_, ?_, ?_⟩
  · exact hf.what₂ n (fun b => - M b n / M n n) M _ (by simp)
  · intro b hb
    simp only [of_apply, Finset.mem_Ioi, hb, if_true]
    field_simp
    ring
  · intro b k hb
    simp [not_lt.mpr hb]
  · intro b k hk
    simp [hk]
end GlobalTheory.UnipotentInvariant
