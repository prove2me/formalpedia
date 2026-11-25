-- Prove2me | solution 1 for GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:06.4394+00:00
-- url     : https://prove2.me/submissions/4511b9b4-6ef2-45d6-97a7-6950a284c567

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
import Theorems.Thm_GlobalTheory_EigenvalueNormAtMostOne_norm_eigenvalue_le_one_of_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EigenvalueNormAtMostOne
namespace GlobalTheory.EigenvalueNormAtMostOne
theorem _root_.solution :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (O : Type) [inst_1 : CommRing O]
      (emb : O →+* PadicAlgCl l), (∀ (a : O), ‖(emb : O → PadicAlgCl l) a‖ ≤ (1 : ℝ)) →
      ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l) (μ : PadicAlgCl l),
        c ≠ (0 : Fin n → PadicAlgCl l) →
        Matrix.mulVec (Matrix.map N (⇑emb : O → PadicAlgCl l)) c = μ • c → ‖μ‖ ≤ (1 : ℝ) := by
  intro l _ O _ emb hemb n N c μ hc h
  exact norm_eigenvalue_le_one_of_entries _ (fun i j => hemb (N i j)) c μ hc h
end GlobalTheory.EigenvalueNormAtMostOne
