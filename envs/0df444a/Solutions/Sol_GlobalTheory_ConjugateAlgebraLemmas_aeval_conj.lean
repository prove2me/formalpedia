-- Prove2me | solution 1 for GlobalTheory.ConjugateAlgebraLemmas.aeval_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:46.042797+00:00
-- url     : https://prove2.me/submissions/4e5db62e-7731-411a-bbd2-47f1e0d44df6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply
import Theorems.Thm_GlobalTheory_ConjugateAlgebraLemmas_conjAlg_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateAlgebraLemmas
open Matrix
namespace GlobalTheory.ConjugateAlgebraLemmas
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : Polynomial K) :
    Polynomial.aeval ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) Q
      = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K) := by
  have h : ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) = conjAlg g (γ : Matrix (Fin n) (Fin n) K) := by
    rw [conjAlg_apply, Units.val_mul, Units.val_mul]
  rw [h, Polynomial.aeval_algHom_apply, conjAlg_apply]
end GlobalTheory.ConjugateAlgebraLemmas
