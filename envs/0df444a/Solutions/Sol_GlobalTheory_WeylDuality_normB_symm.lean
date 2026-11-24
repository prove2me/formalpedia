-- Prove2me | solution 1 for GlobalTheory.WeylDuality.normB_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:52.45987+00:00
-- url     : https://prove2.me/submissions/59f0e8ef-36ad-4ef3-a001-2aac386be0a7

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_normB_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : (normB hn ν).IsSymm := by
  exact ⟨fun x y => by rw [normB_apply, normB_apply, fockQ_symm x.1]⟩
end GlobalTheory.WeylDuality
