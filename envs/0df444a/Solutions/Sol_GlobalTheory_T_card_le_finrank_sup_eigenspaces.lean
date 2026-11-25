-- Prove2me | solution 1 for GlobalTheory.T.card_le_finrank_sup_eigenspaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:27.287141+00:00
-- url     : https://prove2.me/submissions/9134b972-b1b5-4533-aaf8-c6ae83e5f9ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardLeFinrankSupEigenspaces
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardLeFinrankSupEigenspacesStatement
import Theorems.Thm_GlobalTheory_finrank_iSup_iInf_eigenspace_ge_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (O : Type) (T : O → Module.End ℂ W),
    (∀ a b, Commute (T a) (T b)) → ∀ (I : Type) [Fintype I] (ψ : I → O → ℂ), Function.Injective ψ →
    (∀ i, 1 ≤ Module.finrank ℂ (⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W)) →
    Fintype.card I ≤ Module.finrank ℂ (⨆ i, ⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W) := by
  first | exact @GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card | exact GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card | (intros; apply GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card <;> assumption)
end _root_.GlobalTheory.T
