-- Prove2me | solution 1 for GlobalTheory.MinorNorm.hookNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:52:16.363465+00:00
-- url     : https://prove2.me/submissions/6456a05b-0cc0-4944-af5b-63dd9c69d0bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_fock_del

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
variable {σ : Type} (v : Fin l → Fin l → σ)
variable {v}
namespace GlobalTheory.MinorNorm
theorem _root_.solution : HookNorm := by
  intro n l h a ha
  exact fock_del (v := fun r c => (Fin.castLE h r, c))
    (fun r c s e hh => ⟨Fin.castLE_injective _ (Prod.mk.inj hh).1, (Prod.mk.inj hh).2⟩) a ha
end GlobalTheory.MinorNorm
