-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.isKStableOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:58.668985+00:00
-- url     : https://prove2.me/submissions/2ede5c7d-334b-4467-9f7e-27cf5df7de57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Theorems.Thm_GlobalTheory_KTypeCompare_Kset_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (S : Submodule ℂ H) :
    PI.UpqRep.IsKStableOn ε σ S ↔ HarishChandraRootData.KStable ε σ S := by
  unfold PI.UpqRep.IsKStableOn HarishChandraRootData.KStable
  rw [Kset_eq]
end GlobalTheory.KTypeCompare
