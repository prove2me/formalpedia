-- Prove2me | solution 1 for GlobalTheory.CapelliTop.subdet_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:39:24.43666+00:00
-- url     : https://prove2.me/submissions/72193bf5-0521-42f9-bc5e-f4d3d78286a5

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Theorems.Thm_GlobalTheory_CapelliTop_oprod_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.CapelliTop
theorem _root_.solution (E : Fin n → Fin n → A) : subdet E ∅ = 1 := by
  have : univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ k, k ∉ (∅ : Finset (Fin n)) → σ k = k) = {1} := by
    ext σ; simp [Equiv.ext_iff]
  rw [subdet, this, Finset.sum_singleton, oprod_eq _ _ [] (by simp) (by simp)]
  simp
end GlobalTheory.CapelliTop
