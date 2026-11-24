-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StrictCone.char_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:05:36.494986+00:00
-- url     : https://prove2.me/submissions/d9f54495-fe4f-4f3b-9ba9-bc79604b4dd3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone
import Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_char_eq_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_zpow_sum_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone
namespace GlobalTheory.CompanionTheory.StrictCone
theorem _root_.solution {n : ℕ} (c : Fin n → ℤ) (Q : ℂˣ) (φ : (Fin n → ℤ) → ℂˣ)
    (h : ∀ g g', φ (g + g') = φ g * φ g') :
    ∃ ξ : Fin n → ℂˣ, ∀ x, φ x = Q ^ (∑ i, c i * x i) * ∏ i, ξ i ^ x i := by
  refine ⟨fun i => φ (Pi.single i 1) * Q ^ (-c i), fun x => ?_⟩
  rw [char_eq_prod φ h x, zpow_sum_units, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_zpow, ← zpow_mul, mul_left_comm, ← zpow_add]
  simp
end GlobalTheory.CompanionTheory.StrictCone
