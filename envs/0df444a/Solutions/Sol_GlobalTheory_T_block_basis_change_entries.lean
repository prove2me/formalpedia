-- Prove2me | solution 1 for GlobalTheory.T.block_basis_change_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:24.22011+00:00
-- url     : https://prove2.me/submissions/783556f0-7068-48a3-933a-60fec662cdd1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspace
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspaceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_MidConj_conj_units_of_mid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P.det →
    ∀ (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ), Jp * J = 1 → B * Bi = 1 →
    (∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j) →
    (∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0) →
    ∀ p q : Fin n', J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | exact GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | (intros; apply GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid <;> assumption)
end _root_.GlobalTheory.T
