-- Prove2me | solution 1 for GlobalTheory.generalLinearGroup_char_eq_one_of_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:18.372634+00:00
-- url     : https://prove2.me/submissions/ff72ab94-70b0-432b-8dd9-e420d2729f50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_ddChar_exists_unit
import Theorems.Thm_GlobalTheory_ddChar_induction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [Finite R] (r : ℕ) (A : Type) [CommGroup A]
      (ψ : GL (Fin r) R →* A), (∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 4 ≤ Nat.card (R ⧸ 𝔪)) →
      ∀ g : GL (Fin r) R, (g : Matrix (Fin r) (Fin r) R).det = 1 → ψ g = 1 := by
  intro R _ _ r A _ ψ h4 g hdet
  obtain ⟨u, hu⟩ := ddChar_exists_unit h4
  exact ddChar_induction ψ u hu Finset.univ g (fun i j _ hout => by simp at hout) hdet
end GlobalTheory
