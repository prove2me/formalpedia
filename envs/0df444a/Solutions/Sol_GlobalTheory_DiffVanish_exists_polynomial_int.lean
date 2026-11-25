-- Prove2me | solution 1 for GlobalTheory.DiffVanish.exists_polynomial_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:49.289121+00:00
-- url     : https://prove2.me/submissions/96cd2889-516f-468a-aa79-cb701dee3755

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_map
import Theorems.Thm_GlobalTheory_DiffVanish_map
import Theorems.Thm_GlobalTheory_DiffVanish_exists_polynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]
namespace GlobalTheory
namespace DiffVanish
theorem _root_.solution {d : ℕ} {φ : G → ℤ} (h : DiffVanish (d + 1) φ)
    (K : Type*) [Field K] [CharZero K] (a x : G) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧ (∀ n : ℤ, p.eval (n : K) = φ (x + n • a)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * multiDiff (fun _ : Fin d ↦ a) φ x := by
  obtain ⟨p, h1, h2, h3⟩ := (h.map (Int.castAddHom K)).exists_polynomial a x
  exact ⟨p, h1, h2, by rw [h3, multiDiff_map]; rfl⟩
end DiffVanish
end GlobalTheory
