-- Prove2me | solution 1 for GlobalTheory.Nef.isRat_of_hankel_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:27.332792+00:00
-- url     : https://prove2.me/submissions/1244d7d3-61af-4562-825d-1cd0ade968cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
import Theorems.Thm_GlobalTheory_Nef_Kron_exists_annihilator
import Theorems.Thm_GlobalTheory_Nef_Kron_isRat_of_ann

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ),
    (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  intro F _ φ N hN
  obtain ⟨q, hq, h⟩ := Kron.exists_annihilator _ N hN
  exact Kron.isRat_of_ann φ q hq h
end GlobalTheory.Nef
