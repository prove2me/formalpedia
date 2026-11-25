-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.Psi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:15.55373+00:00
-- url     : https://prove2.me/submissions/4f0bbf86-4acd-4a42-86bd-704870b0b78e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_RootValueClassBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis
theorem _root_.solution (rk : (E ≃ₐ[ℚ] E) → ℕ) (x y : E) : Psi rk (x * y) = Psi rk x * Psi rk y := by
  simp only [Psi, map_mul, mul_pow, Finset.prod_mul_distrib]
end GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis
