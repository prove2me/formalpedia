-- Prove2me | solution 1 for GlobalTheory.RealAlgebraCharacters.chi_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:55:12.985801+00:00
-- url     : https://prove2.me/submissions/de0fdda7-fbfa-4a9c-a755-b139ef88037a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealAlgSep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RealAlgebraCharacters
open Filter Topology
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)
namespace GlobalTheory.RealAlgebraCharacters
theorem _root_.solution (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1) (b : B) (x : X) :
    χ (-b) x = (starRingEnd ℂ) (χ b x) := by
  have h1 : χ (-b) x * χ b x = 1 := by rw [← hadd, neg_add_cancel, h0]
  have h2 : χ (-b) x = (χ b x)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h2, Complex.inv_def, Complex.normSq_eq_norm_sq, hn b x]
  simp
end GlobalTheory.RealAlgebraCharacters
