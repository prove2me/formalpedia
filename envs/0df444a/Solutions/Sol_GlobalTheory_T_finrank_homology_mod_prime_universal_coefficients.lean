-- Prove2me | solution 1 for GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:22:34.062288+00:00
-- url     : https://prove2.me/submissions/fb4b6b18-ac89-4418-bfa6-fb06aaaea2a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankHomologyModPrimeUniversalCoefficients
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankHomologyModPrimeUniversalCoefficientsStatement
import Theorems.Thm_GlobalTheory_uct_mod_p


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  first | exact @GlobalTheory.uct_mod_p | exact GlobalTheory.uct_mod_p | (intros; apply GlobalTheory.uct_mod_p <;> assumption)
end _root_.GlobalTheory.T
