-- Prove2me | solution 1 for GlobalTheory.T.exists_dividedPowerEval_twoVars_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:20.374058+00:00
-- url     : https://prove2.me/submissions/2428e611-9df0-4efa-91cc-2506fdb9b0f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHomStatement
import Theorems.Thm_GlobalTheory_dpEval_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  first | exact @GlobalTheory.dpEval_two | exact GlobalTheory.dpEval_two | (intros; apply GlobalTheory.dpEval_two <;> assumption)
end _root_.GlobalTheory.T
