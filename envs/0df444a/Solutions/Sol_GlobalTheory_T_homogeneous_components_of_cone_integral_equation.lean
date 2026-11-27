-- Prove2me | solution 1 for GlobalTheory.T.homogeneous_components_of_cone_integral_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:11.422779+00:00
-- url     : https://prove2.me/submissions/f2719cae-c39a-4207-b00a-7e65df8d3f7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousComponentsOfConeIntegralEquation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousComponentsOfConeIntegralEquationStatement
import Theorems.Thm_GlobalTheory_homogeneous_components_of_integral_equation


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
theorem _root_.solution : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 → ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.homogeneous_components_of_integral_equation | exact GlobalTheory.homogeneous_components_of_integral_equation | (intros; apply GlobalTheory.homogeneous_components_of_integral_equation <;> assumption)
end _root_.GlobalTheory.T
