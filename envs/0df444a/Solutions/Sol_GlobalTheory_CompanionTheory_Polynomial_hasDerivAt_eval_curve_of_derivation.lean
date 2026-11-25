-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Polynomial.hasDerivAt_eval_curve_of_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:35:05.029851+00:00
-- url     : https://prove2.me/submissions/9c0d9b08-f410-4d80-a750-e2eac0c29bdf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtEvalCurveOfDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Polynomial
namespace GlobalTheory.CompanionTheory.Polynomial
theorem _root_.solution {σ : Type}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s)
    (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h0 : D (MvPolynomial.C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap a
    simp only [MvPolynomial.eval_C, h0, map_zero]
    exact hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    have e : MvPolynomial.eval (γ s) (D (p * MvPolynomial.X v)) =
        MvPolynomial.eval (γ s) (D p) * γ s v +
          MvPolynomial.eval (γ s) p * MvPolynomial.eval (γ s) (D (MvPolynomial.X v)) := by
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, MvPolynomial.eval_X]
      ring
    have hf : (fun u => MvPolynomial.eval (γ u) (p * MvPolynomial.X v)) =
        fun u => MvPolynomial.eval (γ u) p * γ u v := by
      funext u; simp
    rw [e, hf]
    exact hp.mul (hγ v)
end GlobalTheory.CompanionTheory.Polynomial
