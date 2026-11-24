-- Prove2me | solution 1 for GlobalTheory.SimAlg.form_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:09.438886+00:00
-- url     : https://prove2.me/submissions/a99615c8-f948-4576-947d-b1e50cd5f22f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_form_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (φ : Module.End ℤ Λ) (e : Λ) (P : ℤ[X]) (hP : aeval φ P e = 0) (h : ℂ[X]) :
    form (fun i j => b ((φ ^ i) e) ((φ ^ j) e)) (P.map (Int.castRingHom ℂ)) h = 0 := by
  have key : ∀ (P : ℤ[X]) (j : ℕ), form (fun i j => b ((φ ^ i) e) ((φ ^ j) e))
      (P.map (Int.castRingHom ℂ)) (X ^ j) = (b (aeval φ P e) ((φ ^ j) e) : ℤ) := by
    intro P j
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial i a =>
      rw [Polynomial.map_monomial, ← smul_X_eq_monomial, ← smul_X_eq_monomial]
      simp only [map_smul, LinearMap.smul_apply, form_pow, map_pow, aeval_X, smul_eq_mul]
      simp
  induction h using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial j c => rw [← smul_X_eq_monomial, map_smul, key, hP]; simp
end GlobalTheory.SimAlg
