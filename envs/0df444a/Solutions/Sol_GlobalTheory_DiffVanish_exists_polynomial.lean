-- Prove2me | solution 1 for GlobalTheory.DiffVanish.exists_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:53.939855+00:00
-- url     : https://prove2.me/submissions/2c98be95-e659-4f68-bc80-2c617bec3cdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_comap
import Theorems.Thm_GlobalTheory_multiDiff_translate
import Theorems.Thm_GlobalTheory_multiDiff_polynomial_eval
import Theorems.Thm_GlobalTheory_DiffVanish_exists_mvPolynomial

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
theorem _root_.solution {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) (a x : G) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧ (∀ n : ℤ, p.eval (n : K) = φ (x + n • a)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * multiDiff (fun _ : Fin d ↦ a) φ x := by
  obtain ⟨P, h1, h2, -, -⟩ := h.exists_mvPolynomial (fun _ : Unit ↦ a) x
  let p : Polynomial K := MvPolynomial.aeval (fun _ ↦ Polynomial.X) P
  have hp : p.natDegree ≤ d := by
    simpa using MvPolynomial.aeval_natDegree_le P h1 (fun _ ↦ Polynomial.X) (n := 1)
      (fun _ ↦ Polynomial.natDegree_X_le)
  have he : ∀ n : ℤ, p.eval (n : K) = φ (x + n • a) := fun n ↦ by
    have := h2 fun _ ↦ n
    simp only [univ_unique, sum_singleton] at this
    rw [← this, ← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp [MvPolynomial.aeval_eq_eval]
  refine ⟨p, hp, he, ?_⟩
  have hd : (d.factorial : K) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  have e1 := multiDiff_polynomial_eval (fun _ : Fin d ↦ (1 : K)) p hp 0
  have e2 := congrFun (multiDiff_comap (Int.castAddHom K) (fun _ : Fin d ↦ (1 : ℤ))
    (fun t ↦ p.eval t)) 0
  have e3 := congrFun (multiDiff_comap (zmultiplesHom G a) (fun _ : Fin d ↦ (1 : ℤ))
    (fun y ↦ φ (x + y))) 0
  simp only [Function.comp_def, Int.coe_castAddHom, Int.cast_one, Int.cast_zero, he,
    zmultiplesHom_apply, one_smul, zero_smul, multiDiff_translate, add_zero] at e2 e3
  rw [← e3, e2, e1]
  simp [hd]
end DiffVanish
end GlobalTheory
