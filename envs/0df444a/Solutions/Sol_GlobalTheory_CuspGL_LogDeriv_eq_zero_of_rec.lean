-- Prove2me | solution 1 for GlobalTheory.CuspGL.LogDeriv.eq_zero_of_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:44:02.721382+00:00
-- url     : https://prove2.me/submissions/99d71c87-7488-45e2-9cd8-ea8b28be618f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolution
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_conv_eq_sum
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_pow_natDegree_ne_one
import Theorems.Thm_GlobalTheory_CuspGL_conv_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.LogDeriv
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.LogDeriv
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) {E : F[X] → ℂ} (h1 : E 1 = 0)
    (hE : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * E P = conv (fun _ => 1) E P) :
    ∀ P : F[X], P.Monic → E P = 0 := by
  intro P
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    by_cases hn : n = 0
    · rw [hP.natDegree_eq_zero.mp (h.trans hn)]; exact h1
    have key : conv (fun _ => 1) E P = E P := by
      rw [conv_eq_sum _ _ hP, Finset.sum_eq_single ((1 : F[X]), P)]
      · simp
      · intro x hx hne
        rw [Set.Finite.mem_toFinset] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        have hd : x.1.natDegree ≠ 0 := by
          intro h0
          have := h1.natDegree_eq_zero.mp h0
          apply hne
          rw [this, one_mul] at h3
          exact Prod.ext this h3
        have hdeg := h1.natDegree_mul h2
        rw [h3, h] at hdeg
        rw [ih x.2.natDegree (by omega) x.2 rfl h2, mul_zero]
      · intro hx
        exact absurd (by simp [hP]) hx
    have h2 := hE P hP
    rw [key, h] at h2
    have h3 : ((q : ℂ) ^ n - 1) * E P = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left (pow_natDegree_ne_one hq hn)
end GlobalTheory.CuspGL.LogDeriv
