-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAntipode.unop_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:24.046289+00:00
-- url     : https://prove2.me/submissions/80d037ea-f321-4755-9cd3-89308ea2cd84

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_unop_ofFn_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_ofFn_prod_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_Tm_op_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_arg_rev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAntipode
namespace GlobalTheory.CompanionTheory.CapelliAntipode
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (v : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    MulOpposite.unop ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Aᵐᵒᵖ) *
        (List.ofFn fun k : Fin n =>
          Tm (fun i j => MulOpposite.op (-X i j)) (v - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod) =
      ((-1 : ℂ) ^ n) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin n =>
          Tm X (((n : ℂ) - 1 - v) - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod) := by
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast, unop_ofFn_prod]
  simp only [Tm_op_neg, MulOpposite.unop_op, id, arg_rev]
  rw [ofFn_prod_neg, smul_mul_assoc, ← Int.cast_comm]
end GlobalTheory.CompanionTheory.CapelliAntipode
