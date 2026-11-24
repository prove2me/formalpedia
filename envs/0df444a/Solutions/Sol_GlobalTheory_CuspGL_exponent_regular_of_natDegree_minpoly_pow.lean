-- Prove2me | solution 1 for GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:01.630219+00:00
-- url     : https://prove2.me/submissions/5cfd24e1-8921-4b4f-8265-4b177136129a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  intro F _ _ d k ζ _ hord hdeg i hi hid hmod
  have h1 : ζ ^ (Nat.card F ^ d - 1) = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one ζ
  have h2 : (ζ ^ k) ^ (Nat.card F ^ i) = ζ ^ k := by
    rw [← pow_mul]; exact pow_eq_pow_of_modEq hmod h1
  have hint : IsIntegral F (ζ ^ k) := Algebra.IsIntegral.isIntegral _
  have hdvd : minpoly F (ζ ^ k) ∣ (X ^ (Nat.card F ^ i) - X : F[X]) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, h2, sub_self]
  have h3 := (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  rw [hdeg] at h3
  exact absurd (Nat.le_of_dvd hi h3) (not_le.mpr hid)
end GlobalTheory.CuspGL
