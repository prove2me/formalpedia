-- Prove2me | solution 1 for GlobalTheory.NoetherInt.exists_algebraicIndependent_of_quasiFiniteAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:16.791689+00:00
-- url     : https://prove2.me/submissions/e280843b-54f1-4c61-bf0e-155a8c8dbea8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Theorems.Thm_GlobalTheory_NoetherInt_exists_quasiFiniteAt_of_not_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
namespace GlobalTheory.NoetherInt
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S]
    [CharZero S] (q : Ideal S) [q.IsPrime] (n : ℕ) :
    ∀ y : Fin n → S, (aeval y : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q →
    ∃ (r : ℕ) (y' : Fin r → S), AlgebraicIndependent ℤ y' ∧
      (aeval y' : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by
  induction n with
  | zero =>
    intro y h
    refine ⟨0, y, ?_, h⟩
    rw [algebraicIndependent_empty_type_iff]
    exact Int.cast_injective
  | succ n ih =>
    intro y h
    by_cases hy : Function.Injective (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S)
    · exact ⟨n + 1, y, hy, h⟩
    · obtain ⟨y', hy'⟩ := exists_quasiFiniteAt_of_not_injective q y h hy
      exact ih y' hy'
end GlobalTheory.NoetherInt
