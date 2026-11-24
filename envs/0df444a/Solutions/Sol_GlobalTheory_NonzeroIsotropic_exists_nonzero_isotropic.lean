-- Prove2me | solution 1 for GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:31:04.764944+00:00
-- url     : https://prove2.me/submissions/1f321ea5-bc67-421f-ba59-1f338a9bc005

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic
import Theorems.Thm_GlobalTheory_NonzeroIsotropic_quadForm_totalDegree_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NonzeroIsotropic
open MvPolynomial
namespace GlobalTheory.NonzeroIsotropic
theorem _root_.solution :
    ∀ {k : Type u_1} [inst : Field k] [Finite k] (a : Fin (3 : ℕ) → Fin (3 : ℕ) → k),
      ∃ (x : Fin (3 : ℕ) → k), x ≠ (0 : Fin (3 : ℕ) → k) ∧
        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), a i j * x i * x j = (0 : k) := by
  intro k _ _ a
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero k p with h | h
    · exact h
    · subst h
      haveI : CharZero k := CharP.charP_to_charZero k
      exact absurd (Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective) (by
        intro h; exact not_finite ℕ)
  set f : MvPolynomial (Fin 3) k := ∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := quadForm_totalDegree_le a
    simp only [Fintype.card_fin]; omega
  have hdvd := char_dvd_card_solutions p hdeg
  have heval : ∀ x : Fin 3 → k, eval x f = ∑ i : Fin 3, ∑ j : Fin 3, a i j * x i * x j := by
    intro x; simp [hf]
  let z : { x : Fin 3 → k // eval x f = 0 } := ⟨0, by rw [heval]; simp⟩
  have hcard : 1 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := by
    have hpos : 0 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := Fintype.card_pos_iff.mpr ⟨z⟩
    have := Nat.le_of_dvd hpos hdvd
    have := hpp.two_le
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard z
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_⟩
  rw [← heval]; exact y.2
end GlobalTheory.NonzeroIsotropic
