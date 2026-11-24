-- Prove2me | solution 1 for GlobalTheory.NormUnits.exists_sqrt_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:49.547797+00:00
-- url     : https://prove2.me/submissions/2a4f96bd-34d6-4d65-8a1f-62be8e9a1383

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Theorems.Thm_GlobalTheory_NormUnits_finite_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GlobalTheory.NormUnits
theorem _root_.solution [LocallyCompactSpace K] (t : K) (ht : ‖t‖ ≤ 1) (h2 : ‖(2 : K)‖ < 1) :
    ∃ r : K, ‖r‖ ≤ 1 ∧ ‖r ^ 2 - t‖ < 1 := by
  classical
  haveI := finite_res K
  letI : Fintype (Res K) := Fintype.ofFinite _
  let T : intRing K := ⟨t, mem_closedBall_zero_iff.2 ht⟩
  have h2k : (2 : Res K) = 0 := by
    have h11 : (((1 + 1 : intRing K)) : K) = 2 := by
      rw [Subring.coe_add, Subring.coe_one]; norm_num
    have : (Ideal.Quotient.mk (maxIdeal K) (1 + 1) : Res K) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 ((mem_maxIdeal K _).2 (by rw [h11]; exact h2))
    rw [map_add, map_one] at this
    rw [← one_add_one_eq_two]; exact this
  have hchar : ringChar (Res K) = 2 := by
    have hd : ringChar (Res K) ∣ 2 := ringChar.dvd (by exact_mod_cast h2k)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two hchar (Ideal.Quotient.mk (maxIdeal K) T)
  obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨l, norm_le_one K l, ?_⟩
  have h0 : Ideal.Quotient.mk (maxIdeal K) (l * l - T) = 0 := by
    rw [map_sub, map_mul, ← hy, sub_self]
  have hm := (mem_maxIdeal K _).1 ((Ideal.Quotient.eq_zero_iff_mem).1 h0)
  simpa [sq, T] using hm
end GlobalTheory.NormUnits
