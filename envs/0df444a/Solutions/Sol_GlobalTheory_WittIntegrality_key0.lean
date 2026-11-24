-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.key0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:57.095701+00:00
-- url     : https://prove2.me/submissions/6ef954ca-7391-47da-9b67-605a0740e040

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
import Theorems.Thm_GlobalTheory_WittIntegrality_mem_of_pow_mem
import Theorems.Thm_GlobalTheory_WittIntegrality_mem_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable [CharP C p]
variable [PerfectRing C p]
namespace GlobalTheory.WittIntegrality
theorem _root_.solution {n : Type} [Fintype n] (Y Z B : Matrix n n (WittVector p C))
    (hY : ∀ i j, Y i j ∈ S A p) (hB : ∀ i j, B i j ∈ S A p)
    (h : ∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) :
    ∀ i j, (Z i j).coeff 0 ∈ A := by
  classical
  have he : ∀ i j, (Z i j).coeff 0 ^ p =
      ∑ a, (Y i a).coeff 0 * (Z a j).coeff 0 + (B i j).coeff 0 := by
    intro i j
    have := congrArg (WittVector.constantCoeff (p := p) (R := C)) (h i j)
    simp only [map_add, map_sum, map_mul, WittVector.constantCoeff_apply,
      coeff_frobenius_charP] at this
    exact this
  by_contra hne
  push_neg at hne
  obtain ⟨i0, j0, hij⟩ := hne
  obtain ⟨⟨i1, j1⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n))
    (fun q => A.valuation ((Z q.1 q.2).coeff 0)) ⟨(i0, j0), Finset.mem_univ _⟩
  set z1 := (Z i1 j1).coeff 0 with hz1
  have h1 : 1 < A.valuation z1 := by
    have a := hmax (i0, j0) (Finset.mem_univ _)
    have b : ¬ A.valuation ((Z i0 j0).coeff 0) ≤ 1 := by rwa [A.valuation_le_one_iff]
    exact lt_of_lt_of_le (not_le.mp b) a
  have hz1A : z1 ∉ A := by
    rw [← A.valuation_le_one_iff]; exact not_le.mpr h1
  have hz0 : z1 ≠ 0 := fun e => hz1A (e ▸ A.zero_mem)
  have hle : A.valuation (z1 ^ p) ≤ A.valuation z1 := by
    rw [hz1, he i1 j1]
    refine Valuation.map_add_le _ ?_ ?_
    · refine Valuation.map_sum_le _ fun a _ => ?_
      rw [map_mul]
      calc A.valuation ((Y i1 a).coeff 0) * A.valuation ((Z a j1).coeff 0)
          ≤ 1 * A.valuation ((Z a j1).coeff 0) :=
            by gcongr; exact (A.valuation_le_one_iff _).2 ((mem_S A _).1 (hY i1 a) 0)
        _ ≤ A.valuation z1 := by rw [one_mul]; exact hmax (a, j1) (Finset.mem_univ _)
    · exact ((A.valuation_le_one_iff _).2 ((mem_S A _).1 (hB i1 j1) 0)).trans h1.le
  have hpm : z1 ^ (p - 1) ∈ A := by
    rw [← A.valuation_le_one_iff]
    have e : z1 ^ (p - 1) = z1 ^ p * z1⁻¹ := by
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    rw [e, map_mul]
    calc A.valuation (z1 ^ p) * A.valuation z1⁻¹ ≤ A.valuation z1 * A.valuation z1⁻¹ :=
          by gcongr
      _ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
  exact hz1A (mem_of_pow_mem A (by have := hp.out.two_le; omega) hpm)
end GlobalTheory.WittIntegrality
