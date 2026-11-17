-- Prove2me | solution 1 for N25.dilation25_triangular_five_dvd
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:32.797753+00:00
-- url     : https://prove2.me/submissions/0db10e24-7e95-4673-adcb-94bac94a38a3

import Mathlib

set_option autoImplicit false

open Matrix

namespace N25

/-- Away from width-one cusps the triangularized first coordinate is divisible by five. -/
theorem _root_.solution
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : ℕ) (e v : ℤ)
    (hd : 0 < d) (he : 0 < e) (hde : (d : ℤ) * e = 25)
    (hm : !![25, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) ℤ) =
      (B : Matrix (Fin 2) (Fin 2) ℤ) * !![(d : ℤ), v; 0, e])
    (hA : ¬ (25 : ℤ) ∣ A 1 0) : (5 : ℤ) ∣ B 0 0 := by
  have h00 : 25 * A 0 0 = B 0 0 * (d : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 0 0) hm
  have h10 : A 1 0 = B 1 0 * (d : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 0) hm
  have hn : d * e.toNat = 25 := by
    have hh : (d : ℤ) * (e.toNat : ℤ) = 25 := by simpa [Int.toNat_of_nonneg he.le] using hde
    exact_mod_cast hh
  have hmem : d ∈ (25 : ℕ).divisors := Nat.mem_divisors.mpr ⟨⟨e.toNat, hn.symm⟩, by decide⟩
  have hs : (25 : ℕ).divisors = {1, 5, 25} := by decide +kernel
  rw [hs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · refine ⟨5 * A 0 0, ?_⟩
    norm_num at h00 ⊢
    omega
  · refine ⟨A 0 0, ?_⟩
    norm_num at h00 ⊢
    omega
  · exact False.elim (hA ⟨B 1 0, by norm_num at h10 ⊢; omega⟩)

end N25
