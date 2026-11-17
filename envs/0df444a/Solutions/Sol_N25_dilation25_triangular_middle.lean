-- Prove2me | solution 1 for N25.dilation25_triangular_middle
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:33.291458+00:00
-- url     : https://prove2.me/submissions/74c817a3-e857-4332-b256-3162cb0b8b42

import Mathlib

set_option autoImplicit false

open Matrix

namespace N25

/-- At a width-five direction the dilation has equal diagonal entries and a nontrivial translation. -/
theorem _root_.solution
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : ℕ) (e v : ℤ)
    (he : 0 < e) (hde : (d : ℤ) * e = 25)
    (hm : !![25, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) ℤ) =
      (B : Matrix (Fin 2) (Fin 2) ℤ) * !![(d : ℤ), v; 0, e])
    (hA5 : (5 : ℤ) ∣ A 1 0) (hA25 : ¬ (25 : ℤ) ∣ A 1 0) :
    d = 5 ∧ e = 5 ∧ ¬ (5 : ℤ) ∣ v := by
  have h00 : 25 * A 0 0 = B 0 0 * (d : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 0 0) hm
  have h10 : A 1 0 = B 1 0 * (d : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 0) hm
  have h11 : A 1 1 = B 1 0 * v + B 1 1 * e := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 1) hm
  have hdetA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hdetB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.property
  have hn : d * e.toNat = 25 := by
    have hh : (d : ℤ) * (e.toNat : ℤ) = 25 := by simpa [Int.toNat_of_nonneg he.le] using hde
    exact_mod_cast hh
  have hmem : d ∈ (25 : ℕ).divisors := Nat.mem_divisors.mpr ⟨⟨e.toNat, hn.symm⟩, by decide⟩
  have hs : (25 : ℕ).divisors = {1, 5, 25} := by decide +kernel
  rw [hs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hd : d = 5 := by
    rcases hmem with rfl | hd | rfl
    · norm_num at h00 h10
      have hb00 : (5 : ℤ) ∣ B 0 0 := ⟨5 * A 0 0, by omega⟩
      have hb10 : (5 : ℤ) ∣ B 1 0 := by simpa [h10] using hA5
      have hbad : (5 : ℤ) ∣ 1 := by
        rw [← hdetB]
        exact dvd_sub (dvd_mul_of_dvd_left hb00 _) (dvd_mul_of_dvd_right hb10 _)
      norm_num at hbad
    · exact hd
    · exact False.elim (hA25 ⟨B 1 0, by norm_num at h10 ⊢; omega⟩)
  have he5 : e = 5 := by rw [hd] at hde; norm_num at hde; omega
  refine ⟨hd, he5, ?_⟩
  intro hv
  have ha11 : (5 : ℤ) ∣ A 1 1 := by
    rw [h11, he5]
    exact dvd_add (dvd_mul_of_dvd_right hv _) (dvd_mul_left _ _)
  have hbad : (5 : ℤ) ∣ 1 := by
    rw [← hdetA]
    exact dvd_sub (dvd_mul_of_dvd_right ha11 _) (dvd_mul_of_dvd_right hA5 _)
  norm_num at hbad

end N25
