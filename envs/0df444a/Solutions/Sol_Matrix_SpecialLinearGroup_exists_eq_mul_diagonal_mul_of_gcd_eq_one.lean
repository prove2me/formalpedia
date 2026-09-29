-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6746b6bf-ecd5-5ff9-bc35-1d12e96aca37

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one

namespace Matrix
p2m_export "Matrix" "ext diag SpecialLinearGroup det_fin_two_of of mul_fin_two"
namespace SpecialLinearGroup
p2m_export "Matrix.SpecialLinearGroup" "ext"
namespace PrimitiveSmith
p2m_open "Matrix.SpecialLinearGroup Matrix"

theorem exists_coprime_mul_add {a b d : ℕ} (hd : d ≠ 0) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ p : ℕ, Nat.Coprime (a * p + b) d := by
  classical

  refine ⟨∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ b), q, ?_⟩
  set P := ∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ b), q with hP
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro q hq hqd hqab
  have hqP : q ∣ P ↔ ¬ q ∣ b := by
    rw [hP]
    first
      | rw [Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hq)]
      | rw [Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hq)]
    constructor
    · rintro ⟨q', hq', hqq'⟩
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq'
      obtain ⟨⟨hq'p, -, -⟩, hq'b⟩ := hq'
      rwa [(Nat.prime_dvd_prime_iff_eq hq hq'p).mp hqq']
    · intro hqb
      exact ⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqd, hd⟩, hqb⟩, dvd_rfl⟩
  by_cases hqb : q ∣ b
  ·
    have hqa : ¬ q ∣ a := by
      intro hqa
      have : q ∣ Nat.gcd a (Nat.gcd b d) := Nat.dvd_gcd hqa (Nat.dvd_gcd hqb hqd)
      rw [hgcd] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp this)
    have hqaP : q ∣ a * P := (Nat.dvd_add_right hqb).mp (by rwa [add_comm] at hqab)
    rcases (Nat.Prime.dvd_mul hq).mp hqaP with h | h
    · exact hqa h
    · exact (hqP.mp h) hqb
  ·
    have hqP' : q ∣ a * P := Dvd.dvd.mul_left (hqP.mpr hqb) a
    exact hqb ((Nat.dvd_add_right hqP').mp hqab)

theorem main {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1]
        * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hd : d ≠ 0 := fun h0 => hN (by rw [← had, h0, mul_zero])
  obtain ⟨p, hp⟩ := exists_coprime_mul_add hd hgcd

  set u : ℤ := (a : ℤ) * p + b with hu
  have hcop : IsCoprime u (d : ℤ) := by
    rw [hu]
    have : ((a * p + b : ℕ) : ℤ) = (a : ℤ) * p + b := by push_cast; ring
    rw [← this, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hp
  obtain ⟨s, t, hst⟩ := hcop

  have hN' : (N : ℤ) = a * d := by exact_mod_cast had.symm
  refine ⟨⟨!![-t, -u; s, -(d : ℤ)], ?_⟩, ⟨!![-1, (p : ℤ); -s * a, (p : ℤ) * s * a - 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hst
  · rw [Matrix.det_fin_two_of]
    ring
  ·
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hN']
    ext i j
    fin_cases i <;> fin_cases j
    · simp
      linear_combination (-(a : ℤ)) * hst + ((a : ℤ) * s) * hu
    · simp
      linear_combination ((a : ℤ) * p) * hst - ((a : ℤ) * p * s) * hu
    · simp
      ring
    · simp
      ring

end Matrix.SpecialLinearGroup.PrimitiveSmith

theorem solution
    {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) :=
  Matrix.SpecialLinearGroup.PrimitiveSmith.main hN had hgcd

end S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one (solution)
