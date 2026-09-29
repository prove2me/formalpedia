-- Prove2me | solution 1 for MTT.algebraicSymbol_horizontal_unitFiber_distribution
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-22T21:57:23.97158+00:00
-- url     : https://prove2.me/submissions/a29c4a9c-897f-460b-9258-af482f75b8d4

import Theorems.Thm_MTT_algebraicSymbol_horizontal_distribution

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
/-- Removing the unique lift divisible by `ℓ` from the arbitrary-denominator
symbol distribution relation gives the coefficientwise horizontal norm
relation at the central exponent. -/
theorem _root_.solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι) (P : Periods k ι f.form)
    (s : Bool) (j : ℕ) (hj : j ≤ k - 2) (hcentral : 2 * j = k - 2)
    (ℓ q : ℕ) (hℓ : ℓ.Prime) (hq : 0 < q) (hcop : Nat.Coprime ℓ q)
    (a c b₀ : ℕ) (hb₀ : b₀ < ℓ) (hlift : a + b₀ * q = ℓ * c) :
    (∑ b ∈ (Finset.range ℓ).erase b₀,
      algebraicSymbol P s j
          ((a : ℚ) + (b : ℚ) * (q : ℚ)) ((ℓ : ℚ) * (q : ℚ)) /
        ((ℓ : Qbar) * (q : Qbar)) ^ j) =
      f.coeff ℓ / (ℓ : Qbar) ^ j *
          (algebraicSymbol P s j (a : ℚ) (q : ℚ) / (q : Qbar) ^ j) -
        algebraicSymbol P s j (c : ℚ) (q : ℚ) / (q : Qbar) ^ j -
        f.epsilon ℓ *
          (algebraicSymbol P s j ((ℓ : ℚ) * (a : ℚ)) (q : ℚ) /
            (q : Qbar) ^ j) := by
  have hlQ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hlK : (ℓ : Qbar) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hqK : (q : Qbar) ≠ 0 := by exact_mod_cast hq.ne'
  have hscale : algebraicSymbol P s j ((ℓ : ℚ) * c) ((ℓ : ℚ) * q) =
      (ℓ : Qbar)^j * algebraicSymbol P s j (c : ℚ) (q : ℚ) := by
    have harg : -((ℓ : ℚ) * c) / ((ℓ : ℚ) * q) = -(c : ℚ) / q := by
      field_simp
    simp only [algebraicSymbol, harg, Finset.mul_sum, Rat.cast_mul, Rat.cast_natCast,
      mul_pow]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htj : t ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hexp : (ℓ : Qbar)^t * (ℓ : Qbar)^(j-t) = (ℓ : Qbar)^j := by
      rw [← pow_add, Nat.add_sub_of_le htj]
    linear_combination (j.choose t : Qbar) * (q : Qbar)^t * (c : Qbar)^(j-t) *
      P.value s t (-(c : ℚ) / q) * hexp
  have hliftQ : (a : ℚ) + (b₀ : ℚ) * q = (ℓ : ℚ) * c := by
    exact_mod_cast hlift
  have hdist := MTT.algebraicSymbol_horizontal_distribution hN hk ι f P s j hj
    ℓ q hℓ hq (a : ℤ)
  simp only [Int.cast_natCast] at hdist
  have herase := Finset.sum_erase_add (Finset.range ℓ)
    (fun b : ℕ => algebraicSymbol P s j ((a : ℚ) + (b : ℚ) * q) ((ℓ : ℚ) * q))
    (Finset.mem_range.mpr hb₀)
  rw [hliftQ, hscale, hdist] at herase
  have hjexp : k - 2 - j = j := by omega
  rw [hjexp] at herase
  rw [← Finset.sum_div]
  rw [mul_pow]
  field_simp
  linear_combination (norm := skip) herase
  simp only [mul_comm (q : ℚ) (ℓ : ℚ), mul_comm (a : ℚ) (ℓ : ℚ)]
  ring
