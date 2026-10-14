-- Prove2me | solution 1 for IntMul.HvdH.bluestein
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:56:52.56309+00:00
-- url     : https://prove2.me/submissions/f41d67e3-9dd1-4697-b715-ee2f23047f25

import Mathlib

open Complex

namespace IntMul.HvdH.Blue

/-- The chirp `m ↦ e^{Real.pi i m² / t}` on integers. -/
noncomputable def chirp (t : ℕ) (m : ℤ) : ℂ := cexp (Real.pi * I * (m : ℂ) ^ 2 / t)

lemma chirp_periodic (t : ℕ) (ht : Even t) (n q : ℤ) : chirp t (n + q * t) = chirp t n := by
  obtain ⟨s, hs⟩ := ht
  unfold chirp
  rcases eq_or_ne t 0 with h0 | h0
  · simp [h0]
  have hs0 : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := by omega
    exact_mod_cast this
  have e : Real.pi * I * (((n + q * t : ℤ)) : ℂ) ^ 2 / t =
      Real.pi * I * (n : ℂ) ^ 2 / t + ((n * q + q ^ 2 * s : ℤ) : ℂ) * (2 * Real.pi * I) := by
    subst hs; push_cast; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma conj_chirp (t : ℕ) (m : ℤ) :
    (starRingEnd ℂ) (chirp t m) = cexp (-(Real.pi * I * (m : ℂ) ^ 2 / t)) := by
  unfold chirp
  rw [← Complex.exp_conj]
  congr 1
  simp [map_div₀]; ring

/-- One-dimensional Bluestein identity: `e^{-2Real.pii jk/t} = ā_j a_{j-k} ā_k` for even `t`. -/
lemma stdAddChar_bluestein (t : ℕ) [NeZero t] (ht : Even t) (j k : ZMod t) :
    (ZMod.stdAddChar (-(j * k)) : ℂ) = (starRingEnd ℂ) (chirp t j.val) *
      chirp t ((j - k).val) * (starRingEnd ℂ) (chirp t k.val) := by
  have e1 : -(j * k) = ((-((j.val : ℤ) * k.val) : ℤ) : ZMod t) := by
    push_cast; simp
  obtain ⟨q, hq⟩ : (t : ℤ) ∣ (((j - k).val : ℤ) - ((j.val : ℤ) - k.val)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; simp
  have e2 : (((j - k).val : ℕ) : ℤ) = ((j.val : ℤ) - k.val) + q * t := by linarith
  rw [e1, ZMod.stdAddChar_coe, e2, chirp_periodic t ht, conj_chirp, conj_chirp]
  unfold chirp
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  push_cast; field_simp; ring

/-- **Bluestein's identity** in `d` dimensions (Harvey–van der Hoeven (3.2)). -/
theorem bluestein {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)] (ht : ∀ i, Even (t i))
    (u : ((i : Fin d) → ZMod (t i)) → ℂ) (j : (i : Fin d) → ZMod (t i)) :
    ∑ k, (∏ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ)) * u k =
      (starRingEnd ℂ) (∏ i, cexp (Real.pi * I * ((j i).val : ℂ) ^ 2 / t i)) *
        ∑ k, (∏ i, cexp (Real.pi * I * (((j i - k i).val : ℕ) : ℂ) ^ 2 / t i)) *
          ((starRingEnd ℂ) (∏ i, cexp (Real.pi * I * ((k i).val : ℂ) ^ 2 / t i)) * u k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h : ∀ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ) =
      (starRingEnd ℂ) (cexp (Real.pi * I * ((j i).val : ℂ) ^ 2 / t i)) *
        cexp (Real.pi * I * (((j i - k i).val : ℕ) : ℂ) ^ 2 / t i) *
          (starRingEnd ℂ) (cexp (Real.pi * I * ((k i).val : ℂ) ^ 2 / t i)) := by
    intro i
    have := stdAddChar_bluestein (t i) (ht i) (j i) (k i)
    simpa [chirp] using this
  simp only [h, Finset.prod_mul_distrib, map_prod]
  ring

end IntMul.HvdH.Blue

theorem solution {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)] (ht : ∀ i, Even (t i))
    (u : ((i : Fin d) → ZMod (t i)) → ℂ) (j : (i : Fin d) → ZMod (t i)) :
    ∑ k, (∏ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ)) * u k =
      (starRingEnd ℂ) (∏ i, Complex.exp (Real.pi * Complex.I * ((j i).val : ℂ) ^ 2 / t i)) *
        ∑ k, (∏ i, Complex.exp (Real.pi * Complex.I * (((j i - k i).val : ℕ) : ℂ) ^ 2 / t i)) *
          ((starRingEnd ℂ) (∏ i, Complex.exp (Real.pi * Complex.I * ((k i).val : ℂ) ^ 2 / t i)) * u k) :=
  IntMul.HvdH.Blue.bluestein t ht u j
