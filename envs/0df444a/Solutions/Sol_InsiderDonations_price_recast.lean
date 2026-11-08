-- Prove2me | solution 1 for InsiderDonations.price_recast
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:27:01.164199+00:00
-- url     : https://prove2.me/submissions/8e07bc86-571c-4495-ba6e-afe8e1378a56

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

open InsiderDonations in
theorem solution {m n : ℕ} (P : Params m n) (hP : P.Standing) (hτo : 0 < P.τo)
    (ω : Outcome m) :
    price (eqProfile P) (orderFlow P (eqProfile P) ω) =
      eta P * ω.1 + (1 - eta P) * P.vbar - lamStar P * ω.2.1 -
        (∑ i, (ω.2.2 i - P.ψbar)) / (2 * P.τo) := by
  obtain ⟨hm1, -, -, -, -, hσu, hσψ, hω0, -, -, -, hstd⟩ := hP
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hN : 0 < P.N := by unfold Params.N; positivity
  rw [lt_div_iff₀ (by positivity)] at hstd
  have harg : 0 < 4 * P.σv ^ 2 * P.A * P.B - m * P.N ^ 2 * P.σψ ^ 2 := by nlinarith
  have hL : 0 < lamStar P := by
    unfold lamStar
    exact div_pos (Real.sqrt_pos.mpr harg) (mul_pos (mul_pos (mul_pos two_pos hN) hσu) hτo)
  have hd : ∀ i, P.omega * donate (eqProfile P) i ω.1 (ω.2.2 i) =
      P.omega * ((P.vbar * P.A / (P.N * lamStar P * P.omega * P.τo) +
        P.ψbar / (2 * lamStar P * P.omega * P.τo)) +
        (-(P.A / (P.N * lamStar P * P.omega * P.τo)) -
          ((1 - P.τc) / P.τo - 1) / (lamStar P * P.omega)) * ω.1) +
      P.omega * (1 / (2 * lamStar P * P.omega * P.τo)) * ω.2.2 i := by
    intro i
    simp only [donate, eqProfile]
    ring
  have hs1 : ∑ i, P.omega * donate (eqProfile P) i ω.1 (ω.2.2 i) =
      (m : ℝ) * (P.omega * ((P.vbar * P.A / (P.N * lamStar P * P.omega * P.τo) +
        P.ψbar / (2 * lamStar P * P.omega * P.τo)) +
        (-(P.A / (P.N * lamStar P * P.omega * P.τo)) -
          ((1 - P.τc) / P.τo - 1) / (lamStar P * P.omega)) * ω.1)) +
      P.omega * (1 / (2 * lamStar P * P.omega * P.τo)) * ∑ i, ω.2.2 i := by
    rw [Finset.sum_congr rfl (fun i _ => hd i), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hs2 : ∑ j, trade (eqProfile P) j ω.1 =
      (n : ℝ) * (P.vbar * P.A / (P.N * lamStar P * P.τo) +
        -(P.A / (P.N * lamStar P * P.τo)) * ω.1) := by
    simp only [trade, eqProfile, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  simp only [price, orderFlow]
  rw [hs1, hs2]
  simp only [eqProfile, eta, alphaStar]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNdef : P.N = 1 + m + n := rfl
  have hAdef : P.A = (1 + m) * P.τo - m * (1 - P.τc) := rfl
  have hBdef : P.B = m * (1 - P.τc) + n * P.τo := rfl
  rw [hAdef, hBdef]
  rw [hNdef] at hN
  generalize lamStar P = L at hL ⊢
  generalize ∑ i, ω.2.2 i = S
  rw [hNdef]
  have hN' : (1 + (m : ℝ) + n) ≠ 0 := hN.ne'
  field_simp <;> ring
