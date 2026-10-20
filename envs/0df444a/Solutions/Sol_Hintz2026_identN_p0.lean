-- Prove2me | solution 1 for Hintz2026.identN_p0
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:24:27.267204+00:00
-- url     : https://prove2.me/submissions/cf6a96fc-80b7-4be3-a80a-5c31a4914b3e

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_Dp_g1N

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) : Dp p (fun z => yNeg p (-1) G z 0) x + (A p x *ᵥ yNeg p (-1) G x) 0 - ((cscalar p (-1) om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p (-1) om mm x) *ᵥ yNeg p 1 G x) 0 = ↑(preNeg p x) * (I * res1aN p om mm G x + ↑(Real.sqrt (Del p (x 0))) * res1bN p om mm G x) :=
  by
    have hy : (fun z => yNeg p (-1) G z 0) = fun z => ↑(preNeg p z) * g1N p (-1) G z := by funext z; exact yNeg_0 p (-1) G z
    rw [hy, Dp_preNeg_mul p hx _ (diff_g1N_slice p (-1) hx hG), Dp_g1N p (-1) hx hG,
      mulVec_entry0, mulVec_entry0, cIaddB_00, cIaddB_01, A_00, A_01, B_00, B_01, yNeg_0, yNeg_1, yNeg_0, yNeg_1]
    unfold res1aN res1bN Dop DopDag Lop LopDag threeIaSin threeOverRhoStar Fplus Fminus lamNegP cscalar bcoeff Qhat cotR Kfreq Del' g1N g2N
    simp only [cpd_neg]
    unfold Dp
    have hD : 0 < Del p (x 0) := Del_pos p hx.1
    have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
    have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
    have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
    have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
    have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
    have hpre : (↑(preNeg p x) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hx).ne'
    have hrr : rhoBar p x = ↑(x 0) + ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBar_eq_ofReal]; push_cast; ring
    have hrrs : rhoBarStar p x = ↑(x 0) - ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBarStar_eq_ofReal]; push_cast; ring
    have htrig : (↑(Real.sin (x 1)) : ℂ) ^ 2 + (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.sin_sq_add_cos_sq]; rfl
    have hcos2 : (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 - (↑(Real.sin (x 1)) : ℂ) ^ 2 := by linear_combination htrig
    have hs3 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 3 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) := by rw [pow_succ, hsq, mul_comm]
    have hs4 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 4 = ↑(Del p (x 0)) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq]
    have hs5 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 5 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) ^ 2 := by rw [pow_succ, hs4, mul_comm]
    have hs6 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 6 = ↑(Del p (x 0)) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hsq]
    have hc3 : (↑(Real.cos (x 1)) : ℂ) ^ 3 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) := by rw [pow_succ, hcos2, mul_comm]
    have hc4 : (↑(Real.cos (x 1)) : ℂ) ^ 4 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hcos2]
    have hc5 : (↑(Real.cos (x 1)) : ℂ) ^ 5 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [pow_succ, hc4, mul_comm]
    have hc6 : (↑(Real.cos (x 1)) : ℂ) ^ 6 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hcos2]
    have hI5 : (I : ℂ) ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]
    have hI6 : (I : ℂ) ^ 6 = -1 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, I_sq]; norm_num
    have hI7 : (I : ℂ) ^ 7 = -I := by rw [pow_succ, hI6]; ring
    have hI8 : (I : ℂ) ^ 8 = 1 := by rw [show (8:ℕ) = 4*2 from rfl, pow_mul, I_pow_four, one_pow]
    push_cast at *
    field_simp [hr, hrs, hDne, hsD, hs, hQ, hpre]
    rw [hrr, hrrs]
    ring_nf
    simp only [hsq, hs3, hs4, hs5, hs6, hcos2, hc3, hc4, hc5, hc6, I_sq, I_pow_three, I_pow_four, hI5, hI6, hI7, hI8]
    simp only [Del]
    push_cast
    ring_nf

end
