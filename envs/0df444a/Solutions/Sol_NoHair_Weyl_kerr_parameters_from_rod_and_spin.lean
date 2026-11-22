-- Prove2me | solution 1 for NoHair.Weyl.kerr_parameters_from_rod_and_spin
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:21:00.158232+00:00
-- url     : https://prove2.me/submissions/98074155-4b1d-40a3-99fc-fb122f876f8c

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (ℓ J : ℝ) (hℓ : 0 ≤ ℓ) (hn : 0 < ℓ ∨ J ≠ 0) :
    ∃! q : ℝ × ℝ, 0 < q.1 ∧ q.1 ^ 2 - q.2 ^ 2 = ℓ ^ 2 ∧ q.1 * q.2 = J := by
  let d := Real.sqrt ((ℓ^2)^2 + 4*J^2)
  have hdisc : 0 < (ℓ^2)^2 + 4*J^2 := by
    rcases hn with h | h
    · positivity
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (ℓ^2)]
  have hd : 0 < d := Real.sqrt_pos.2 hdisc
  have hd2 : d^2 = (ℓ^2)^2 + 4*J^2 := Real.sq_sqrt hdisc.le
  let x := (ℓ^2+d)/2
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hx : x^2 - ℓ^2*x = J^2 := by dsimp [x]; nlinarith only [hd2]
  let m := Real.sqrt x
  let a := J/m
  have hm : 0 < m := Real.sqrt_pos.2 hxpos
  have hm2 : m^2 = x := Real.sq_sqrt hxpos.le
  have hJ : m*a = J := by dsimp [a]; rw [mul_comm]; exact div_mul_cancel₀ _ hm.ne'
  have hprod : m^2 * (m^2 - a^2 - ℓ^2) = 0 := by
    calc
      _ = (m^2)^2 - ℓ^2*m^2 - (m*a)^2 := by ring
      _ = 0 := by rw [hm2, hJ, hx]; ring
  have hrod : m^2 - a^2 = ℓ^2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hm.ne'))
  refine ⟨(m,a), ⟨hm,hrod,hJ⟩, ?_⟩
  rintro ⟨n,b⟩ ⟨hnpos, hnrod, hnj⟩
  change 0 < n at hnpos
  change n^2 - b^2 = ℓ^2 at hnrod
  change n*b = J at hnj
  have energy (k t : ℝ) (hr : k^2 - t^2 = ℓ^2) (hj : k*t = J) :
      (k^2)^2 - k^2*ℓ^2 = J^2 := by rw [← hr, ← hj]; ring
  have hfactor : (n^2-m^2)*(n^2+m^2-ℓ^2) = 0 := by
    nlinarith only [energy n b hnrod hnj, energy m a hrod hJ]
  have hsum : 0 < n^2 + m^2 - ℓ^2 := by nlinarith [sq_pos_of_pos hnpos, sq_nonneg a]
  have hsquares := (mul_eq_zero.mp hfactor).resolve_right hsum.ne'
  have hnm : n = m := by
    apply (mul_self_inj_of_nonneg hnpos.le hm.le).mp
    nlinarith only [hsquares]
  subst n
  have hba := mul_left_cancel₀ hm.ne' (hnj.trans hJ.symm)
  exact Prod.ext rfl hba
