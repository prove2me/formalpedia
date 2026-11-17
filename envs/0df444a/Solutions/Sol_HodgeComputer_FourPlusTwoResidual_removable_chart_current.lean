-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.removable_chart_current
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T06:54:30.681552+00:00
-- url     : https://prove2.me/submissions/d23756c1-54ba-4359-9f2f-813c59b22419

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    {K : Type*} [Field K] [CharZero K]
    (Dt Dr Ds : Derivation ℤ K K)
    (p : Fin 4 → K) (t b c : K)
    (ht_t : Dt t = 1) (ht_r : Dr t = 0) (ht_s : Ds t = 0)
    (hp_t : ∀ j : Fin 4, Dt (p j) = 0)
    (hp0_s : Ds (p 0) = 0) (hp3_r : Dr (p 3) = 0)
    (ha0_t : Dt ((1 / 3 : K) * (Dr b + p 3 * Ds c + (1 / 3 : K) * Ds (p 3) * c)) = 0) :
    let a0 : K := (1 / 3 : K) * (Dr b + p 3 * Ds c + (1 / 3 : K) * Ds (p 3) * c);
    let qt : K := a0 * t;
    let qr : K := b;
    let qs : K := p 3 * c;
    let Pt : K := p 0 + p 1 * t ^ 2 + p 2 * t ^ 4 + p 3 * t ^ 6;
    let divq := Dt qt + Dr qr + Ds qs;
    let qP := qt * Dt Pt + qr * Dr Pt + qs * Ds Pt;
    let s0 := (2 / 3 : K) * b * Dr (p 0) - (4 / 3 : K) * Dr b * p 0 -
      (10 / 9 : K) * c * p 0 * Ds (p 3) - (4 / 3 : K) * Ds c * p 0 * p 3;
    let s1 := (2 / 3 : K) * b * Dr (p 1) - (8 / 9 : K) * Dr b * p 1 -
      (26 / 27 : K) * c * p 1 * Ds (p 3) + (2 / 3 : K) * c * Ds (p 1) * p 3 -
      (8 / 9 : K) * Ds c * p 1 * p 3;
    let s2 := (2 / 3 : K) * b * Dr (p 2) - (4 / 9 : K) * Dr b * p 2 -
      (22 / 27 : K) * c * p 2 * Ds (p 3) + (2 / 3 : K) * c * Ds (p 2) * p 3 -
      (4 / 9 : K) * Ds c * p 2 * p 3;
    -(Pt * divq - (2 / 3 : K) * qP) = s0 + s1 * t ^ 2 + s2 * t ^ 4 := by
  intro a0 qt qr qs Pt divq qP s0 s1 s2
  have hdiv : divq = a0 + Dr b + Ds (p 3) * c + p 3 * Ds c := by
    dsimp only [divq, qt, qr, qs]
    rw [Derivation.leibniz, ha0_t, ht_t, Derivation.leibniz]
    simp only [smul_eq_mul, mul_one]
    ring
  have hDtP : Dt Pt = 2 * p 1 * t + 4 * p 2 * t ^ 3 + 6 * p 3 * t ^ 5 := by
    dsimp only [Pt]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, hp_t, ht_t, smul_eq_mul]
    ring
  have hDrP : Dr Pt = Dr (p 0) + Dr (p 1) * t ^ 2 + Dr (p 2) * t ^ 4 := by
    dsimp only [Pt]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, ht_r, hp3_r, smul_eq_mul]
    ring
  have hDsP : Ds Pt = Ds (p 1) * t ^ 2 + Ds (p 2) * t ^ 4 + Ds (p 3) * t ^ 6 := by
    dsimp only [Pt]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, hp0_s, ht_s, smul_eq_mul]
    ring
  dsimp only [qP]
  rw [hdiv, hDtP, hDrP, hDsP]
  dsimp only [Pt, qt, qr, qs, a0, s0, s1, s2]
  field_simp
  ring
