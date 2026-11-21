-- Prove2me | solution 1 for KhintchineTwoRegime.haagerupF_increasing
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:29:42.248179+00:00
-- url     : https://prove2.me/submissions/15d5f5d9-1acf-4cf8-a42e-82d974c3656c

import Mathlib
import Definitions.Def_KhintchineTwoRegime_haagerupF

namespace KhintchineTwoRegime

private noncomputable def rAux (x : ℝ) : ℝ :=
  Real.Gamma (x + 1 / 2) ^ 2 / (Real.Gamma x * Real.Gamma (x + 1))

private noncomputable def qAux (t : ℝ) : ℝ :=
  t * (t + 1) / (t + 1 / 2) ^ 2

private noncomputable def rSeqAux (x : ℝ) (n : ℕ) : ℝ :=
  Real.GammaSeq (x + 1 / 2) n ^ 2 /
    (Real.GammaSeq x n * Real.GammaSeq (x + 1) n)

private lemma rSeq_algebra {A B C f a b c : ℝ}
    (hA : A ^ 2 = B * C) (hB : B ≠ 0) (hC : C ≠ 0)
    (hf : f ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (A * f / b) ^ 2 / (B * f / a * (C * f / c)) = a * c / (b * b) := by
  rw [div_pow, mul_pow, hA]
  field_simp [hB, hC, hf, ha, hb, hc] <;> ring

private lemma rpow_sq_factor {N x : ℝ} (hN : 0 < N) :
    (N ^ (x + 1 / 2)) ^ 2 = N ^ x * N ^ (x + 1) := by
  calc
    (N ^ (x + 1 / 2)) ^ 2 = (N ^ (x + 1 / 2)) ^ (2 : ℝ) := by
      simpa using (Real.rpow_natCast (N ^ (x + 1 / 2)) 2).symm
    _ = N ^ ((x + 1 / 2) * (2 : ℝ)) := by
      symm
      exact Real.rpow_mul hN.le _ _
    _ = N ^ (x + (x + 1)) := by
      congr 1
      ring
    _ = N ^ x * N ^ (x + 1) := Real.rpow_add hN x (x + 1)

private lemma prod_shift_pos {z : ℝ} (hz : 0 < z) (n : ℕ) :
    0 < ∏ j ∈ Finset.range (n + 1), (z + (j : ℝ)) := by
  apply Finset.prod_pos
  intro j hj
  have hj0 : 0 ≤ (j : ℝ) := by positivity
  linarith

private lemma rSeqAux_eq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    rSeqAux x n = ∏ k ∈ Finset.range (n + 1), qAux (x + (k : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hN : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hpow : ((n : ℝ) ^ (x + 1 / 2)) ^ 2 =
      (n : ℝ) ^ x * (n : ℝ) ^ (x + 1) :=
    rpow_sq_factor hN
  have hPx := prod_shift_pos hx n
  have hPh := prod_shift_pos (z := x + 1 / 2) (by linarith) n
  have hP1 := prod_shift_pos (z := x + 1) (by linarith) n
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hprod :
      (∏ k ∈ Finset.range (n + 1), qAux (x + (k : ℝ))) =
        ((∏ j ∈ Finset.range (n + 1), (x + (j : ℝ))) *
          (∏ j ∈ Finset.range (n + 1), (x + 1 + (j : ℝ)))) /
        ((∏ j ∈ Finset.range (n + 1), (x + 1 / 2 + (j : ℝ))) *
          (∏ j ∈ Finset.range (n + 1), (x + 1 / 2 + (j : ℝ)))) := by
    have h₁ (k : ℕ) : x + (k : ℝ) + 1 = x + 1 + (k : ℝ) := by
      ring
    have h₂ (k : ℕ) :
        x + (k : ℝ) + 1 / 2 = x + 1 / 2 + (k : ℝ) := by
      ring
    simp only [qAux, pow_two]
    simp_rw [h₁, h₂]
    simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  unfold rSeqAux
  simp only [Real.GammaSeq]
  rw [hprod]
  exact rSeq_algebra hpow
    (Real.rpow_pos_of_pos hN x).ne'
    (Real.rpow_pos_of_pos hN (x + 1)).ne'
    hf hPx.ne' hPh.ne' hP1.ne'

private lemma qAux_pos {t : ℝ} (ht : 0 < t) : 0 < qAux t := by
  unfold qAux
  exact div_pos (mul_pos ht (by linarith)) (sq_pos_of_pos (by linarith))

private lemma qAux_strict {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    qAux x < qAux y := by
  have hy : 0 < y := hx.trans hxy
  have hax : 0 < x + 1 / 2 := by linarith
  have hay : 0 < y + 1 / 2 := by linarith
  unfold qAux
  apply (div_lt_div_iff₀ (sq_pos_of_pos hax) (sq_pos_of_pos hay)).2
  have hp : 0 < (y - x) * (x + y + 1) :=
    mul_pos (sub_pos.mpr hxy) (by linarith)
  nlinarith [hp]

private lemma qAux_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    qAux x ≤ qAux y := by
  rcases hxy.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (qAux_strict hx h).le

private lemma rSeqAux_tendsto {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (rSeqAux x) Filter.atTop (nhds (rAux x)) := by
  have hgx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hg1 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
  have htend : Filter.Tendsto
      (fun n => Real.GammaSeq (x + 1 / 2) n ^ 2 /
        (Real.GammaSeq x n * Real.GammaSeq (x + 1) n))
      Filter.atTop (nhds (Real.Gamma (x + 1 / 2) ^ 2 /
        (Real.Gamma x * Real.Gamma (x + 1)))) :=
    ((Real.GammaSeq_tendsto_Gamma (x + 1 / 2)).pow 2).div
      ((Real.GammaSeq_tendsto_Gamma x).mul
        (Real.GammaSeq_tendsto_Gamma (x + 1)))
      (mul_ne_zero hgx.ne' hg1.ne')
  change Filter.Tendsto
    (fun n : ℕ => Real.GammaSeq (x + 1 / 2) n ^ 2 /
      (Real.GammaSeq x n * Real.GammaSeq (x + 1) n))
    Filter.atTop
    (nhds (Real.Gamma (x + 1 / 2) ^ 2 /
      (Real.Gamma x * Real.Gamma (x + 1))))
  exact htend

private lemma rAux_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    rAux x ≤ rAux y := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  refine le_of_tendsto_of_tendsto (rSeqAux_tendsto hx) (rSeqAux_tendsto hy) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  rw [rSeqAux_eq hx hn, rSeqAux_eq hy hn]
  refine Finset.prod_le_prod (fun k hk => ?_) (fun k hk => ?_)
  · have hk0 : 0 ≤ (k : ℝ) := by positivity
    exact (qAux_pos (by linarith)).le
  · have hk0 : 0 ≤ (k : ℝ) := by positivity
    exact qAux_mono (by linarith) (by linarith)

private lemma rAux_pos {x : ℝ} (hx : 0 < x) : 0 < rAux x := by
  unfold rAux
  exact div_pos
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)))
    (mul_pos (Real.Gamma_pos_of_pos hx)
      (Real.Gamma_pos_of_pos (by linarith)))

private lemma rAux_eq_q_mul {x : ℝ} (hx : 0 < x) :
    rAux x = qAux x * rAux (x + 1) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hx1 : x + 1 ≠ 0 := by linarith
  have ha : x + 1 / 2 ≠ 0 := by linarith
  have hg : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  unfold rAux qAux
  rw [show x + 1 + 1 / 2 = (x + 1 / 2) + 1 by ring]
  rw [Real.Gamma_add_one ha]
  rw [show x + 1 + 1 = (x + 1) + 1 by ring]
  rw [Real.Gamma_add_one hx1]
  rw [Real.Gamma_add_one hx0]
  field_simp [hx0, hx1, ha, hg] <;> ring

private lemma rAux_strict {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    rAux x < rAux y := by
  have hy : 0 < y := hx.trans hxy
  have hq : qAux x < qAux y := qAux_strict hx hxy
  have hR : rAux (x + 1) ≤ rAux (y + 1) :=
    rAux_mono (x := x + 1) (y := y + 1) (by linarith) (by linarith)
  have hRpos : 0 < rAux (x + 1) := rAux_pos (by linarith)
  have hqy : 0 < qAux y := qAux_pos hy
  rw [rAux_eq_q_mul hx, rAux_eq_q_mul hy]
  calc
    qAux x * rAux (x + 1) < qAux y * rAux (x + 1) :=
      mul_lt_mul_of_pos_right hq hRpos
    _ ≤ qAux y * rAux (y + 1) :=
      mul_le_mul_of_nonneg_left hR hqy.le

private lemma haagerup_algebra {r p s G H : ℝ}
    (hr : r ≠ 0) (hp : p ≠ 0) (hs : s ≠ 0) (hG : G ≠ 0)
    (hrs : r ^ 2 = p * s) :
    (2 / r * (H / G)) ^ 2 =
      (2 / p) * (H ^ 2 / (G * (s / 2 * G))) := by
  calc
    (2 / r * (H / G)) ^ 2 = 4 * H ^ 2 / (r ^ 2 * G ^ 2) := by
      field_simp [hr, hG] <;> ring
    _ = 4 * H ^ 2 / ((p * s) * G ^ 2) := by rw [hrs]
    _ = (2 / p) * (H ^ 2 / (G * (s / 2 * G))) := by
      field_simp [hp, hs, hG] <;> ring

private lemma haagerupF_sq {s : ℝ} (hs : 0 < s) :
    (haagerupF s) ^ 2 = (2 / Real.pi) * rAux (s / 2) := by
  have hspos : 0 < Real.pi * s := mul_pos Real.pi_pos hs
  have hsqrt : 0 < Real.sqrt (Real.pi * s) := Real.sqrt_pos.2 hspos
  have hsq : (Real.sqrt (Real.pi * s)) ^ 2 = Real.pi * s :=
    Real.sq_sqrt hspos.le
  have hg : Real.Gamma (s / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < s / 2)).ne'
  unfold haagerupF rAux
  rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring]
  rw [Real.Gamma_add_one (show s / 2 ≠ 0 by linarith)]
  exact haagerup_algebra hsqrt.ne' Real.pi_ne_zero hs.ne' hg hsq

private lemma haagerupF_pos {s : ℝ} (hs : 0 < s) : 0 < haagerupF s := by
  unfold haagerupF
  have hsqrt : 0 < Real.sqrt (Real.pi * s) :=
    Real.sqrt_pos.2 (mul_pos Real.pi_pos hs)
  exact mul_pos (div_pos (by norm_num) hsqrt)
    (div_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos (by linarith)))

private lemma gamma_two : Real.Gamma (2 : ℝ) = 1 := by
  calc
    Real.Gamma (2 : ℝ) = Real.Gamma (1 + 1) := by norm_num
    _ = (1 : ℝ) * Real.Gamma 1 := Real.Gamma_add_one (by norm_num)
    _ = 1 := by rw [Real.Gamma_one]; norm_num

private lemma gamma_five_halves :
    Real.Gamma (5 / 2 : ℝ) = 3 / 4 * Real.sqrt Real.pi := by
  have hG52 : Real.Gamma (5 / 2 : ℝ) =
      (3 / 2 : ℝ) * Real.Gamma (3 / 2 : ℝ) := by
    convert Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hG32 : Real.Gamma (3 / 2 : ℝ) =
      (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) := by
    convert Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  rw [hG52, hG32]
  rw [show Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi by
    simpa using Real.Gamma_one_half_eq]
  ring

private lemma sqrt_pi_mul_four :
    Real.sqrt (Real.pi * 4) = 2 * Real.sqrt Real.pi := by
  have hsq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  calc
    Real.sqrt (Real.pi * 4) = Real.sqrt ((2 * Real.sqrt Real.pi) ^ 2) := by
      congr 1
      rw [mul_pow, hsq]
      ring
    _ = 2 * Real.sqrt Real.pi := Real.sqrt_sq (by positivity)

private lemma haagerupF_four : haagerupF 4 = 3 / 4 := by
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  unfold haagerupF
  rw [show (4 + 1 : ℝ) / 2 = 5 / 2 by norm_num,
    show (4 : ℝ) / 2 = 2 by norm_num,
    gamma_five_halves, gamma_two, sqrt_pi_mul_four]
  field_simp [hsp.ne'] <;> ring

theorem _root_.solution :
    StrictMonoOn haagerupF (Set.Ioi 0) ∧ haagerupF 4 = 3 / 4 := by
  refine ⟨?_, haagerupF_four⟩
  intro s hs t ht hst
  have hs0 : 0 < s := by simpa using hs
  have ht0 : 0 < t := by simpa using ht
  have hR : rAux (s / 2) < rAux (t / 2) :=
    rAux_strict (x := s / 2) (y := t / 2) (by linarith) (by linarith)
  have hsquare : (haagerupF s) ^ 2 < (haagerupF t) ^ 2 := by
    rw [haagerupF_sq hs0, haagerupF_sq ht0]
    exact mul_lt_mul_of_pos_left hR (div_pos (by norm_num) Real.pi_pos)
  have hFs : 0 < haagerupF s := haagerupF_pos hs0
  have hFt : 0 < haagerupF t := haagerupF_pos ht0
  by_contra hnot
  have hle : haagerupF t ≤ haagerupF s := le_of_not_gt hnot
  have hprod : 0 ≤ (haagerupF s - haagerupF t) *
      (haagerupF s + haagerupF t) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_pos hFs hFt).le
  nlinarith

end KhintchineTwoRegime
