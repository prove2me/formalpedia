-- Prove2me | solution 1 for KhintchineTwoRegime.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:40:14.75017+00:00
-- url     : https://prove2.me/submissions/e5c5aa1f-dd0e-4334-97be-a97774a89c99

import Mathlib
import Definitions.Def_KhintchineTwoRegime_haagerupF
import Definitions.Def_KhintchineTwoRegime_Cconst
import Definitions.Def_KhintchineTwoRegime_rFun

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

private noncomputable def dAux (x : ℝ) : ℝ :=
  (32 * x ^ 2 + 16 * x + 3) / (8 * x * (4 * x + 1))

private lemma dAux_eq_sum {x : ℝ} (hx : 0 < x) :
    dAux x = 1 + 1 / (4 * x) + 1 / (16 * x * (2 * x + 1 / 2)) := by
  have h4 : 4 * x + 1 ≠ 0 := by linarith
  have h2 : 2 * x + 1 / 2 ≠ 0 := by linarith
  unfold dAux
  field_simp [hx.ne', h4, h2] <;> ring

private lemma dAux_pos {x : ℝ} (hx : 0 < x) : 0 < dAux x := by
  have h4 : 0 < 4 * x + 1 := by linarith
  unfold dAux
  apply div_pos
  · nlinarith [sq_nonneg x]
  · exact mul_pos (by linarith) h4

private lemma dAux_one_le {x : ℝ} (hx : 0 < x) : 1 ≤ dAux x := by
  have h4 : 0 < 4 * x + 1 := by linarith
  have hden : 0 < 8 * x * (4 * x + 1) :=
    mul_pos (by linarith) h4
  unfold dAux
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg x]

private lemma qAux_mul_dAux {x : ℝ} (hx : 0 < x) :
    dAux (x + 1) ≤ qAux x * dAux x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hx1 : x + 1 ≠ 0 := by linarith
  have h4 : 4 * x + 1 ≠ 0 := by linarith
  have hhalf : x + 1 / 2 ≠ 0 := by linarith
  have h2 : 2 * x + 1 ≠ 0 := by linarith
  have hq : qAux x * dAux x =
      (x + 1) * (32 * x ^ 2 + 16 * x + 3) /
        (2 * (4 * x + 1) * (2 * x + 1) ^ 2) := by
    unfold qAux dAux
    field_simp [hx0, hx1, h4, hhalf, h2] <;> ring
  have hn : 32 * (x + 1) ^ 2 + 16 * (x + 1) + 3 =
      32 * x ^ 2 + 80 * x + 51 := by
    ring
  have hden : 8 * (x + 1) * (4 * (x + 1) + 1) =
      32 * x ^ 2 + 72 * x + 40 := by
    ring
  have hd : dAux (x + 1) =
      (32 * x ^ 2 + 80 * x + 51) / (32 * x ^ 2 + 72 * x + 40) := by
    unfold dAux
    rw [hn, hden]
  have h4pos : 0 < 4 * x + 1 := by linarith
  have h2pos : 0 < 2 * x + 1 := by linarith
  have hP : 0 < 2 * (4 * x + 1) * (2 * x + 1) ^ 2 :=
    mul_pos (mul_pos (by norm_num) h4pos) (sq_pos_of_pos h2pos)
  have hQ : 0 < 32 * x ^ 2 + 72 * x + 40 := by
    nlinarith [sq_nonneg x]
  rw [hd, hq]
  apply (div_le_div_iff₀ hQ hP).2
  have hcross :
      (32 * x ^ 2 + 80 * x + 51) *
          (2 * (4 * x + 1) * (2 * x + 1) ^ 2) + 18 =
        ((x + 1) * (32 * x ^ 2 + 16 * x + 3)) *
          (32 * x ^ 2 + 72 * x + 40) := by
    ring
  nlinarith [hcross]

private lemma dAux_mul_prod_ge {x : ℝ} (hx : 0 < x) (n : ℕ) :
    dAux (x + (n : ℝ)) ≤
      dAux x * ∏ k ∈ Finset.range n, qAux (x + (k : ℝ)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hxn : 0 < x + (n : ℝ) := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        linarith
      have hcast : x + ((n + 1 : ℕ) : ℝ) = (x + (n : ℝ)) + 1 := by
        push_cast
        ring
      calc
        dAux (x + ((n + 1 : ℕ) : ℝ)) = dAux ((x + (n : ℝ)) + 1) := by
          rw [hcast]
        _ ≤ qAux (x + (n : ℝ)) * dAux (x + (n : ℝ)) :=
          qAux_mul_dAux hxn
        _ ≤ qAux (x + (n : ℝ)) *
            (dAux x * ∏ k ∈ Finset.range n, qAux (x + (k : ℝ))) :=
          mul_le_mul_of_nonneg_left ih (qAux_pos hxn).le
        _ = dAux x * ∏ k ∈ Finset.range (n + 1), qAux (x + (k : ℝ)) := by
          rw [Finset.prod_range_succ]
          ring

private lemma one_le_dAux_mul_rSeqAux {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ dAux x * rSeqAux x n := by
  rw [rSeqAux_eq hx hn]
  have hxn : 0 < x + ((n + 1 : ℕ) : ℝ) := by
    have hn0 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  calc
    1 ≤ dAux (x + ((n + 1 : ℕ) : ℝ)) := dAux_one_le hxn
    _ ≤ dAux x * ∏ k ∈ Finset.range (n + 1), qAux (x + (k : ℝ)) :=
      dAux_mul_prod_ge hx (n + 1)

private lemma one_le_dAux_mul_rAux {x : ℝ} (hx : 0 < x) :
    1 ≤ dAux x * rAux x := by
  have ht : Filter.Tendsto (fun n : ℕ => dAux x * rSeqAux x n)
      Filter.atTop (nhds (dAux x * rAux x)) :=
    (rSeqAux_tendsto hx).const_mul (dAux x)
  refine ge_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact one_le_dAux_mul_rSeqAux hx hn

private lemma wallis_bound {s : ℝ} (hs : 0 < s) :
    Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2))) ≤
      haagerupF s := by
  have hx : 0 < s / 2 := by linarith
  have hbase :
      1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2)) = dAux (s / 2) := by
    rw [dAux_eq_sum hx]
    have h1 : 4 * (s / 2) = 2 * s := by ring
    have h2 : 16 * (s / 2) * (2 * (s / 2) + 1 / 2) =
        8 * s * (s + 1 / 2) := by ring
    rw [h1, h2]
  have hB : 0 < 1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2)) := by
    rw [hbase]
    exact dAux_pos hx
  have hp : 0 < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hCpos : 0 < Cconst := by
    unfold Cconst
    exact Real.sqrt_pos.2 hp
  have hCsq : Cconst ^ 2 = 2 / Real.pi := by
    unfold Cconst
    exact Real.sq_sqrt hp.le
  have hsqrtB : 0 < Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2))) :=
    Real.sqrt_pos.2 hB
  have hApos : 0 <
      Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2))) :=
    div_pos hCpos hsqrtB
  have hFpos : 0 < haagerupF s := haagerupF_pos hs
  have hbound : (2 / Real.pi) / dAux (s / 2) ≤ (haagerupF s) ^ 2 := by
    rw [haagerupF_sq hs]
    apply (div_le_iff₀ (dAux_pos hx)).2
    have hmul := mul_le_mul_of_nonneg_left
      (one_le_dAux_mul_rAux hx) hp.le
    calc
      2 / Real.pi ≤ (2 / Real.pi) * (dAux (s / 2) * rAux (s / 2)) := by
        simpa using hmul
      _ = (2 / Real.pi) * rAux (s / 2) * dAux (s / 2) := by ring
  have hAsq :
      (Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2)))) ^ 2 =
        (2 / Real.pi) / dAux (s / 2) := by
    rw [div_pow, hCsq, Real.sq_sqrt hB.le, hbase]
  have hsquare :
      (Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2)))) ^ 2 ≤
        (haagerupF s) ^ 2 := by
    rw [hAsq]
    exact hbound
  by_contra hnot
  have hlt : haagerupF s <
      Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2))) :=
    not_le.mp hnot
  have hprod : 0 <
      ((Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2)))) -
        haagerupF s) *
      ((Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2)))) +
        haagerupF s) :=
    mul_pos (sub_pos.mpr hlt) (add_pos hApos hFpos)
  nlinarith [hsquare]

private lemma sqrt_eq_one_div {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hAB : A * B = 1) :
    Real.sqrt A = 1 / Real.sqrt B := by
  have hprod : Real.sqrt A * Real.sqrt B = 1 := by
    calc
      Real.sqrt A * Real.sqrt B = Real.sqrt (A * B) :=
        (Real.sqrt_mul hA.le B).symm
      _ = 1 := by rw [hAB, Real.sqrt_one]
  exact (eq_div_iff (Real.sqrt_pos.2 hB).ne').2 hprod

theorem _root_.solution :
    (∀ s : ℝ, 0 < s →
      Cconst / Real.sqrt (1 + 1 / (2 * s) + 1 / (8 * s * (s + 1 / 2))) ≤ haagerupF s) ∧
    (∀ u : ℝ, 0 < u → Cconst * rFun u ≤ haagerupF ((u ^ 2)⁻¹)) := by
  constructor
  · intro s hs
    exact wallis_bound hs
  · intro u hu
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
    have hs : 0 < (u ^ 2)⁻¹ := inv_pos.mpr hu2
    have hmain := wallis_bound hs
    have hnum : 0 < 8 + 4 * u ^ 2 := by positivity
    have hden : 0 < 8 + 8 * u ^ 2 + 3 * u ^ 4 := by positivity
    have hsum0 : (u ^ 2)⁻¹ + 1 / 2 ≠ 0 := by linarith
    have hBform :
        1 + 1 / (2 * (u ^ 2)⁻¹) +
            1 / (8 * (u ^ 2)⁻¹ * ((u ^ 2)⁻¹ + 1 / 2)) =
          (8 + 8 * u ^ 2 + 3 * u ^ 4) / (8 + 4 * u ^ 2) := by
      field_simp [hu.ne', hu2.ne', hs.ne', hsum0, hnum.ne'] <;> ring
    have hB : 0 <
        1 + 1 / (2 * (u ^ 2)⁻¹) +
          1 / (8 * (u ^ 2)⁻¹ * ((u ^ 2)⁻¹ + 1 / 2)) := by
      rw [hBform]
      exact div_pos hden hnum
    have hR : 0 < (8 + 4 * u ^ 2) / (8 + 8 * u ^ 2 + 3 * u ^ 4) :=
      div_pos hnum hden
    have hAB :
        ((8 + 4 * u ^ 2) / (8 + 8 * u ^ 2 + 3 * u ^ 4)) *
          (1 + 1 / (2 * (u ^ 2)⁻¹) +
            1 / (8 * (u ^ 2)⁻¹ * ((u ^ 2)⁻¹ + 1 / 2))) = 1 := by
      rw [hBform]
      field_simp [hnum.ne', hden.ne'] <;> ring
    have hrsqrt : rFun u =
        1 / Real.sqrt (1 + 1 / (2 * (u ^ 2)⁻¹) +
          1 / (8 * (u ^ 2)⁻¹ * ((u ^ 2)⁻¹ + 1 / 2))) := by
      unfold rFun
      exact sqrt_eq_one_div hR hB hAB
    have heq : Cconst * rFun u =
        Cconst / Real.sqrt (1 + 1 / (2 * (u ^ 2)⁻¹) +
          1 / (8 * (u ^ 2)⁻¹ * ((u ^ 2)⁻¹ + 1 / 2))) := by
      rw [hrsqrt]
      ring
    rw [heq]
    exact hmain

end KhintchineTwoRegime
