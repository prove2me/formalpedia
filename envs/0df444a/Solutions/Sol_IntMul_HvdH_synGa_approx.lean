-- Prove2me | solution 1 for IntMul.HvdH.synGa_approx
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T01:27:53.907695+00:00
-- url     : https://prove2.me/submissions/6882e3c3-ebd6-4103-a35a-d52de88e27a9

import Definitions.Def_IntMul_HvdH_SynFFT

open Complex

namespace IntMul.HvdH.SynPf
open IntMul.HvdH

@[simp] lemma gC_re (z : ℤ × ℤ) : (gC z).re = z.1 := by simp [gC]
@[simp] lemma gC_im (z : ℤ × ℤ) : (gC z).im = z.2 := by simp [gC]

lemma gC_add (a b : ℤ × ℤ) : gC (a + b) = gC a + gC b := by
  simp only [gC, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

lemma gC_sub (a b : ℤ × ℤ) : gC (a - b) = gC a - gC b := by
  simp only [gC, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]; ring

lemma gC_neg (a : ℤ × ℤ) : gC (-a) = -gC a := by
  simp only [gC, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]; ring

lemma norm_le_of_re_im {z : ℂ} {c : ℝ} (hre : |z.re| ≤ c) (him : |z.im| ≤ c) :
    ‖z‖ ≤ 3 / 2 * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hre
  have h1 : z.re ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 : z.im ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have : ‖z‖ ^ 2 ≤ (3 / 2 * c) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this

lemma tdiv2_bounds (m : ℤ) : |(m.tdiv 2 : ℝ) - m / 2| ≤ 1 / 2 ∧ |(m.tdiv 2 : ℝ)| ≤ |(m : ℝ)| / 2 := by
  have h : 2 * m.tdiv 2 + m.tmod 2 = m := Int.mul_tdiv_add_tmod m 2
  have h1 := Int.tmod_lt_of_pos m (by norm_num : (0 : ℤ) < 2)
  have h2 := Int.lt_tmod_of_pos m (by norm_num : (0 : ℤ) < 2)
  rcases le_or_gt 0 m with hm | hm
  · have h3 : 0 ≤ m.tmod 2 := Int.tmod_nonneg 2 hm
    have hq : 0 ≤ m.tdiv 2 := Int.tdiv_nonneg hm (by norm_num)
    have e1 : (m : ℝ) = 2 * (m.tdiv 2 : ℝ) + (m.tmod 2 : ℝ) := by exact_mod_cast h.symm
    have e2 : (0 : ℝ) ≤ (m.tmod 2 : ℝ) := by exact_mod_cast h3
    have e3 : (m.tmod 2 : ℝ) < 2 := by exact_mod_cast h1
    have e3' : (m.tmod 2 : ℝ) ≤ 1 := by
      have : m.tmod 2 ≤ 1 := by omega
      exact_mod_cast this
    have hqR : (0 : ℝ) ≤ (m.tdiv 2 : ℝ) := by exact_mod_cast hq
    have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
    rw [abs_of_nonneg hqR, abs_of_nonneg hmR, abs_le]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · have h3 : m.tmod 2 ≤ 0 := by
      have := Int.tmod_nonneg 2 (show 0 ≤ -m by omega); rw [Int.neg_tmod] at this; omega
    have hq : m.tdiv 2 ≤ 0 := by
      have := Int.tdiv_nonneg (show 0 ≤ -m by omega) (by norm_num : (0:ℤ) ≤ 2); rw [Int.neg_tdiv] at this; omega
    have e1 : (m : ℝ) = 2 * (m.tdiv 2 : ℝ) + (m.tmod 2 : ℝ) := by exact_mod_cast h.symm
    have e2 : (m.tmod 2 : ℝ) ≤ 0 := by exact_mod_cast h3
    have e3' : (-1 : ℝ) ≤ (m.tmod 2 : ℝ) := by
      have : -1 ≤ m.tmod 2 := by omega
      exact_mod_cast this
    have hqR : (m.tdiv 2 : ℝ) ≤ 0 := by exact_mod_cast hq
    have hmR : (m : ℝ) < 0 := by exact_mod_cast hm
    rw [abs_of_nonpos hqR, abs_of_neg hmR, abs_le]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

lemma halfZ_err (z : ℤ × ℤ) : ‖gC (halfZ z) - gC z / 2‖ ≤ 3 / 4 := by
  have h := norm_le_of_re_im (z := gC (halfZ z) - gC z / 2) (c := 1 / 2) ?_ ?_
  · linarith
  · have := (tdiv2_bounds z.1).1
    simpa [halfZ] using this
  · have := (tdiv2_bounds z.2).1
    simpa [halfZ] using this

lemma halfZ_norm (z : ℤ × ℤ) : ‖gC (halfZ z)‖ ≤ ‖gC z‖ / 2 := by
  have h1 := (tdiv2_bounds z.1).2
  have h2 := (tdiv2_bounds z.2).2
  have hn : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have a1 : ((z.1.tdiv 2 : ℤ) : ℝ) ^ 2 ≤ ((z.1 : ℝ) / 2) ^ 2 := by
    rw [← sq_abs, ← sq_abs ((z.1 : ℝ) / 2), abs_div, abs_two]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a2 : ((z.2.tdiv 2 : ℤ) : ℝ) ^ 2 ≤ ((z.2 : ℝ) / 2) ^ 2 := by
    rw [← sq_abs, ← sq_abs ((z.2 : ℝ) / 2), abs_div, abs_two]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have : ‖gC (halfZ z)‖ ^ 2 ≤ (‖gC z‖ / 2) ^ 2 := by
    rw [div_pow, hn, hn]; simp only [gC_re, gC_im, halfZ]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this

lemma gC_yShift (r : ℕ) (m : ℤ) (A : ℕ → ℤ × ℤ) (c : ℕ) :
    gC (yShift r m A c) = yShift r m (fun c' => gC (A c')) c := by
  unfold yShift; split_ifs <;> simp [gC_neg]

lemma yShift_sub (r : ℕ) (m : ℤ) (a b : ℕ → ℂ) (c : ℕ) :
    yShift r m a c - yShift r m b c = yShift r m (fun c' => a c' - b c') c := by
  unfold yShift; split_ifs <;> ring

lemma norm_yShift (r : ℕ) (m : ℤ) (a : ℕ → ℂ) (c : ℕ) :
    ‖yShift r m a c‖ = ‖a ((c - m) % r).toNat‖ := by
  unfold yShift; split_ifs <;> simp

/-- The exact recursive transform is `1`-Lipschitz. -/
lemma half_diff_lip {ι : Type*} {x y : ι → ℂ} {δ : ℝ} (h : ∀ k, ‖x k - y k‖ ≤ δ) (a b : ι) :
    ‖(x a - x b) / 2 - (y a - y b) / 2‖ ≤ δ := by
  have e : (x a - x b) / 2 - (y a - y b) / 2 = ((x a - y a) - (x b - y b)) / 2 := by ring
  rw [e, norm_div, Complex.norm_two]
  have := norm_sub_le (x a - y a) (x b - y b)
  linarith [h a, h b]

theorem synG_lip (r : ℕ) : ∀ e, SupLip (synG r e)
  | 0 => fun _ _ _ h k => h k
  | e + 1 => by
    intro x y δ h kc
    have ih := synG_lip r e
    simp only [synG]
    split_ifs
    · apply ih; intro kc'
      have : (x kc' + x (kc'.1 + 2 ^ e, kc'.2)) / 2 - (y kc' + y (kc'.1 + 2 ^ e, kc'.2)) / 2 =
          ((x kc' - y kc') + (x (kc'.1 + 2 ^ e, kc'.2) - y (kc'.1 + 2 ^ e, kc'.2))) / 2 := by ring
      rw [this, norm_div, Complex.norm_two]
      have := norm_add_le (x kc' - y kc') (x (kc'.1 + 2 ^ e, kc'.2) - y (kc'.1 + 2 ^ e, kc'.2))
      linarith [h kc', h (kc'.1 + 2 ^ e, kc'.2)]
    · apply ih; intro kc'
      rw [yShift_sub, norm_yShift]
      exact half_diff_lip h _ _

/-- **Lemma 3.2.** The fixed-point synthetic FFT `G̃_{2^e}` approximates `G_{2^e}` with
error at most `e = log₂ t`. -/
theorem synGa_approx (p r : ℕ) : ∀ e, FPApprox p (synGa r e) (synG r e) e
  | 0 => by
    intro U hU
    refine ⟨hU, fun k => ?_⟩
    have hp : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
    simp only [synGa, synG, id]
    rw [mul_div_cancel₀ _ hp, sub_self, norm_zero]; norm_num
  | e + 1 => by
    intro U hU
    have ih := synGa_approx p r e
    have hl := synG_lip r e
    have hp : (0 : ℝ) < 2 ^ p := by positivity
    set u : ℕ × ℕ → ℂ := fun i => gC (U i) / 2 ^ p with hu
    set m : ℕ → ℤ := fun k => -((2 * r / 2 ^ (e + 1) * k : ℕ) : ℤ) with hm
    set V : ℕ × ℕ → ℤ × ℤ := fun kc' => halfZ (U kc' + U (kc'.1 + 2 ^ e, kc'.2)) with hV
    set W : ℕ × ℕ → ℤ × ℤ := fun kc' => yShift r (m kc'.1)
      (fun c => halfZ (U (kc'.1, c) - U (kc'.1 + 2 ^ e, c))) kc'.2 with hW
    set v : ℕ × ℕ → ℂ := fun kc' => (u kc' + u (kc'.1 + 2 ^ e, kc'.2)) / 2 with hv
    set w : ℕ × ℕ → ℂ := fun kc' => yShift r (m kc'.1)
      (fun c => (u (kc'.1, c) - u (kc'.1 + 2 ^ e, c)) / 2) kc'.2 with hw
    -- the butterflies keep the disc
    have hVd : InDisc p V := by
      intro kc'
      refine (halfZ_norm _).trans ?_
      rw [gC_add]
      have := norm_add_le (gC (U kc')) (gC (U (kc'.1 + 2 ^ e, kc'.2)))
      linarith [hU kc', hU (kc'.1 + 2 ^ e, kc'.2)]
    have hWd : InDisc p W := by
      intro kc'
      simp only [hW]
      rw [gC_yShift, norm_yShift]
      refine (halfZ_norm _).trans ?_
      rw [gC_sub]
      have := norm_sub_le (gC (U (kc'.1, ((kc'.2 - m kc'.1) % r).toNat)))
        (gC (U (kc'.1 + 2 ^ e, ((kc'.2 - m kc'.1) % r).toNat)))
      linarith [hU (kc'.1, ((kc'.2 - m kc'.1) % r).toNat),
        hU (kc'.1 + 2 ^ e, ((kc'.2 - m kc'.1) % r).toNat)]
    -- and are accurate to `1` unit
    have hVe : ∀ kc', ‖gC (V kc') / 2 ^ p - v kc'‖ ≤ 1 / 2 ^ p := by
      intro kc'
      have e1 : gC (V kc') / 2 ^ p - v kc' =
          (gC (halfZ (U kc' + U (kc'.1 + 2 ^ e, kc'.2))) -
            gC (U kc' + U (kc'.1 + 2 ^ e, kc'.2)) / 2) / 2 ^ p := by
        simp only [hV, hv, hu, gC_add]; field_simp; try ring
      rw [e1, norm_div, norm_pow, Complex.norm_two]
      exact div_le_div_of_nonneg_right ((halfZ_err _).trans (by norm_num)) hp.le
    have hWe : ∀ kc', ‖gC (W kc') / 2 ^ p - w kc'‖ ≤ 1 / 2 ^ p := by
      intro kc'
      simp only [hW, hw]
      rw [gC_yShift]
      have e1 : yShift r (m kc'.1) (fun c' => gC (halfZ (U (kc'.1, c') - U (kc'.1 + 2 ^ e, c')))) kc'.2
          / 2 ^ p - yShift r (m kc'.1) (fun c => (u (kc'.1, c) - u (kc'.1 + 2 ^ e, c)) / 2) kc'.2 =
          yShift r (m kc'.1) (fun c' => gC (halfZ (U (kc'.1, c') - U (kc'.1 + 2 ^ e, c'))) / 2 ^ p)
            kc'.2 - yShift r (m kc'.1) (fun c => (u (kc'.1, c) - u (kc'.1 + 2 ^ e, c)) / 2) kc'.2 := by
        unfold yShift; split_ifs <;> ring
      rw [e1, yShift_sub, norm_yShift]
      set c := ((kc'.2 - m kc'.1) % r).toNat
      have e2 : gC (halfZ (U (kc'.1, c) - U (kc'.1 + 2 ^ e, c))) / 2 ^ p -
          (u (kc'.1, c) - u (kc'.1 + 2 ^ e, c)) / 2 =
          (gC (halfZ (U (kc'.1, c) - U (kc'.1 + 2 ^ e, c))) -
            gC (U (kc'.1, c) - U (kc'.1 + 2 ^ e, c)) / 2) / 2 ^ p := by
        simp only [hu, gC_sub]; field_simp; try ring
      rw [e2, norm_div, norm_pow, Complex.norm_two]
      exact div_le_div_of_nonneg_right ((halfZ_err _).trans (by norm_num)) hp.le
    -- combine with the induction hypothesis
    have comb : ∀ (X : ℕ × ℕ → ℤ × ℤ) (x : ℕ × ℕ → ℂ), InDisc p X →
        (∀ kc', ‖gC (X kc') / 2 ^ p - x kc'‖ ≤ 1 / 2 ^ p) → ∀ kc,
        ‖gC (synGa r e X kc) - 2 ^ p * synG r e x kc‖ ≤ ((e + 1 : ℕ) : ℝ) := by
      intro X x hX hXe kc
      have h1 := (ih X hX).2 kc
      have h2 := hl (fun i => gC (X i) / 2 ^ p) x _ hXe kc
      have e3 : gC (synGa r e X kc) - 2 ^ p * synG r e x kc =
          (gC (synGa r e X kc) - 2 ^ p * synG r e (fun i => gC (X i) / 2 ^ p) kc) +
            2 ^ p * (synG r e (fun i => gC (X i) / 2 ^ p) kc - synG r e x kc) := by ring
      rw [e3]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_pow, Complex.norm_two]
      have h3 : (2 : ℝ) ^ p * ‖synG r e (fun i => gC (X i) / 2 ^ p) kc - synG r e x kc‖ ≤ 1 := by
        calc _ ≤ 2 ^ p * (1 / 2 ^ p) := mul_le_mul_of_nonneg_left h2 hp.le
          _ = 1 := by field_simp
      push_cast; linarith
    refine ⟨fun kc => ?_, fun kc => ?_⟩
    · simp only [synGa]
      split_ifs
      · exact (ih V hVd).1 _
      · exact (ih W hWd).1 _
    · show ‖gC (synGa r (e + 1) U kc) - 2 ^ p * synG r (e + 1) u kc‖ ≤ ((e + 1 : ℕ) : ℝ)
      simp only [synGa, synG]
      split_ifs
      · exact comb V v hVd hVe _
      · exact comb W w hWd hWe _

end IntMul.HvdH.SynPf

open IntMul.HvdH in
theorem solution (p r e : ℕ) : FPApprox p (synGa r e) (synG r e) e := IntMul.HvdH.SynPf.synGa_approx p r e
