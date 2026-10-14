-- Prove2me | solution 1 for IntMul.HvdH.mulZ_disc
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T02:52:47.109024+00:00
-- url     : https://prove2.me/submissions/c2087a2e-4a69-4e63-aa3a-0c12f70e1dc9

import Definitions.Def_IntMul_HvdH_FPApprox
import Definitions.Def_IntMul_HvdH_SynFFT
import Definitions.Def_IntMul_HvdH_FixedPoint
import Definitions.Def_IntMul_HvdH_KronMul
import Definitions.Def_IntMul_HvdH_ConvR
import Mathlib
import Definitions.Def_IntMul_HvdH_ConvC
import Theorems.Thm_IntMul_HvdH_twiddle_bound

open Complex

namespace IntMul.HvdH.FPPf
open IntMul.HvdH

/-- The identity is its own approximation. -/
theorem fp_id {ι : Type*} (p : ℕ) : FPApprox (ι := ι) p id id 0 := by
  intro U hU
  refine ⟨hU, fun k => ?_⟩
  have hp : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [id]
  rw [mul_div_cancel₀ _ hp, sub_self, norm_zero]

/-- Corollary 2.8: composing approximations adds their errors, provided the second exact map
is `1`-Lipschitz. -/
theorem fp_comp {ι κ μ : Type*} (p : ℕ) {Aa : (ι → ℤ × ℤ) → (κ → ℤ × ℤ)} {A : (ι → ℂ) → (κ → ℂ)}
    {Ba : (κ → ℤ × ℤ) → (μ → ℤ × ℤ)} {B : (κ → ℂ) → (μ → ℂ)} {ε₁ ε₂ : ℝ}
    (hA : FPApprox p Aa A ε₁) (hB : FPApprox p Ba B ε₂) (hBl : SupLip B) :
    FPApprox p (Ba ∘ Aa) (B ∘ A) (ε₁ + ε₂) := by
  intro U hU
  obtain ⟨hV, hAe⟩ := hA U hU
  obtain ⟨hW, hBe⟩ := hB (Aa U) hV
  refine ⟨hW, fun k => ?_⟩
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set u : ι → ℂ := fun i => gC (U i) / 2 ^ p
  set v : κ → ℂ := fun i => gC (Aa U i) / 2 ^ p
  have hvu : ∀ i, ‖v i - A u i‖ ≤ ε₁ / 2 ^ p := by
    intro i
    have e : v i - A u i = (gC (Aa U i) - 2 ^ p * A u i) / 2 ^ p := by
      simp only [v]; field_simp
    rw [e, norm_div, norm_pow, Complex.norm_two]
    exact div_le_div_of_nonneg_right (hAe i) hp.le
  have hL := hBl v (A u) _ hvu k
  have e : gC (Ba (Aa U) k) - 2 ^ p * B (A u) k =
      (gC (Ba (Aa U) k) - 2 ^ p * B v k) + 2 ^ p * (B v k - B (A u) k) := by ring
  show ‖gC (Ba (Aa U) k) - 2 ^ p * B (A u) k‖ ≤ ε₁ + ε₂
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_pow, Complex.norm_two]
  have h2 : (2 : ℝ) ^ p * ‖B v k - B (A u) k‖ ≤ ε₁ := by
    calc _ ≤ 2 ^ p * (ε₁ / 2 ^ p) := mul_le_mul_of_nonneg_left hL hp.le
      _ = ε₁ := by field_simp
  linarith [hBe k]

theorem lip_comp {ι κ μ : Type*} {A : (ι → ℂ) → (κ → ℂ)} {B : (κ → ℂ) → (μ → ℂ)}
    (hA : SupLip A) (hB : SupLip B) : SupLip (B ∘ A) :=
  fun x y δ h k => hB _ _ δ (hA x y δ h) k

theorem fp_slice {d : ℕ} (p : ℕ) (i : Fin d) {Aa : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)}
    {A : (ℕ → ℂ) → (ℕ → ℂ)} {ε : ℝ} (hA : FPApprox p Aa A ε) :
    FPApprox p (sliceMapZ i Aa) (sliceMap i A) ε := by
  intro U hU
  have hrow : ∀ j : Fin d → ℕ, InDisc p (fun k => U (Function.update j i k)) := fun j k => hU _
  exact ⟨fun j => (hA _ (hrow j)).1 (j i), fun j => (hA _ (hrow j)).2 (j i)⟩

theorem lip_slice {d : ℕ} (i : Fin d) {A : (ℕ → ℂ) → (ℕ → ℂ)} (hA : SupLip A) :
    SupLip (sliceMap i A) :=
  fun x y δ h j => hA _ _ δ (fun k => h _) (j i)

theorem fp_sliceComp {d : ℕ} (p : ℕ) {Aa : Fin d → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)}
    {A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)} {ε : Fin d → ℝ}
    (hA : ∀ i, FPApprox p (Aa i) (A i) (ε i)) (hL : ∀ i, SupLip (A i)) :
    ∀ l : List (Fin d), FPApprox p (sliceCompZ Aa l) (sliceComp A l) (l.map ε).sum ∧
      SupLip (sliceComp A l)
  | [] => ⟨by simpa [sliceCompZ, sliceComp] using fp_id p, fun _ _ _ h k => h k⟩
  | i :: l => by
    obtain ⟨h1, h2⟩ := fp_sliceComp p hA hL l
    refine ⟨?_, lip_comp (lip_slice i (hL i)) h2⟩
    have := fp_comp p (fp_slice p i (hA i)) h1 h2
    simpa [sliceCompZ, sliceComp] using this

/-- Lemma 2.11: the fixed-point tensor product of approximations approximates the tensor
product, with error the sum of the errors. -/
theorem fp_tensor {d : ℕ} (p : ℕ) (Aa : Fin d → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ))
    (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (ε : Fin d → ℝ)
    (hA : ∀ i, FPApprox p (Aa i) (A i) (ε i)) (hL : ∀ i, SupLip (A i)) :
    FPApprox p (tensorMapZ Aa) (tensorMap A) (∑ i, ε i) := by
  have h := (fp_sliceComp p hA hL (List.finRange d)).1
  rw [Fin.sum_univ_def]
  exact h

theorem lip_sliceComp {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hL : ∀ i, SupLip (A i)) :
    ∀ l : List (Fin d), SupLip (sliceComp A l)
  | [] => fun _ _ _ h k => h k
  | i :: l => lip_comp (lip_slice i (hL i)) (lip_sliceComp A hL l)

theorem lip_tensor {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hL : ∀ i, SupLip (A i)) :
    SupLip (tensorMap A) :=
  lip_sliceComp A hL (List.finRange d)

end IntMul.HvdH.FPPf


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


namespace IntMul.HvdH.FP
open IntMul.HvdH

lemma rho0_abs_le (x : ℝ) : |((rho0 x : ℤ) : ℝ)| ≤ |x| := by
  unfold rho0
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast Int.floor_nonneg.2 h), abs_of_nonneg h]
    exact Int.floor_le x
  · push Not at h
    have h1 : ((⌈x⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.2 (by simpa using h.le)
    rw [abs_of_nonpos h1, abs_of_neg h]
    linarith [Int.le_ceil x]

lemma rho0_sub_lt (x : ℝ) : |((rho0 x : ℤ) : ℝ) - x| < 1 := by
  unfold rho0
  split_ifs with h
  · rw [abs_lt]; constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]
  · rw [abs_lt]; constructor <;> linarith [Int.le_ceil x, Int.ceil_lt_add_one x]

/-- If `2x ∈ ℤ` then rounding towards zero moves `x` by at most `1/2`. -/
lemma rho0_sub_half (x : ℝ) (hx : ∃ n : ℤ, 2 * x = n) : |((rho0 x : ℤ) : ℝ) - x| ≤ 1 / 2 := by
  obtain ⟨n, hn⟩ := hx
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · have : x = ((n / 2 : ℤ) : ℝ) := by
      have := Int.mul_ediv_add_emod n 2
      rw [h, add_zero] at this
      have e : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by exact_mod_cast this.symm
      linarith
    rw [this]; unfold rho0
    split_ifs <;> simp
  · have hx : x = ((n / 2 : ℤ) : ℝ) + 1 / 2 := by
      have := Int.mul_ediv_add_emod n 2
      rw [h] at this
      have e : (n : ℝ) = 1 + 2 * ((n / 2 : ℤ) : ℝ) := by
        have e' : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast this.symm
        linarith
      linarith
    set m := n / 2
    unfold rho0
    split_ifs with h0
    · have : ⌊x⌋ = m := by rw [Int.floor_eq_iff, hx]; constructor <;> linarith
      rw [this, hx, abs_le]; constructor <;> linarith
    · have : ⌈x⌉ = m + 1 := by
        rw [Int.ceil_eq_iff, hx]; push_cast; constructor <;> linarith
      rw [this, hx, abs_le]; push_cast; constructor <;> linarith

lemma norm_rho0C_le (u : ℂ) : ‖rho0C u‖ ≤ ‖u‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  have h1 := rho0_abs_le u.re
  have h2 := rho0_abs_le u.im
  have hre : (rho0C u).re = rho0 u.re := by simp [rho0C]
  have him : (rho0C u).im = rho0 u.im := by simp [rho0C]
  rw [hre, him]
  nlinarith [sq_abs ((rho0 u.re : ℤ) : ℝ), sq_abs u.re, sq_abs ((rho0 u.im : ℤ) : ℝ), sq_abs u.im,
    abs_nonneg ((rho0 u.re : ℤ) : ℝ), abs_nonneg ((rho0 u.im : ℤ) : ℝ)]

lemma norm_rho0C_sub_lt (u : ℂ) : ‖rho0C u - u‖ < Real.sqrt 2 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_lt_sqrt (by positivity)
  have h1 := rho0_sub_lt u.re
  have h2 := rho0_sub_lt u.im
  simp only [rho0C, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, zero_mul]
  have a1 : (((rho0 u.re : ℤ) : ℝ) - u.re) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.re : ℤ) : ℝ) - u.re)]
  have a2 : (((rho0 u.im : ℤ) : ℝ) - u.im) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.im : ℤ) : ℝ) - u.im)]
  linarith

lemma norm_rho0C_sub_half (u : ℂ) (hre : ∃ n : ℤ, 2 * u.re = n) (him : ∃ n : ℤ, 2 * u.im = n) :
    ‖rho0C u - u‖ ≤ Real.sqrt 2 / 2 := by
  have hs : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [show (1 / 2 : ℝ) = 2 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [Complex.norm_eq_sqrt_sq_add_sq, ← hs]
  apply Real.sqrt_le_sqrt
  have h1 := rho0_sub_half u.re hre
  have h2 := rho0_sub_half u.im him
  simp only [rho0C, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, zero_mul]
  have a1 : (((rho0 u.re : ℤ) : ℝ) - u.re) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.re : ℤ) : ℝ) - u.re)]
  have a2 : (((rho0 u.im : ℤ) : ℝ) - u.im) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.im : ℤ) : ℝ) - u.im)]
  linarith

/-- `|ρ(u)| ≤ |u|` and `|ρ(u) - u| < √2 · 2^{-p}`. -/
theorem rho_bounds (p : ℕ) (u : ℂ) :
    ‖rho p u‖ ≤ ‖u‖ ∧ ‖rho p u - u‖ < Real.sqrt 2 * ((2 : ℝ) ^ p)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have hn : ‖(2 : ℂ) ^ p‖ = 2 ^ p := by simp
  constructor
  · unfold rho
    rw [norm_mul, norm_inv, hn]
    calc ((2 : ℝ) ^ p)⁻¹ * ‖rho0C ((2 : ℂ) ^ p * u)‖ ≤ ((2 : ℝ) ^ p)⁻¹ * ‖(2 : ℂ) ^ p * u‖ :=
          mul_le_mul_of_nonneg_left (norm_rho0C_le _) (by positivity)
      _ = ‖u‖ := by rw [norm_mul, hn, ← mul_assoc, inv_mul_cancel₀ h2.ne', one_mul]
  · have e : rho p u - u = ((2 : ℂ) ^ p)⁻¹ * (rho0C ((2 : ℂ) ^ p * u) - (2 : ℂ) ^ p * u) := by
      unfold rho; field_simp
    rw [e, norm_mul, norm_inv, hn, mul_comm (Real.sqrt 2)]
    exact mul_lt_mul_of_pos_left (norm_rho0C_sub_lt _) (by positivity)

/-- **Lemma 2.2 (scaling), error part.** If `‖u‖ ≤ 1/c` then `ṽ = scaleFP p c ũ` lies in the unit
disc and `2^p ‖ṽ - c u‖ < 2 c · 2^p ‖ũ - u‖ + 3`. -/
theorem scaleFP_bound (p c : ℕ) (hc : 1 ≤ c) (u ũ : ℂ) (hu : ‖u‖ ≤ (c : ℝ)⁻¹) :
    ‖scaleFP p c ũ‖ ≤ 1 ∧
      (2 : ℝ) ^ p * ‖scaleFP p c ũ - c * u‖ < 2 * c * ((2 : ℝ) ^ p * ‖ũ - u‖) + 3 := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  set w := (c : ℂ) * ũ with hw
  have hv : ‖(c : ℂ) * u‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_natCast]
    calc (c : ℝ) * ‖u‖ ≤ c * (c : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hu hc0.le
      _ = 1 := mul_inv_cancel₀ hc0.ne'
  have hwv : ‖w - c * u‖ = c * ‖ũ - u‖ := by
    rw [hw, ← mul_sub, norm_mul, Complex.norm_natCast]
  have hε : 0 ≤ (2 : ℝ) ^ p * ‖ũ - u‖ := by positivity
  unfold scaleFP
  rw [← hw]
  split_ifs with hw1
  · refine ⟨hw1, ?_⟩
    rw [hwv]
    nlinarith
  · push Not at hw1
    set B : ℝ := ((⌈(2 : ℝ) ^ p * ‖w‖⌉ : ℤ) : ℝ) with hB
    have hB1 : (2 : ℝ) ^ p * ‖w‖ ≤ B := Int.le_ceil _
    have hB2 : B < (2 : ℝ) ^ p * ‖w‖ + 1 := Int.ceil_lt_add_one _
    have hBp : (2 : ℝ) ^ p < B := by nlinarith
    have hB0 : 0 < B := by linarith
    set z : ℂ := (((2 : ℝ) ^ p / B : ℝ) : ℂ) * w with hz
    have hzdef : (2 : ℂ) ^ p * w / ((⌈(2 : ℝ) ^ p * ‖w‖⌉ : ℤ) : ℂ) = z := by
      rw [hz]
      have : ((⌈(2 : ℝ) ^ p * ‖w‖⌉ : ℤ) : ℂ) = (B : ℂ) := by rw [hB]; push_cast; rfl
      rw [this]; push_cast; ring
    rw [hzdef]
    have hzn : ‖z‖ ≤ 1 := by
      rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_eq_mul_div, div_le_one hB0]
      exact hB1
    obtain ⟨hr1, hr2⟩ := rho_bounds p z
    refine ⟨hr1.trans hzn, ?_⟩
    have hzw : (2 : ℝ) ^ p * ‖z - w‖ ≤ B - 2 ^ p := by
      have e : z - w = (((2 : ℝ) ^ p / B - 1 : ℝ) : ℂ) * w := by rw [hz]; push_cast; ring
      have hneg : (2 : ℝ) ^ p / B - 1 ≤ 0 := by
        rw [div_sub_one hB0.ne']; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hB0.le
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hneg]
      have hq : -((2 : ℝ) ^ p / B - 1) = (B - 2 ^ p) / B := by field_simp; ring
      rw [hq, div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hB0]
      have := mul_le_mul_of_nonneg_left hB1 (show 0 ≤ B - 2 ^ p by linarith)
      nlinarith [norm_nonneg w]
    have hwle : ‖w‖ ≤ 1 + ‖w - c * u‖ := by
      calc ‖w‖ = ‖(c * u) + (w - c * u)‖ := by ring_nf
        _ ≤ ‖(c : ℂ) * u‖ + ‖w - c * u‖ := norm_add_le _ _
        _ ≤ 1 + ‖w - c * u‖ := by linarith
    have htri : ‖rho p z - c * u‖ ≤ ‖rho p z - z‖ + ‖z - w‖ + ‖w - c * u‖ := by
      calc ‖rho p z - c * u‖ = ‖(rho p z - z) + (z - w) + (w - c * u)‖ := by ring_nf
        _ ≤ ‖(rho p z - z) + (z - w)‖ + ‖w - c * u‖ := norm_add_le _ _
        _ ≤ ‖rho p z - z‖ + ‖z - w‖ + ‖w - c * u‖ := by gcongr; exact norm_add_le _ _
    have hs2 : Real.sqrt 2 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      · exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hr2' : (2 : ℝ) ^ p * ‖rho p z - z‖ < Real.sqrt 2 := by
      have := mul_lt_mul_of_pos_left hr2 h2
      rwa [mul_comm (Real.sqrt 2), ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul] at this
    rw [hwv] at hwle htri
    have hpw : (2 : ℝ) ^ p * ‖w‖ ≤ 2 ^ p + c * ((2 : ℝ) ^ p * ‖ũ - u‖) := by nlinarith
    calc (2 : ℝ) ^ p * ‖rho p z - c * u‖
        ≤ (2 : ℝ) ^ p * ‖rho p z - z‖ + (2 : ℝ) ^ p * ‖z - w‖ + c * ((2 : ℝ) ^ p * ‖ũ - u‖) := by
          nlinarith
      _ < 2 * c * ((2 : ℝ) ^ p * ‖ũ - u‖) + 3 := by nlinarith

end IntMul.HvdH.FP


open Finset

namespace IntMul.HvdH.KronPf
open IntMul.HvdH

lemma balanced_digit (B : ℤ) (hBe : Even B) (c W' : ℤ) (hc : 2 * |c| < B) :
    (c + B * W' + B / 2) % B - B / 2 = c := by
  obtain ⟨h, rfl⟩ := hBe
  have hh : (h + h) / 2 = h := by omega
  rw [hh]
  have : (c + (h + h) * W' + h) % (h + h) = c + h := by
    rw [show c + (h + h) * W' + h = (c + h) + (h + h) * W' by ring, Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt <;> · have := abs_lt.1 (show |c| < h by omega); omega
  omega

theorem kunpack_kpack (B : ℤ) (hB : 0 < B) (hBe : Even B) (c : List ℤ)
    (hc : ∀ x ∈ c, 2 * |x| < B) : kunpack B c.length (kpack B c) = c := by
  induction c with
  | nil => rfl
  | cons a cs ih =>
    have ha : 2 * |a| < B := hc a (by simp)
    have hcs : ∀ x ∈ cs, 2 * |x| < B := fun x hx => hc x (by simp [hx])
    simp only [List.length_cons, kunpack, kpack]
    have hd : (a + B * kpack B cs + B / 2) % B - B / 2 = a := balanced_digit B hBe a _ ha
    rw [hd]
    have hq : (a + B * kpack B cs - a) / B = kpack B cs := by
      rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hB.ne']
    rw [hq, ih hcs]

lemma kpack_eq_sum (B : ℤ) (c : List ℤ) :
    kpack B c = ∑ i ∈ range c.length, c.getD i 0 * B ^ i := by
  induction c with
  | nil => simp [kpack]
  | cons a cs ih =>
    rw [kpack, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_); ring

/-- The polynomial with coefficient list `c`. -/
noncomputable def toPoly (c : List ℤ) : Polynomial ℤ :=
  ∑ i ∈ range c.length, Polynomial.C (c.getD i 0) * Polynomial.X ^ i

lemma coeff_toPoly (c : List ℤ) (k : ℕ) : (toPoly c).coeff k = c.getD k 0 := by
  unfold toPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hk; simp only [Finset.mem_range, not_lt] at hk
    rw [List.getD_eq_default _ _ hk]; simp

lemma eval_toPoly (B : ℤ) (c : List ℤ) : (toPoly c).eval B = kpack B c := by
  rw [kpack_eq_sum, toPoly, Polynomial.eval_finset_sum]
  simp

lemma toPoly_polyMul (a b : List ℤ) : toPoly (polyMul a b) = toPoly a * toPoly b := by
  ext k
  rw [coeff_toPoly, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_toPoly]
  unfold polyMul
  by_cases hk : k < a.length + b.length - 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  · push Not at hk
    rw [List.getD_eq_default _ _ (by simpa using hk)]
    symm
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    by_cases hia : i < a.length
    · have : b.length ≤ k - i := by omega
      rw [List.getD_eq_default _ _ this, mul_zero]
    · push Not at hia
      rw [List.getD_eq_default _ _ hia, zero_mul]

theorem kpack_polyMul (B : ℤ) (a b : List ℤ) :
    kpack B (polyMul a b) = kpack B a * kpack B b := by
  rw [← eval_toPoly, ← eval_toPoly, ← eval_toPoly, toPoly_polyMul, Polynomial.eval_mul]

lemma sum_abs_getD_le (a : List ℤ) (M : ℤ) (ha : ∀ x ∈ a, |x| ≤ M) (N : ℕ) :
    ∑ i ∈ range N, |a.getD i 0| ≤ a.length * M := by
  have hz : ∀ i ∈ range N, i ∉ range N ∩ range a.length → |a.getD i 0| = 0 := by
    intro i hi hni
    have : a.length ≤ i := by
      by_contra h; exact hni (Finset.mem_inter.2 ⟨hi, Finset.mem_range.2 (by omega)⟩)
    rw [List.getD_eq_default _ _ this, abs_zero]
  rw [← Finset.sum_subset Finset.inter_subset_left hz]
  calc ∑ i ∈ range N ∩ range a.length, |a.getD i 0| ≤ ∑ i ∈ range a.length, |a.getD i 0| :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun i _ _ => abs_nonneg _)
    _ ≤ ∑ _i ∈ range a.length, M := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.1 hi)]
        exact ha _ (List.getElem_mem _)
    _ = a.length * M := by simp

lemma polyMul_coeff_bound (a b : List ℤ) (M : ℤ) (hM0 : 0 ≤ M) (ha : ∀ x ∈ a, |x| ≤ M)
    (hb : ∀ x ∈ b, |x| ≤ M) : ∀ x ∈ polyMul a b, |x| ≤ a.length * M * M := by
  intro x hx
  unfold polyMul at hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  have hM : ∀ j, |b.getD j 0| ≤ M := by
    intro j
    by_cases hj : j < b.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hb _ (List.getElem_mem _)
    · push Not at hj
      rw [List.getD_eq_default _ _ hj, abs_zero]
      exact hM0
  calc |∑ i ∈ range (k + 1), a.getD i 0 * b.getD (k - i) 0|
      ≤ ∑ i ∈ range (k + 1), |a.getD i 0 * b.getD (k - i) 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (k + 1), |a.getD i 0| * M := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
    _ = (∑ i ∈ range (k + 1), |a.getD i 0|) * M := by rw [Finset.sum_mul]
    _ ≤ a.length * M * M := by
        exact mul_le_mul_of_nonneg_right (sum_abs_getD_le a M ha _) hM0

lemma polyMul_length (a b : List ℤ) : (polyMul a b).length = a.length + b.length - 1 := by
  simp [polyMul]

theorem kronMul_eq (p r : ℕ) (a b : List ℤ) (ha : a.length = r) (hb : b.length = r)
    (hab : ∀ x ∈ a, |x| ≤ 2 ^ p) (hbb : ∀ x ∈ b, |x| ≤ 2 ^ p) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p) :
    kronMul p r a b = polyMul a b := by
  have hB : (0 : ℤ) < 2 ^ (3 * p) := by positivity
  have hBe : Even ((2 : ℤ) ^ (3 * p)) := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at hrp; omega
    · exact (Int.even_pow.2 ⟨even_two, by omega⟩)
  unfold kronMul
  rw [← kpack_polyMul]
  have hlen : 2 * r - 1 = (polyMul a b).length := by rw [polyMul_length, ha, hb]; omega
  rw [hlen]
  refine kunpack_kpack _ hB hBe _ (fun x hx => ?_)
  have h1 := polyMul_coeff_bound a b (2 ^ p) (by positivity) hab hbb x hx
  rw [ha] at h1
  have hrp' : (2 : ℤ) * r < 2 ^ p := by exact_mod_cast hrp
  have : (2 : ℤ) ^ (3 * p) = 2 ^ p * 2 ^ p * 2 ^ p := by ring
  rw [this]
  have hp0 : (0 : ℤ) < 2 ^ p := by positivity
  nlinarith [mul_pos hp0 hp0]

theorem mulR_eq_spec (p r : ℕ) (U0 U1 V0 V1 : List ℤ)
    (h0 : U0.length = r) (h1 : U1.length = r) (h2 : V0.length = r) (h3 : V1.length = r)
    (hU0 : ∀ x ∈ U0, |x| ≤ 2 ^ p) (hU1 : ∀ x ∈ U1, |x| ≤ 2 ^ p)
    (hV0 : ∀ x ∈ V0, |x| ≤ 2 ^ p) (hV1 : ∀ x ∈ V1, |x| ≤ 2 ^ p) (hr : 1 ≤ r)
    (hrp : 2 * r < 2 ^ p) :
    mulR p r U0 U1 V0 V1 = mulRSpec p r U0 U1 V0 V1 := by
  unfold mulR mulRSpec
  rw [kronMul_eq p r U0 V0 h0 h2 hU0 hV0 hr hrp, kronMul_eq p r U1 V1 h1 h3 hU1 hV1 hr hrp,
    kronMul_eq p r U0 V1 h0 h3 hU0 hV1 hr hrp, kronMul_eq p r U1 V0 h1 h2 hU1 hV0 hr hrp]

end IntMul.HvdH.KronPf


namespace IntMul.HvdH.SynEq
open IntMul.HvdH

lemma yShift_eq (r : ℕ) (m : ℤ) (a : ℕ → ℂ) (c : ℕ) :
    yShift r m a c = (-1 : ℂ) ^ (((c : ℤ) - m) / r) * a (((c : ℤ) - m) % r).toNat := by
  unfold yShift
  split_ifs with h
  · rw [Even.neg_one_zpow (Int.even_iff.mpr h), one_mul]
  · rw [Odd.neg_one_zpow (Int.odd_iff.mpr (by omega)), neg_one_mul]

lemma yShift_comp (r : ℕ) (hr : 0 < r) (m m' : ℤ) (a : ℕ → ℂ) (c : ℕ) :
    yShift r m (fun c' => yShift r m' a c') c = yShift r (m + m') a c := by
  rw [yShift_eq, yShift_eq, yShift_eq]
  set A : ℤ := (c : ℤ) - m
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hi : ((A % r).toNat : ℤ) = A % r := Int.toNat_of_nonneg (Int.emod_nonneg _ hr')
  rw [hi]
  have hA := Int.emod_add_mul_ediv A r
  have e : (c : ℤ) - (m + m') = (A % r - m') + (A / r) * r := by
    simp only [A] at hA ⊢; linarith
  rw [e, Int.add_mul_ediv_right _ _ hr', Int.add_mul_emod_self_right,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

lemma yShift_sub_r (r : ℕ) (hr : 0 < r) (m : ℤ) (n : ℕ) (a : ℕ → ℂ) (c : ℕ) :
    yShift r (m - r * n) a c = (-1 : ℂ) ^ n * yShift r m a c := by
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [yShift_eq, yShift_eq]
  have e : (c : ℤ) - (m - r * n) = ((c : ℤ) - m) + n * r := by ring
  rw [e, Int.add_mul_ediv_right _ _ hr', Int.add_mul_emod_self_right,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
  ring

lemma yShift_zero (r : ℕ) (a : ℕ → ℂ) (c : ℕ) (hc : c < r) : yShift r 0 a c = a c := by
  rw [yShift_eq]
  have h1 : ((c : ℤ) - 0) / r = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h2 : ((c : ℤ) - 0) % r = c := Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1, h2]; simp

lemma yShift_avg (r : ℕ) (m : ℤ) (a b : ℕ → ℂ) (c : ℕ) :
    yShift r m (fun c => (a c + b c) / 2) c = (yShift r m a c + yShift r m b c) / 2 := by
  simp only [yShift_eq]; ring

lemma yShift_hdiff (r : ℕ) (m : ℤ) (a b : ℕ → ℂ) (c : ℕ) :
    yShift r m (fun c => (a c - b c) / 2) c = (yShift r m a c - yShift r m b c) / 2 := by
  simp only [yShift_eq]; ring

lemma split_sum (f : ℕ → ℂ) (e : ℕ) :
    ∑ k ∈ Finset.range (2 ^ (e + 1)), f k = ∑ k ∈ Finset.range (2 ^ e), (f k + f (k + 2 ^ e)) := by
  rw [show 2 ^ (e + 1) = 2 ^ e + 2 ^ e by ring, Finset.sum_range_add, Finset.sum_add_distrib]
  congr 1; apply Finset.sum_congr rfl; intro k _; rw [add_comm]

theorem synG_eq (r : ℕ) (hr : 0 < r) : ∀ e, 2 ^ e ∣ 2 * r → ∀ (u : ℕ × ℕ → ℂ) (j c : ℕ),
    j < 2 ^ e → c < r →
    synG r e u (j, c) = (1 / 2 ^ e : ℂ) * ∑ k ∈ Finset.range (2 ^ e),
      yShift r (-((2 * r / 2 ^ e * j * k : ℕ) : ℤ)) (fun c' => u (k, c')) c
  | 0 => by
    intro _ u j c hj hc
    obtain rfl : j = 0 := by omega
    simp [synG, yShift_zero r _ c hc]
  | e + 1 => by
    intro hdiv u j c hj hc
    obtain ⟨K, hK⟩ := hdiv
    have hK1 : 2 * r / 2 ^ (e + 1) = K := by rw [hK]; exact Nat.mul_div_cancel_left _ (by positivity)
    have hK2 : 2 * r / 2 ^ e = 2 * K := by
      rw [hK, pow_succ, show 2 ^ e * 2 * K = 2 ^ e * (2 * K) by ring]
      exact Nat.mul_div_cancel_left _ (by positivity)
    have hrK : r = 2 ^ e * K := by rw [pow_succ] at hK; linarith
    have hdiv' : 2 ^ e ∣ 2 * r := ⟨2 * K, by rw [hK]; ring⟩
    have ih := synG_eq r hr e hdiv'
    have hp : (2 : ℂ) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
    simp only [synG]
    split_ifs with hpar
    · obtain ⟨l, rfl⟩ : ∃ l, j = 2 * l := ⟨j / 2, by omega⟩
      have hl : 2 * l / 2 = l := by omega
      rw [hl, ih _ l c (by omega) hc, split_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [yShift_avg]
      simp only [hK1, hK2]
      have e1 : (-((2 * K * l * k : ℕ) : ℤ)) = -((K * (2 * l) * k : ℕ) : ℤ) := by push_cast; ring
      have e2 : (-((K * (2 * l) * (k + 2 ^ e) : ℕ) : ℤ)) =
          -((2 * K * l * k : ℕ) : ℤ) - r * (2 * l : ℕ) := by rw [hrK]; push_cast; ring
      rw [e2, yShift_sub_r r hr, e1, pow_mul]
      simp only [neg_one_sq, one_pow, one_mul, pow_succ]
      field_simp; ring
    · obtain ⟨l, rfl⟩ : ∃ l, j = 2 * l + 1 := ⟨j / 2, by omega⟩
      have hl : (2 * l + 1) / 2 = l := by omega
      rw [hl, ih _ l c (by omega) hc, split_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      simp only [hK1, hK2]
      rw [yShift_comp r hr, yShift_hdiff]
      have e1 : (-((2 * K * l * k : ℕ) : ℤ)) + -((K * k : ℕ) : ℤ) =
          -((K * (2 * l + 1) * k : ℕ) : ℤ) := by push_cast; ring
      have e2 : (-((K * (2 * l + 1) * (k + 2 ^ e) : ℕ) : ℤ)) =
          -((K * (2 * l + 1) * k : ℕ) : ℤ) - r * (2 * l + 1 : ℕ) := by rw [hrK]; push_cast; ring
      rw [e2, yShift_sub_r r hr, e1, Odd.neg_one_pow ⟨l, rfl⟩]
      rw [pow_succ]
      field_simp; ring

end IntMul.HvdH.SynEq


open Complex

namespace IntMul.HvdH.CRPf
open IntMul.HvdH IntMul.HvdH.FPPf

theorem fp_rSlice {d : ℕ} (p : ℕ) (i : Fin d) {Aa : ((ℕ × ℕ) → ℤ × ℤ) → ((ℕ × ℕ) → ℤ × ℤ)}
    {A : ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)} {ε : ℝ} (hA : FPApprox p Aa A ε) :
    FPApprox p (rSlice i Aa) (rSlice i A) ε := by
  intro U hU
  have hrow : ∀ j : Fin (d + 1) → ℕ, InDisc p (fun kc : ℕ × ℕ =>
      U (Function.update (Function.update j i.castSucc kc.1) (Fin.last d) kc.2)) :=
    fun j k => hU _
  exact ⟨fun j => (hA _ (hrow j)).1 _, fun j => (hA _ (hrow j)).2 _⟩

theorem lip_rSlice {d : ℕ} (i : Fin d) {A : ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)} (hA : SupLip A) :
    SupLip (rSlice i A) :=
  fun x y δ h j => hA _ _ δ (fun k => h _) _

theorem fp_rComp {d : ℕ} (p : ℕ) {Aa : Fin d → ((ℕ × ℕ) → ℤ × ℤ) → ((ℕ × ℕ) → ℤ × ℤ)}
    {A : Fin d → ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)} {ε : Fin d → ℝ}
    (hA : ∀ i, FPApprox p (Aa i) (A i) (ε i)) (hL : ∀ i, SupLip (A i)) :
    ∀ l : List (Fin d), FPApprox p (rComp Aa l) (rComp A l) (l.map ε).sum ∧ SupLip (rComp A l)
  | [] => ⟨by simpa [rComp] using fp_id p, fun _ _ _ h k => h k⟩
  | i :: l => by
    obtain ⟨h1, h2⟩ := fp_rComp p hA hL l
    refine ⟨?_, lip_comp (lip_rSlice i (hL i)) h2⟩
    have := fp_comp p (fp_rSlice p i (hA i)) h1 h2
    simpa [rComp] using this

theorem fp_rTensor {d : ℕ} (p : ℕ) (Aa : Fin d → ((ℕ × ℕ) → ℤ × ℤ) → ((ℕ × ℕ) → ℤ × ℤ))
    (A : Fin d → ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)) (ε : Fin d → ℝ)
    (hA : ∀ i, FPApprox p (Aa i) (A i) (ε i)) (hL : ∀ i, SupLip (A i)) :
    FPApprox p (rTensor Aa) (rTensor A) (∑ i, ε i) ∧ SupLip (rTensor A) := by
  have h := fp_rComp p hA hL (List.finRange d)
  rw [Fin.sum_univ_def]
  exact h

theorem fp_negIdx {p e : ℕ} {Aa : ((ℕ × ℕ) → ℤ × ℤ) → ((ℕ × ℕ) → ℤ × ℤ)}
    {A : ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)} {ε : ℝ} (hA : FPApprox p Aa A ε) :
    FPApprox p (negIdx e ∘ Aa) (negIdx e ∘ A) ε := by
  intro U hU
  obtain ⟨h1, h2⟩ := hA U hU
  exact ⟨fun kc => h1 _, fun kc => h2 _⟩

theorem lip_negIdx {e : ℕ} {A : ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)} (hA : SupLip A) :
    SupLip (negIdx e ∘ A) :=
  fun x y δ h kc => hA x y δ h _

/-- **Proposition 3.3.** -/
theorem synGad_approx {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) :
    FPApprox p (synGad r e) (synGd r e) (∑ i, (e i : ℝ)) ∧ SupLip (synGd r e) :=
  fp_rTensor p _ _ _ (fun i => SynPf.synGa_approx p r (e i)) (fun i => SynPf.synG_lip r (e i))

theorem synGadInv_approx {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) :
    FPApprox p (synGadInv r e) (synGdInv r e) (∑ i, (e i : ℝ)) ∧ SupLip (synGdInv r e) :=
  fp_rTensor p _ _ _ (fun i => fp_negIdx (SynPf.synGa_approx p r (e i)))
    (fun i => lip_negIdx (SynPf.synG_lip r (e i)))


/-! ### Pointwise products in `R` -/

lemma negaCoeff_bound (r : ℕ) (a b : ℕ → ℂ) (c : ℕ) (hc : c < r) (A B : ℝ)
    (ha : ∀ i, i < r → ‖a i‖ ≤ A) (hb : ∀ i, i < r → ‖b i‖ ≤ B) (hA : 0 ≤ A) :
    ‖negaCoeff r a b c‖ ≤ r * (A * B) := by
  unfold negaCoeff
  have h1 : ‖∑ i ∈ Finset.range (c + 1), a i * b (c - i)‖ ≤ ((c + 1 : ℕ) : ℝ) * (A * B) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ Finset.range (c + 1), ‖a i * b (c - i)‖ ≤ A * B := by
      intro i hi; rw [Finset.mem_range] at hi; rw [norm_mul]
      exact mul_le_mul (ha i (by omega)) (hb _ (by omega)) (norm_nonneg _) hA
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 : ‖∑ i ∈ Finset.Ico (c + 1) r, a i * b (c + r - i)‖ ≤ ((r - (c + 1) : ℕ) : ℝ) * (A * B) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ Finset.Ico (c + 1) r, ‖a i * b (c + r - i)‖ ≤ A * B := by
      intro i hi; rw [Finset.mem_Ico] at hi; rw [norm_mul]
      exact mul_le_mul (ha i (by omega)) (hb _ (by omega)) (norm_nonneg _) hA
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h3 : ((r - (c + 1) : ℕ) : ℝ) + ((c + 1 : ℕ) : ℝ) = r := by
    rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by rw [← h3]; ring

lemma negaCoeff_sub (r : ℕ) (a b a' b' : ℕ → ℂ) (c : ℕ) :
    negaCoeff r a b c - negaCoeff r a' b' c =
      negaCoeff r (fun i => a i - a' i) b c + negaCoeff r a' (fun i => b i - b' i) c := by
  simp only [negaCoeff, sub_mul, mul_sub, Finset.sum_sub_distrib]; ring

lemma mulPt_norm {d : ℕ} (r : ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ) (hu : ∀ x, ‖u x‖ ≤ 1)
    (hv : ∀ x, ‖v x‖ ≤ 1) (j : Fin (d + 1) → ℕ) : ‖mulPt r u v j‖ ≤ 1 := by
  unfold mulPt
  split_ifs with h
  · have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    rw [norm_div, Complex.norm_natCast, div_le_one hr]
    have := negaCoeff_bound r (fun c => u (Function.update j (Fin.last d) c)) (fun c => v (Function.update j (Fin.last d) c)) _ h 1 1 (fun i _ => hu _) (fun i _ => hv _) zero_le_one
    linarith
  · simp

lemma mulPt_lip {d : ℕ} (r : ℕ) (u v u' v' : (Fin (d + 1) → ℕ) → ℂ) (δ₁ δ₂ : ℝ)
    (hu' : ∀ x, ‖u' x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (h₁ : ∀ x, ‖u x - u' x‖ ≤ δ₁) (h₂ : ∀ x, ‖v x - v' x‖ ≤ δ₂) (j : Fin (d + 1) → ℕ) :
    ‖mulPt r u v j - mulPt r u' v' j‖ ≤ δ₁ + δ₂ := by
  have hδ₁ : 0 ≤ δ₁ := (norm_nonneg _).trans (h₁ j)
  have hδ₂ : 0 ≤ δ₂ := (norm_nonneg _).trans (h₂ j)
  unfold mulPt
  split_ifs with h
  · have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    rw [← sub_div, negaCoeff_sub, norm_div, Complex.norm_natCast, div_le_iff₀ hr]
    have e1 := negaCoeff_bound r (fun c => u (Function.update j (Fin.last d) c) - u' (Function.update j (Fin.last d) c)) (fun c => v (Function.update j (Fin.last d) c)) _ h δ₁ 1 (fun i _ => h₁ _) (fun i _ => hv _) hδ₁
    have e2 := negaCoeff_bound r (fun c => u' (Function.update j (Fin.last d) c)) (fun c => v (Function.update j (Fin.last d) c) - v' (Function.update j (Fin.last d) c)) _ h 1 δ₂ (fun i _ => hu' _) (fun i _ => h₂ _) zero_le_one
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring
  · simp; positivity


lemma getD_map_range {α : Type*} (f : ℕ → α) (r i : ℕ) (x : α) :
    ((List.range r).map f).getD i x = if i < r then f i else x := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h <;> simp [h]

lemma tdiv_eq_rho0 (W : ℤ) (N : ℕ) (hN : 0 < N) : W.tdiv N = rho0 ((W : ℝ) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold rho0
  split_ifs with h
  · have hW : 0 ≤ W := by
      have : (0 : ℝ) ≤ W := by
        by_contra hc; push_neg at hc
        have := div_neg_of_neg_of_pos hc hN'; linarith
      exact_mod_cast this
    rw [Int.tdiv_eq_ediv_of_nonneg hW, Int.floor_div_natCast, Int.floor_intCast]
  · have hW : W < 0 := by
      by_contra hc; push_neg at hc
      exact h (div_nonneg (by exact_mod_cast hc) hN'.le)
    have e : (W : ℝ) / N = -(((-W : ℤ) : ℝ) / N) := by push_cast; ring
    rw [e, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast,
      ← Int.tdiv_eq_ediv_of_nonneg (by omega), Int.neg_tdiv, neg_neg]

lemma listSub_getD (n : ℕ) (a b : List ℤ) (ha : a.length ≤ n) (hb : b.length ≤ n) (k : ℕ) :
    (listSub n a b).getD k 0 = a.getD k 0 - b.getD k 0 := by
  unfold listSub; rw [getD_map_range]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]; simp

lemma listAdd_getD (n : ℕ) (a b : List ℤ) (ha : a.length ≤ n) (hb : b.length ≤ n) (k : ℕ) :
    (listAdd n a b).getD k 0 = a.getD k 0 + b.getD k 0 := by
  unfold listAdd; rw [getD_map_range]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]; simp

lemma negFold_getD (r : ℕ) (l : List ℤ) (c : ℕ) (hc : c < r) :
    (negFold r l).getD c 0 = l.getD c 0 - l.getD (c + r) 0 := by
  unfold negFold; rw [getD_map_range, if_pos hc]

lemma polyMul_getD_low (a b : List ℤ) (r : ℕ) (ha : a.length = r) (hb : b.length = r) (c : ℕ)
    (hc : c < r) : (polyMul a b).getD c 0 =
      ∑ i ∈ Finset.range (c + 1), a.getD i 0 * b.getD (c - i) 0 := by
  unfold polyMul; rw [getD_map_range, if_pos (by omega)]

lemma polyMul_getD_high (a b : List ℤ) (r : ℕ) (ha : a.length = r) (hb : b.length = r) (c : ℕ)
    (hc : c < r) : (polyMul a b).getD (c + r) 0 =
      ∑ i ∈ Finset.Ico (c + 1) r, a.getD i 0 * b.getD (c + r - i) 0 := by
  unfold polyMul; rw [getD_map_range]
  split_ifs with h
  · rw [← Finset.sum_range_add_sum_Ico _ (show c + 1 ≤ c + r + 1 by omega),
      ← Finset.sum_Ico_consecutive _ (show c + 1 ≤ r by omega) (show r ≤ c + r + 1 by omega)]
    have h1 : ∑ i ∈ Finset.range (c + 1), a.getD i 0 * b.getD (c + r - i) 0 = 0 := by
      apply Finset.sum_eq_zero; intro i hi; rw [Finset.mem_range] at hi
      rw [show b.getD (c + r - i) 0 = 0 from List.getD_eq_default _ _ (by omega)]; simp
    have h2 : ∑ i ∈ Finset.Ico r (c + r + 1), a.getD i 0 * b.getD (c + r - i) 0 = 0 := by
      apply Finset.sum_eq_zero; intro i hi; rw [Finset.mem_Ico] at hi
      rw [show a.getD i 0 = 0 from List.getD_eq_default _ _ (by omega)]; simp
    rw [h1, h2]; ring
  · have : r ≤ c + 1 := by omega
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]

lemma gC_mul (a b : ℤ × ℤ) : gC a * gC b =
    ((a.1 * b.1 - a.2 * b.2 : ℤ) : ℂ) + ((a.1 * b.2 + a.2 * b.1 : ℤ) : ℂ) * Complex.I := by
  simp only [gC]; push_cast; ring_nf; rw [Complex.I_sq]; ring

lemma negaCoeff_div (r : ℕ) (a b : ℕ → ℂ) (s : ℂ) (c : ℕ) :
    negaCoeff r (fun i => a i / s) (fun i => b i / s) c = negaCoeff r a b c / s ^ 2 := by
  simp only [negaCoeff, sub_div, Finset.sum_div]
  congr 1 <;> (apply Finset.sum_congr rfl; intro i _; ring)

lemma abs_fst_le {p : ℕ} (z : ℤ × ℤ) (h : ‖gC z‖ ≤ 2 ^ p) : |z.1| ≤ 2 ^ p := by
  have h1 := Complex.abs_re_le_norm (gC z)
  rw [SynPf.gC_re] at h1
  rw [← Int.cast_abs] at h1
  have : ((|z.1| : ℤ) : ℝ) ≤ 2 ^ p := by linarith
  exact_mod_cast this

lemma abs_snd_le {p : ℕ} (z : ℤ × ℤ) (h : ‖gC z‖ ≤ 2 ^ p) : |z.2| ≤ 2 ^ p := by
  have h1 := Complex.abs_im_le_norm (gC z)
  rw [SynPf.gC_im] at h1
  rw [← Int.cast_abs] at h1
  have : ((|z.2| : ℤ) : ℝ) ≤ 2 ^ p := by linarith
  exact_mod_cast this

lemma gC_tdiv_eq (A B : ℤ) (N : ℕ) (hN : 0 < N) (z : ℂ) (hz : z = ((A : ℂ) + (B : ℂ) * Complex.I) / N) :
    gC (A.tdiv N, B.tdiv N) = rho0C z := by
  have e : z = (((A : ℝ) / N : ℝ) : ℂ) + (((B : ℝ) / N : ℝ) : ℂ) * Complex.I := by
    rw [hz]; push_cast; ring
  have hre : z.re = (A : ℝ) / N := by rw [e]; simp
  have him : z.im = (B : ℝ) / N := by rw [e]; simp
  unfold gC rho0C
  rw [hre, him, tdiv_eq_rho0 A N hN, tdiv_eq_rho0 B N hN]

/-- The fixed-point pointwise product is the exact one, rounded towards zero (Lemma 2.5). -/
theorem mulPtZ_gC {d : ℕ} (p r : ℕ) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc p U) (hV : InDisc p V) (j : Fin (d + 1) → ℕ) :
    gC (mulPtZ p r U V j) =
      rho0C ((2 : ℂ) ^ p * mulPt r (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j) := by
  set c := j (Fin.last d) with hcdef
  set Uc : ℕ → ℤ × ℤ := fun i => U (Function.update j (Fin.last d) i)
  set Vc : ℕ → ℤ × ℤ := fun i => V (Function.update j (Fin.last d) i)
  have hl : ∀ (W : (Fin (d + 1) → ℕ) → ℤ × ℤ) (f : ℤ × ℤ → ℤ),
      ((coeffList r W j).map f) = (List.range r).map (fun i => f (W (Function.update j (Fin.last d) i))) := by
    intro W f; simp [coeffList, List.map_map, Function.comp_def]
  have hlen : ∀ (W : (Fin (d + 1) → ℕ) → ℤ × ℤ) (f : ℤ × ℤ → ℤ), ((coeffList r W j).map f).length = r := by
    intro W f; rw [hl]; simp
  have hb : ∀ (W : (Fin (d + 1) → ℕ) → ℤ × ℤ), InDisc p W → ∀ x ∈ (coeffList r W j).map Prod.fst, |x| ≤ 2 ^ p := by
    intro W hW x hx; rw [hl] at hx; simp only [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx; exact abs_fst_le _ (hW _)
  have hb' : ∀ (W : (Fin (d + 1) → ℕ) → ℤ × ℤ), InDisc p W → ∀ x ∈ (coeffList r W j).map Prod.snd, |x| ≤ 2 ^ p := by
    intro W hW x hx; rw [hl] at hx; simp only [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx; exact abs_snd_le _ (hW _)
  unfold mulPtZ
  rw [KronPf.mulR_eq_spec p r _ _ _ _ (hlen _ _) (hlen _ _) (hlen _ _) (hlen _ _) (hb U hU) (hb' U hU)
    (hb V hV) (hb' V hV) hr hrp]
  unfold mulRSpec mulPt
  simp only []
  rw [getD_map_range]
  split_ifs with hc
  · rw [← hcdef] at hc ⊢
    have hpl : ∀ (a b : List ℤ), a.length = r → b.length = r → (polyMul a b).length ≤ 2 * r - 1 := by
      intro a b ha hb; rw [KronPf.polyMul_length, ha, hb]; omega
    have hg : ∀ (W : (Fin (d + 1) → ℕ) → ℤ × ℤ) (f : ℤ × ℤ → ℤ) (i : ℕ), i < r →
        ((coeffList r W j).map f).getD i 0 = f (W (Function.update j (Fin.last d) i)) := by
      intro W f i hi; rw [hl, getD_map_range, if_pos hi]
    have hlow : ∀ (W W' : (Fin (d + 1) → ℕ) → ℤ × ℤ) (f g : ℤ × ℤ → ℤ),
        (polyMul ((coeffList r W j).map f) ((coeffList r W' j).map g)).getD c 0 =
          ∑ i ∈ Finset.range (c + 1), f (W (Function.update j (Fin.last d) i)) *
            g (W' (Function.update j (Fin.last d) (c - i))) := by
      intro W W' f g
      rw [polyMul_getD_low _ _ r (hlen _ _) (hlen _ _) c hc]
      apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
      rw [hg _ _ _ (by omega), hg _ _ _ (by omega)]
    have hhigh : ∀ (W W' : (Fin (d + 1) → ℕ) → ℤ × ℤ) (f g : ℤ × ℤ → ℤ),
        (polyMul ((coeffList r W j).map f) ((coeffList r W' j).map g)).getD (c + r) 0 =
          ∑ i ∈ Finset.Ico (c + 1) r, f (W (Function.update j (Fin.last d) i)) *
            g (W' (Function.update j (Fin.last d) (c + r - i))) := by
      intro W W' f g
      rw [polyMul_getD_high _ _ r (hlen _ _) (hlen _ _) c hc]
      apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_Ico] at hi
      rw [hg _ _ _ (by omega), hg _ _ _ (by omega)]
    rw [negFold_getD _ _ _ hc, negFold_getD _ _ _ hc,
      listSub_getD _ _ _ (hpl _ _ (hlen _ _) (hlen _ _)) (hpl _ _ (hlen _ _) (hlen _ _)),
      listSub_getD _ _ _ (hpl _ _ (hlen _ _) (hlen _ _)) (hpl _ _ (hlen _ _) (hlen _ _)),
      listAdd_getD _ _ _ (hpl _ _ (hlen _ _) (hlen _ _)) (hpl _ _ (hlen _ _) (hlen _ _)),
      listAdd_getD _ _ _ (hpl _ _ (hlen _ _) (hlen _ _)) (hpl _ _ (hlen _ _) (hlen _ _)),
      hlow, hlow, hlow, hlow, hhigh, hhigh, hhigh, hhigh]
    have hN : (0 : ℕ) < 2 ^ p * r := by positivity
    rw [show (2 : ℤ) ^ p * (r : ℤ) = ((2 ^ p * r : ℕ) : ℤ) by push_cast; ring]
    apply gC_tdiv_eq _ _ _ hN
    rw [negaCoeff_div]
    have hX : negaCoeff r (fun c => gC (U (Function.update j (Fin.last d) c)))
        (fun c => gC (V (Function.update j (Fin.last d) c))) c =
        (((∑ i ∈ Finset.range (c + 1), (U (Function.update j (Fin.last d) i)).1 *
            (V (Function.update j (Fin.last d) (c - i))).1 -
          ∑ i ∈ Finset.range (c + 1), (U (Function.update j (Fin.last d) i)).2 *
            (V (Function.update j (Fin.last d) (c - i))).2) -
          (∑ i ∈ Finset.Ico (c + 1) r, (U (Function.update j (Fin.last d) i)).1 *
            (V (Function.update j (Fin.last d) (c + r - i))).1 -
          ∑ i ∈ Finset.Ico (c + 1) r, (U (Function.update j (Fin.last d) i)).2 *
            (V (Function.update j (Fin.last d) (c + r - i))).2) : ℤ) : ℂ) +
        (((∑ i ∈ Finset.range (c + 1), (U (Function.update j (Fin.last d) i)).1 *
            (V (Function.update j (Fin.last d) (c - i))).2 +
          ∑ i ∈ Finset.range (c + 1), (U (Function.update j (Fin.last d) i)).2 *
            (V (Function.update j (Fin.last d) (c - i))).1) -
          (∑ i ∈ Finset.Ico (c + 1) r, (U (Function.update j (Fin.last d) i)).1 *
            (V (Function.update j (Fin.last d) (c + r - i))).2 +
          ∑ i ∈ Finset.Ico (c + 1) r, (U (Function.update j (Fin.last d) i)).2 *
            (V (Function.update j (Fin.last d) (c + r - i))).1) : ℤ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [negaCoeff, gC, Complex.re_sum, Complex.im_sum, Finset.sum_sub_distrib,
          Finset.sum_add_distrib] <;> ring
    rw [hX]
    have h2 : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    push_cast
    field_simp
  · simp [gC, rho0C, rho0]


/-! ### Scaling by a power of two (Lemma 2.2) -/

lemma ceilSqrt_real (N : ℕ) : Real.sqrt N ≤ ceilSqrt N ∧ (ceilSqrt N : ℝ) < Real.sqrt N + 1 := by
  have h1 := Nat.sqrt_le' N
  have h2 := Nat.lt_succ_sqrt' N
  have hs : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast h1)
  unfold ceilSqrt
  split_ifs with h
  · refine ⟨?_, ?_⟩
    · push_cast
      calc Real.sqrt N ≤ Real.sqrt (((Nat.sqrt N : ℝ) + 1) ^ 2) :=
            Real.sqrt_le_sqrt (by exact_mod_cast h2.le)
        _ = (Nat.sqrt N : ℝ) + 1 := Real.sqrt_sq (by positivity)
    · have : ((Nat.sqrt N : ℕ) : ℝ) < Real.sqrt N :=
        (Real.lt_sqrt (by positivity)).2 (by rw [sq]; exact_mod_cast h)
      push_cast; linarith
  · have e : Nat.sqrt N * Nat.sqrt N = N := by
      have := Nat.sqrt_le N; omega
    have : Real.sqrt N = Nat.sqrt N := by
      rw [show (N : ℝ) = (Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ) by exact_mod_cast e.symm]
      exact Real.sqrt_mul_self (Nat.cast_nonneg _)
    rw [this]; exact ⟨le_refl _, by linarith⟩

lemma norm_gC_eq (z : ℤ × ℤ) : ‖gC z‖ = Real.sqrt ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, SynPf.gC_re, SynPf.gC_im]

theorem scaleZ_bound (p k : ℕ) (z : ℤ × ℤ) (w : ℂ) (hw : ‖(2 : ℂ) ^ k * w‖ ≤ 1) :
    ‖gC (scaleZ p k z)‖ ≤ 2 ^ p ∧
      ‖gC (scaleZ p k z) - 2 ^ p * (2 ^ k * w)‖ ≤ 2 * 2 ^ k * ‖gC z - 2 ^ p * w‖ + 3 := by
  set W : ℤ × ℤ := (2 ^ k * z.1, 2 ^ k * z.2) with hWdef
  have hgW : gC W = 2 ^ k * gC z := by simp only [W, gC]; push_cast; ring
  set D := ‖gC W - 2 ^ p * (2 ^ k * w)‖ with hD
  have hD' : D = 2 ^ k * ‖gC z - 2 ^ p * w‖ := by
    rw [hD, hgW, show (2 : ℂ) ^ k * gC z - 2 ^ p * (2 ^ k * w) = 2 ^ k * (gC z - 2 ^ p * w) by ring,
      norm_mul, norm_pow, Complex.norm_two]
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hT : ‖(2 : ℂ) ^ p * (2 ^ k * w)‖ ≤ 2 ^ p := by
    rw [norm_mul, norm_pow, Complex.norm_two]
    calc _ ≤ (2 : ℝ) ^ p * 1 := mul_le_mul_of_nonneg_left hw hp.le
      _ = _ := mul_one _
  have ha : ‖gC W‖ ≤ D + 2 ^ p := by
    have := norm_sub_norm_le (gC W) (2 ^ p * (2 ^ k * w)); linarith
  have hDnn : 0 ≤ D := norm_nonneg _
  have hW2 : ‖gC W‖ ^ 2 = ((W.1 ^ 2 + W.2 ^ 2 : ℤ) : ℝ) := by
    rw [norm_gC_eq, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hsc : scaleZ p k z = if W.1 ^ 2 + W.2 ^ 2 ≤ 4 ^ p then W else
      ((W.1 * 2 ^ p).tdiv (ceilSqrt (W.1 ^ 2 + W.2 ^ 2).toNat : ℤ),
        (W.2 * 2 ^ p).tdiv (ceilSqrt (W.1 ^ 2 + W.2 ^ 2).toNat : ℤ)) := rfl
  rw [hsc]
  rw [show 2 * 2 ^ k * ‖gC z - 2 ^ p * w‖ = 2 * D by rw [hD']; ring]
  split_ifs with h
  · refine ⟨?_, by linarith⟩
    have : ‖gC W‖ ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
      rw [hW2, ← pow_mul, mul_comm, pow_mul]; norm_num; exact_mod_cast h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hp.le (by norm_num)).1 this
  · push_neg at h
    set N : ℕ := (W.1 ^ 2 + W.2 ^ 2).toNat with hN
    have hNr : (N : ℝ) = ‖gC W‖ ^ 2 := by
      rw [hW2]
      have hz : ((N : ℕ) : ℤ) = W.1 ^ 2 + W.2 ^ 2 := Int.toNat_of_nonneg (by positivity)
      rw [← hz]; norm_cast
    have hsq : Real.sqrt N = ‖gC W‖ := by rw [hNr, Real.sqrt_sq (norm_nonneg _)]
    obtain ⟨hm1, hm2⟩ := ceilSqrt_real N
    rw [hsq] at hm1 hm2
    have hagt : (2 : ℝ) ^ p < ‖gC W‖ := by
      have : ((2 : ℝ) ^ p) ^ 2 < ‖gC W‖ ^ 2 := by
        rw [hW2, ← pow_mul, mul_comm, pow_mul]; norm_num; exact_mod_cast h
      exact (pow_lt_pow_iff_left₀ hp.le (norm_nonneg _) (by norm_num)).1 this
    set m := ceilSqrt N with hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hm0' : 0 < m := by exact_mod_cast hm0
    set X : ℂ := gC W * 2 ^ p / m with hX
    have hR : gC ((W.1 * 2 ^ p).tdiv (m : ℤ), (W.2 * 2 ^ p).tdiv (m : ℤ)) = rho0C X := by
      apply gC_tdiv_eq _ _ _ hm0'
      rw [hX]; simp only [gC]; push_cast; ring
    rw [hR]
    have hXn : ‖X‖ = ‖gC W‖ * 2 ^ p / m := by
      rw [hX, norm_div, norm_mul, norm_pow, Complex.norm_two, Complex.norm_natCast]
    have hXle : ‖X‖ ≤ 2 ^ p := by
      rw [hXn, div_le_iff₀ hm0]; nlinarith [norm_nonneg (gC W)]
    refine ⟨(FP.norm_rho0C_le X).trans hXle, ?_⟩
    have h1 := FP.norm_rho0C_sub_lt X
    have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h2 : ‖X - gC W‖ ≤ ‖gC W‖ - 2 ^ p + 1 := by
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0'.ne'
      have e : X - gC W = gC W * ((2 ^ p - m) / m : ℂ) := by
        rw [hX]; field_simp; try ring
      rw [e, norm_mul]
      have e2 : ((2 : ℂ) ^ p - m) / m = (((2 : ℝ) ^ p - m) / m : ℝ) := by push_cast; ring
      rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
      · rw [div_eq_mul_inv]
        have key : ‖gC W‖ * (-(((2 : ℝ) ^ p - m) * (m : ℝ)⁻¹)) ≤ ‖gC W‖ - 2 ^ p + 1 := by
          rw [show ‖gC W‖ * (-(((2 : ℝ) ^ p - m) * (m : ℝ)⁻¹)) = ‖gC W‖ - ‖gC W‖ * 2 ^ p / m by
            field_simp; ring]
          have : (2 : ℝ) ^ p - 1 ≤ ‖gC W‖ * 2 ^ p / m := by
            rw [le_div_iff₀ hm0]; nlinarith
          linarith
        linarith
      · apply div_nonpos_of_nonpos_of_nonneg _ hm0.le; linarith
    have e : rho0C X - 2 ^ p * (2 ^ k * w) = (rho0C X - X) + (X - gC W) + (gC W - 2 ^ p * (2 ^ k * w)) := by
      ring
    rw [e]
    calc _ ≤ ‖(rho0C X - X) + (X - gC W)‖ + D := norm_add_le _ _
      _ ≤ ‖rho0C X - X‖ + ‖X - gC W‖ + D := by gcongr; exact norm_add_le _ _
      _ ≤ 2 * D + 3 := by linarith

end IntMul.HvdH.CRPf


open Finset

namespace IntMul.HvdH.Syn

variable {R : Type*} [CommRing R]

/-- Radix-2 Cooley–Tukey, even outputs. -/
theorem ct_even (m : ℕ) (ω : R) (hω : ω ^ m = -1) (u : ℕ → R) (l : ℕ) :
    ∑ k ∈ range (2 * m), ω ^ (2 * l * k) * u k =
      ∑ k ∈ range m, (ω ^ 2) ^ (l * k) * (u k + u (k + m)) := by
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : ω ^ (2 * l * (m + k)) = ω ^ (2 * l * k) := by
    rw [show 2 * l * (m + k) = 2 * l * k + m * (2 * l) by ring, pow_add, pow_mul ω m, hω,
      pow_mul (-1 : R) 2, neg_one_sq, one_pow, mul_one]
  rw [this, ← pow_mul, show 2 * (l * k) = 2 * l * k by ring, add_comm m k]; ring

/-- Radix-2 Cooley–Tukey, odd outputs (with the twiddle factor `ω^k`). -/
theorem ct_odd (m : ℕ) (ω : R) (hω : ω ^ m = -1) (u : ℕ → R) (l : ℕ) :
    ∑ k ∈ range (2 * m), ω ^ ((2 * l + 1) * k) * u k =
      ∑ k ∈ range m, (ω ^ 2) ^ (l * k) * (ω ^ k * (u k - u (k + m))) := by
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : ω ^ ((2 * l + 1) * (m + k)) = -ω ^ ((2 * l + 1) * k) := by
    rw [show (2 * l + 1) * (m + k) = (2 * l + 1) * k + m * (2 * l + 1) by ring, pow_add, pow_mul ω m,
      hω, pow_succ, pow_mul (-1 : R) 2, neg_one_sq, one_pow]; ring
  have h2 : ω ^ ((2 * l + 1) * k) = (ω ^ 2) ^ (l * k) * ω ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [this, h2, add_comm m k]; ring

lemma sum_block (x : R) (L : ℕ) (hx : x ^ L = -1) (c : ℕ) :
    ∑ k ∈ range (2 * L * c), x ^ k = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show 2 * L * (c + 1) = 2 * L * c + (L + L) by ring, Finset.sum_range_add, ih, zero_add,
      Finset.sum_range_add]
    have : ∑ i ∈ range L, x ^ (2 * L * c + (L + i)) =
        x ^ L * ∑ i ∈ range L, x ^ (2 * L * c + i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← pow_add]; congr 1; ring
    rw [this, hx]; ring

/-- If `ω^{2^e} = -1` then `ω` is a principal `2^{e+1}`-th root of unity. -/
theorem sum_pow_eq_zero (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (j : ℕ)
    (hj : ¬ 2 ^ (e + 1) ∣ j) : ∑ k ∈ range (2 ^ (e + 1)), ω ^ (j * k) = 0 := by
  have hj0 : j ≠ 0 := by rintro rfl; exact hj (dvd_zero _)
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hj0
  have ha : a ≤ e := by
    by_contra h
    exact hj (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) b)
  have hx : (ω ^ (2 ^ a * b)) ^ (2 ^ (e - a)) = -1 := by
    rw [← pow_mul, show 2 ^ a * b * 2 ^ (e - a) = 2 ^ e * b by
      rw [mul_comm (2 ^ a) b, mul_assoc, ← pow_add, Nat.add_sub_cancel' ha, mul_comm],
      pow_mul, hω, hb.neg_one_pow]
  have := sum_block (ω ^ (2 ^ a * b)) (2 ^ (e - a)) hx (2 ^ a)
  rw [show 2 * 2 ^ (e - a) * 2 ^ a = 2 ^ (e + 1) by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel ha, pow_succ, mul_comm]] at this
  simpa [← pow_mul] using this

lemma pow_mod_eq (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (m : ℕ) :
    ω ^ m = ω ^ (m % 2 ^ (e + 1)) := by
  have h1 : ω ^ (2 ^ (e + 1)) = 1 := by
    rw [pow_succ, pow_mul, hω, neg_one_sq]
  conv_lhs => rw [← Nat.div_add_mod m (2 ^ (e + 1)), pow_add, pow_mul, h1, one_pow, one_mul]

lemma pow_val_add (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (a b : ZMod (2 ^ (e + 1))) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [ZMod.val_add, ← pow_mod_eq e ω hω, pow_add]

lemma pow_val_mul (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (a b : ZMod (2 ^ (e + 1))) :
    ω ^ (a * b).val = ω ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← pow_mod_eq e ω hω]

lemma sum_char (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (a : ZMod (2 ^ (e + 1))) :
    ∑ t : ZMod (2 ^ (e + 1)), ω ^ (t * a).val = if a = 0 then ((2 ^ (e + 1) : ℕ) : R) else 0 := by
  have e1 : ∑ t : ZMod (2 ^ (e + 1)), ω ^ (t * a).val =
      ∑ k ∈ range (2 ^ (e + 1)), ω ^ (a.val * k) := by
    refine Finset.sum_nbij' (fun t => t.val) (fun k => (k : ZMod (2 ^ (e + 1)))) (fun t _ => ?_)
      (fun k _ => Finset.mem_univ _) (fun t _ => ZMod.natCast_zmod_val t) (fun k hk => ?_)
      (fun t _ => ?_)
    · exact Finset.mem_range.2 (ZMod.val_lt t)
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hk)]
    · rw [pow_val_mul e ω hω, mul_comm]
  rw [e1]
  split_ifs with ha
  · subst ha; simp
  · apply sum_pow_eq_zero e ω hω
    intro hd
    have h1 := ZMod.val_lt a
    have h2 : a.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
    exact h2 (Nat.eq_zero_of_dvd_of_lt hd h1)

/-- **Convolution formula over a ring with principal power-of-two roots** (Lemma 2.3 / (2.1) of
Harvey–van der Hoeven, synthetic case). If `ω i ^ (2 ^ e i) = -1` then `ω i` is a principal
`2^(e i + 1)`-th root of unity and multidimensional cyclic convolution is computed by the
corresponding transforms: `N · (u ∗ v) = F_{ω⁻¹}(F_ω u · F_ω v)` (unnormalised). -/
theorem synthetic_conv {d : ℕ} (e : Fin d → ℕ) (ω : Fin d → R) (hω : ∀ i, ω i ^ (2 ^ e i) = -1)
    (u v : ((i : Fin d) → ZMod (2 ^ (e i + 1))) → R) (j : (i : Fin d) → ZMod (2 ^ (e i + 1))) :
    (∏ i, ((2 ^ (e i + 1) : ℕ) : R)) * ∑ k, u k * v (j - k) =
      ∑ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), (∏ i, ω i ^ (t i * j i).val) *
        ((∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * u k) *
          (∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * v k)) := by
  -- expand the right-hand side
  have hR : ∀ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), (∏ i, ω i ^ (t i * j i).val) *
      ((∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * u k) *
        (∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * v k)) =
      ∑ k, ∑ l, u k * v l * ∏ i, ω i ^ (t i * (j i - k i - l i)).val := by
    intro t
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hc : ∀ i, ω i ^ (t i * (j i - k i - l i)).val =
        ω i ^ (t i * j i).val * (ω i ^ (-(t i * k i)).val * ω i ^ (-(t i * l i)).val) := by
      intro i
      rw [← pow_val_add (e i) (ω i) (hω i), ← pow_val_add (e i) (ω i) (hω i)]
      congr 2; ring
    simp only [hc, Finset.prod_mul_distrib]
    ring
  simp only [hR]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hs : ∀ l : (i : Fin d) → ZMod (2 ^ (e i + 1)),
      ∑ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), ∏ i, ω i ^ (t i * (j i - k i - l i)).val =
        if j - k = l then ∏ i, ((2 ^ (e i + 1) : ℕ) : R) else 0 := by
    intro l
    rw [← Fintype.prod_sum (fun i (x : ZMod (2 ^ (e i + 1))) => ω i ^ (x * (j i - k i - l i)).val)]
    simp only [sum_char _ _ (hω _)]
    rw [Finset.prod_ite_zero]
    congr 1
    apply propext
    constructor
    · intro h; funext i; have := h i (Finset.mem_univ _)
      rw [sub_sub, sub_eq_zero] at this; rw [Pi.sub_apply, this]; ring
    · intro h i _; rw [← h]; simp
  simp only [hs, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

end IntMul.HvdH.Syn


open Complex

namespace IntMul.HvdH.SynId
open IntMul.HvdH

/-- Evaluation of a coefficient array at `z` (a root of `y^r + 1`). -/
noncomputable def ev (r : ℕ) (z : ℂ) (a : ℕ → ℂ) : ℂ := ∑ c ∈ Finset.range r, a c * z ^ c

/-- Negacyclic extension of a coefficient array to `ℤ`. -/
noncomputable def negExt (r : ℕ) (a : ℕ → ℂ) (n : ℤ) : ℂ := (-1 : ℂ) ^ (n / r) * a (n % r).toNat

lemma yShift_negExt (r : ℕ) (m : ℤ) (a : ℕ → ℂ) (c : ℕ) :
    yShift r m a c = negExt r a ((c : ℤ) - m) := SynEq.yShift_eq r m a c

lemma negExt_of_lt (r : ℕ) (a : ℕ → ℂ) (n : ℕ) (hn : n < r) : negExt r a n = a n := by
  unfold negExt
  have h1 : (n : ℤ) / r = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h2 : (n : ℤ) % r = n := Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1, h2]; simp

lemma negExt_of_neg (r : ℕ) (a : ℕ → ℂ) (n : ℤ) (h0 : n < 0) (h1 : -(r : ℤ) ≤ n) :
    negExt r a n = -a (n + r).toNat := by
  unfold negExt
  have hr : (0 : ℤ) < r := by omega
  obtain ⟨e1, e2⟩ := (Int.ediv_emod_unique hr (a := n) (q := -1) (r := n + r)).2
    ⟨by ring, by omega, by omega⟩
  rw [e1, e2]; simp

lemma negExt_add (r : ℕ) (hr : 0 < r) (a : ℕ → ℂ) (n : ℤ) : negExt r a (n + r) = -negExt r a n := by
  unfold negExt
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [show n + (r : ℤ) = n + 1 * r by ring, Int.add_mul_ediv_right _ _ hr', Int.add_mul_emod_self_right,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

/-- Sums of an `r`-periodic function over any window of length `r` agree. -/
lemma sum_window (r : ℕ) (hr : 0 < r) (f : ℤ → ℂ) (hf : ∀ n, f (n + r) = f n) (s : ℤ) :
    ∑ c ∈ Finset.range r, f (c + s) = ∑ c ∈ Finset.range r, f c := by
  have hper : Function.Periodic f r := hf
  haveI : NeZero r := ⟨hr.ne'⟩
  have key : ∀ n : ℤ, f n = f ((n : ZMod r).val) := by
    intro n
    rw [ZMod.val_intCast]
    conv_lhs => rw [← Int.emod_add_mul_ediv n r]
    rw [show n % r + r * (n / r) = n % r + (n / r) * r by ring]
    exact (hper.int_mul (n / r)) _
  have hsum : ∀ g : ℕ → ℂ, ∑ c ∈ Finset.range r, g c = ∑ x : ZMod r, g x.val := by
    intro g
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    exact (Fin.sum_univ_eq_sum_range g (n + 1)).symm
  rw [hsum (fun c => f (c + s)), hsum (fun c => f c)]
  have h1 : ∀ x : ZMod r, f ((x.val : ℤ) + s) = f ((x + (s : ZMod r)).val) := by
    intro x; rw [key]; congr 2; push_cast; simp
  simp only [h1]
  exact Fintype.sum_equiv (Equiv.addRight (s : ZMod r)) _ _ (fun x => rfl)

lemma per_f (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) (hz0 : z ≠ 0) (a : ℕ → ℂ) (n : ℤ) :
    negExt r a (n + r) * z ^ (n + r) = negExt r a n * z ^ n := by
  rw [negExt_add r hr, zpow_add₀ hz0, zpow_natCast, hz]; ring

lemma ev_eq_sum_f (r : ℕ) (z : ℂ) (a : ℕ → ℂ) :
    ev r z a = ∑ c ∈ Finset.range r, negExt r a c * z ^ (c : ℤ) := by
  unfold ev
  apply Finset.sum_congr rfl; intro c hc; rw [Finset.mem_range] at hc
  rw [negExt_of_lt r a c hc, zpow_natCast]

theorem ev_yShift (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) (hz0 : z ≠ 0) (m : ℤ)
    (a : ℕ → ℂ) : ev r z (fun c => yShift r m a c) = z ^ m * ev r z a := by
  rw [ev_eq_sum_f r z a]
  rw [← sum_window r hr (fun n => negExt r a n * z ^ n) (fun n => per_f r hr z hz hz0 a n) (-m),
    Finset.mul_sum]
  unfold ev
  apply Finset.sum_congr rfl; intro c _
  simp only []
  rw [yShift_negExt, show (c : ℤ) + -m = c - m by ring, zpow_sub₀ hz0, zpow_natCast]
  field_simp

theorem ev_negaCoeff (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) (hz0 : z ≠ 0) (a b : ℕ → ℂ) :
    ev r z (fun c => negaCoeff r a b c) = ev r z a * ev r z b := by
  have hrow : ∀ i : ℕ, a i * z ^ i * ev r z b =
      ∑ l ∈ Finset.range r, a i * negExt r b ((l : ℤ) - i) * z ^ l := by
    intro i
    rw [ev_eq_sum_f r z b,
      ← sum_window r hr (fun n => negExt r b n * z ^ n) (fun n => per_f r hr z hz hz0 b n) (-(i : ℤ)),
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    rw [show (l : ℤ) + -(i : ℤ) = l - i by ring, zpow_sub₀ hz0, zpow_natCast, zpow_natCast]
    field_simp
  have hL : ev r z a * ev r z b = ∑ i ∈ Finset.range r, a i * z ^ i * ev r z b := by
    unfold ev; rw [Finset.sum_mul]
  rw [hL, Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_comm]
  unfold ev
  apply Finset.sum_congr rfl; intro l hl; rw [Finset.mem_range] at hl
  rw [← Finset.sum_mul]
  congr 1
  unfold negaCoeff
  rw [← Finset.sum_range_add_sum_Ico _ (show l + 1 ≤ r by omega)]
  have h1 : ∑ i ∈ Finset.range (l + 1), a i * negExt r b ((l : ℤ) - i) =
      ∑ i ∈ Finset.range (l + 1), a i * b (l - i) := by
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    rw [show (l : ℤ) - i = ((l - i : ℕ) : ℤ) by push_cast [Nat.cast_sub (show i ≤ l by omega)]; ring,
      negExt_of_lt r b _ (by omega)]
  have h2 : ∑ i ∈ Finset.Ico (l + 1) r, a i * negExt r b ((l : ℤ) - i) =
      -∑ i ∈ Finset.Ico (l + 1) r, a i * b (l + r - i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_Ico] at hi
    rw [negExt_of_neg r b _ (by omega) (by omega)]
    rw [show ((l : ℤ) - i + r).toNat = l + r - i by omega]
    ring
  rw [h1, h2]; ring

/-- A coefficient array is determined by its values at the `r` roots of `y^r + 1`. -/
theorem ev_inj (r : ℕ) (hr : 0 < r) (a b : ℕ → ℂ)
    (h : ∀ z : ℂ, z ^ r = -1 → ev r z a = ev r z b) (c : ℕ) (hc : c < r) : a c = b c := by
  classical
  set P : Polynomial ℂ := ∑ i : Fin r, Polynomial.C (a i - b i) * Polynomial.X ^ (i : ℕ) with hP
  have hζ := Complex.isPrimitiveRoot_exp (2 * r) (by omega)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ((2 * r : ℕ) : ℂ))
  have hζr : ζ ^ r = -1 := by
    have h1 : ζ ^ r * ζ ^ r = 1 := by rw [← pow_add, ← two_mul]; exact hζ.pow_eq_one
    have h2 : ζ ^ r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    rcases mul_self_eq_one_iff.1 h1 with h3 | h3
    · exact absurd h3 h2
    · exact h3
  set x : Fin r → ℂ := fun s => ζ ^ (2 * (s : ℕ) + 1)
  have hinj : Function.Injective x := by
    intro s t hst
    have := hζ.pow_inj (by omega) (by omega) hst
    exact Fin.ext (by omega)
  have hroot : ∀ s, x s ^ r = -1 := by
    intro s; simp only [x]
    rw [← pow_mul, mul_comm, pow_mul, hζr, Odd.neg_one_pow ⟨s, rfl⟩]
  have heval : ∀ s, P.eval (x s) = 0 := by
    intro s
    have : P.eval (x s) = ev r (x s) a - ev r (x s) b := by
      simp only [hP, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      unfold ev
      rw [← Finset.sum_sub_distrib]
      rw [Fin.sum_univ_eq_sum_range (fun i => (a i - b i) * x s ^ i) r]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this, h _ (hroot s), sub_self]
  have hP0 : P = 0 := by
    by_contra hne
    have hdeg : P.natDegree < r :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).2 (Polynomial.degree_sum_fin_lt _)
    exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj heval
      (by simpa using hdeg))
  have hcoef := congrArg (fun q => q.coeff c) hP0
  simp only [hP, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hcoef
  rw [Finset.sum_eq_single ⟨c, hc⟩ (fun i _ hi => by
      rw [if_neg (fun h' => hi (Fin.ext h'.symm))]; ring) (by simp)] at hcoef
  simp at hcoef
  exact sub_eq_zero.1 hcoef

/-! ### Evaluating arrays over `R` -/

/-- Evaluate the `R`-entry at position `k` at the root `z`. -/
noncomputable def E (r : ℕ) (z : ℂ) {d : ℕ} (u : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ) : ℂ :=
  ev r z (fun c => u (Fin.snoc k c))

lemma snoc_update_castSucc {d : ℕ} (k : Fin d → ℕ) (c : ℕ) (i : Fin d) (m : ℕ) :
    Function.update (Fin.snoc k c : Fin (d + 1) → ℕ) i.castSucc m = Fin.snoc (Function.update k i m) c := by
  funext x
  refine Fin.lastCases ?_ (fun y => ?_) x
  · rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne', Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc]
    by_cases h : y = i
    · subst h; simp
    · rw [Function.update_of_ne (fun h' => h (Fin.castSucc_injective _ h')), Fin.snoc_castSucc,
        Function.update_of_ne h]

lemma snoc_update_last {d : ℕ} (k : Fin d → ℕ) (c c' : ℕ) :
    Function.update (Fin.snoc k c : Fin (d + 1) → ℕ) (Fin.last d) c' = Fin.snoc k c' := by
  funext x
  refine Fin.lastCases ?_ (fun y => ?_) x
  · simp
  · rw [Function.update_of_ne (Fin.castSucc_lt_last y).ne, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- One `R`-axis transform, evaluated at a root: a generic DFT-type formula. -/
def SliceDFT (r : ℕ) (z : ℂ) {d : ℕ} (i : Fin d) (B : ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)) (t : ℕ)
    (ω : ℂ) : Prop :=
  ∀ (u : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ), k i < t →
    E r z (rSlice i B u) k = (1 / t : ℂ) * ∑ m ∈ Finset.range t, ω ^ (k i * m) * E r z u (Function.update k i m)

lemma rSlice_snoc {d : ℕ} (i : Fin d) (B : ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ))
    (u : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ) (c : ℕ) :
    rSlice i B u (Fin.snoc k c) = B (fun mc => u (Fin.snoc (Function.update k i mc.1) mc.2)) (k i, c) := by
  unfold rSlice
  rw [Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  funext mc
  rw [snoc_update_castSucc, snoc_update_last]

theorem sliceDFT_synG (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) (hz0 : z ≠ 0) {d : ℕ}
    (i : Fin d) (e : ℕ) (he : 2 ^ e ∣ 2 * r) :
    SliceDFT r z i (synG r e) (2 ^ e) (z ^ (2 * r / 2 ^ e))⁻¹ := by
  intro u k hk
  unfold E ev
  simp only [rSlice_snoc]
  have hs : ∀ c ∈ Finset.range r, synG r e (fun mc => u (Fin.snoc (Function.update k i mc.1) mc.2)) (k i, c) * z ^ c
      = (1 / 2 ^ e : ℂ) * ∑ m ∈ Finset.range (2 ^ e),
        yShift r (-((2 * r / 2 ^ e * k i * m : ℕ) : ℤ)) (fun c' => u (Fin.snoc (Function.update k i m) c')) c * z ^ c := by
    intro c hc; rw [Finset.mem_range] at hc
    rw [SynEq.synG_eq r hr e he _ _ _ hk hc, mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, Finset.sum_comm]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl; intro m _
  have := ev_yShift r hr z hz hz0 (-((2 * r / 2 ^ e * k i * m : ℕ) : ℤ))
    (fun c' => u (Fin.snoc (Function.update k i m) c'))
  unfold ev at this
  rw [this, zpow_neg, zpow_natCast, inv_pow, ← pow_mul]
  simp [mul_assoc]

theorem sliceDFT_synGinv (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) (hz0 : z ≠ 0) {d : ℕ}
    (i : Fin d) (e : ℕ) (he : 2 ^ e ∣ 2 * r) :
    SliceDFT r z i (negIdx e ∘ synG r e) (2 ^ e) (z ^ (2 * r / 2 ^ e)) := by
  intro u k hk
  set j' := (2 ^ e - k i % 2 ^ e) % 2 ^ e with hj'
  have hj'lt : j' < 2 ^ e := Nat.mod_lt _ (by positivity)
  have hE : E r z (rSlice i (negIdx e ∘ synG r e) u) k =
      E r z (rSlice i (synG r e) u) (Function.update k i j') := by
    unfold E
    simp only [rSlice_snoc, Function.comp, negIdx, Function.update_self, Function.update_idem]
    rfl
  rw [hE, sliceDFT_synG r hr z hz hz0 i e he u _ (by rw [Function.update_self]; exact hj'lt)]
  congr 1
  apply Finset.sum_congr rfl; intro m _
  rw [Function.update_self, Function.update_idem]
  congr 1
  set W := z ^ (2 * r / 2 ^ e)
  have hW0 : W ≠ 0 := pow_ne_zero _ hz0
  have hWt : W ^ (2 ^ e) = 1 := by
    simp only [W]; rw [← pow_mul, Nat.div_mul_cancel he, pow_mul', hz]; norm_num
  have hsum : ∃ q, j' + k i = 2 ^ e * q := by
    rw [Nat.mod_eq_of_lt hk] at hj'
    by_cases h0 : k i = 0
    · exact ⟨0, by rw [hj', h0]; simp⟩
    · refine ⟨1, ?_⟩
      rw [hj', Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨q, hq⟩ := hsum
  have h1 : W ^ (j' * m) * W ^ (k i * m) = 1 := by
    rw [← pow_add, ← add_mul, hq, mul_assoc, pow_mul, hWt, one_pow]
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_right h1).symm

/-- Iterated `R`-axis transforms, evaluated at a root: the multidimensional DFT-type formula over
the axes in `l`. -/
theorem rComp_DFT (r : ℕ) (z : ℂ) {d : ℕ} (B : Fin d → ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ))
    (t : Fin d → ℕ) (ω : Fin d → ℂ) (hB : ∀ i, SliceDFT r z i (B i) (t i) (ω i)) :
    ∀ l : List (Fin d), l.Nodup → ∀ (u : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ),
      (∀ i ∈ l, k i < t i) →
      E r z (rComp B l u) k = (∏ i ∈ l.toFinset, (1 / t i : ℂ)) *
        ∑ m ∈ Fintype.piFinset (fun i => if i ∈ l then Finset.range (t i) else {k i}),
          (∏ i ∈ l.toFinset, ω i ^ (k i * m i)) * E r z u m
  | [] => by
    intro _ u k _
    simp [rComp, Fintype.piFinset_singleton]
  | i :: l => by
    intro hnd u k hk
    rw [List.nodup_cons] at hnd
    obtain ⟨hil, hnd⟩ := hnd
    have hil' : i ∉ l.toFinset := by rwa [List.mem_toFinset]
    have ih := rComp_DFT r z B t ω hB l hnd (rSlice i (B i) u) k
      (fun x hx => hk x (List.mem_cons_of_mem _ hx))
    show E r z (rComp B l (rSlice i (B i) u)) k = _
    rw [ih]
    have hbox : ∀ m ∈ Fintype.piFinset (fun x => if x ∈ l then Finset.range (t x) else {k x}),
        m i = k i := by
      intro m hm
      have := Fintype.mem_piFinset.1 hm i
      rw [if_neg hil, Finset.mem_singleton] at this; exact this
    have hinner : ∀ m ∈ Fintype.piFinset (fun x => if x ∈ l then Finset.range (t x) else {k x}),
        (∏ x ∈ l.toFinset, ω x ^ (k x * m x)) * E r z (rSlice i (B i) u) m =
        (1 / t i : ℂ) * ∑ n ∈ Finset.range (t i),
          (∏ x ∈ l.toFinset, ω x ^ (k x * m x)) * (ω i ^ (k i * n) * E r z u (Function.update m i n)) := by
      intro m hm
      rw [hB i u m (by rw [hbox m hm]; exact hk i (List.mem_cons_self ..)), hbox m hm, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, List.toFinset_cons,
      Finset.prod_insert hil', mul_comm (1 / (t i : ℂ)) _, mul_assoc]
    have key : ∀ (P S c S' : ℂ), S = S' → P * (S * c) = c * (P * S') := by
      intro P S c S' h; rw [h]; ring
    refine key _ _ _ _ ?_
    rw [Finset.sum_product' (s := Fintype.piFinset (fun x => if x ∈ l then Finset.range (t x) else {k x}))
      (t := Finset.range (t i))
      (f := fun m n => (∏ x ∈ l.toFinset, ω x ^ (k x * m x)) *
        (ω i ^ (k i * n) * E r z u (Function.update m i n))) |>.symm]
    apply Finset.sum_nbij' (fun pn => Function.update pn.1 i pn.2) (fun m' => (Function.update m' i (k i), m' i))
    · intro pn hpn
      rw [Finset.mem_product] at hpn
      rw [Fintype.mem_piFinset]
      intro x
      by_cases hx : x = i
      · subst hx; rw [Function.update_self, if_pos (List.mem_cons_self ..)]; exact hpn.2
      · rw [Function.update_of_ne hx]
        have := Fintype.mem_piFinset.1 hpn.1 x
        by_cases hxl : x ∈ l
        · rw [if_pos hxl] at this; rw [if_pos (List.mem_cons_of_mem _ hxl)]; exact this
        · rw [if_neg hxl] at this
          rw [if_neg (by simp [hx, hxl])]; exact this
    · intro m' hm'
      rw [Fintype.mem_piFinset] at hm'
      rw [Finset.mem_product, Fintype.mem_piFinset]
      refine ⟨fun x => ?_, ?_⟩
      · dsimp only
        by_cases hx : x = i
        · subst hx; rw [Function.update_self, if_neg hil]; exact Finset.mem_singleton_self _
        · rw [Function.update_of_ne hx]
          have := hm' x
          by_cases hxl : x ∈ l
          · rw [if_pos (List.mem_cons_of_mem _ hxl)] at this; rw [if_pos hxl]; exact this
          · rw [if_neg (by simp [hx, hxl])] at this; rw [if_neg hxl]; exact this
      · dsimp only
        have := hm' i; rw [if_pos (List.mem_cons_self ..)] at this; exact this
    · intro pn hpn
      rw [Finset.mem_product] at hpn
      simp only [Function.update_idem, Function.update_self]
      rw [← hbox _ hpn.1, Function.update_eq_self]
    · intro m' _
      simp only [Function.update_idem, Function.update_eq_self]
    · intro pn hpn
      rw [Finset.mem_product] at hpn
      have hprod : ∏ x ∈ l.toFinset, ω x ^ (k x * Function.update pn.1 i pn.2 x) =
          ∏ x ∈ l.toFinset, ω x ^ (k x * pn.1 x) := by
        apply Finset.prod_congr rfl; intro x hx
        rw [Function.update_of_ne (fun h => hil' (by rw [← h]; exact hx))]
      rw [Finset.prod_insert hil', hprod, Function.update_self]; ring

/-! ### The convolution theorem on boxes -/

/-- Orthogonality for a root `W` with `W^{t/2} = -1`, `t = 2^{e+1}`. -/
lemma orth (e : ℕ) (W : ℂ) (hW : W ^ (2 ^ e) = -1) (a : ℤ) :
    ∑ m ∈ Finset.range (2 ^ (e + 1)), W ^ ((m : ℤ) * a) =
      if ((2 ^ (e + 1) : ℕ) : ℤ) ∣ a then ((2 ^ (e + 1) : ℕ) : ℂ) else 0 := by
  set t : ℕ := 2 ^ (e + 1) with ht
  have htpos : 0 < t := by positivity
  have hW0 : W ≠ 0 := by rintro rfl; rw [zero_pow (by positivity)] at hW; norm_num at hW
  have hWt : W ^ t = 1 := by rw [ht, pow_succ, pow_mul, hW]; norm_num
  set j : ℕ := (a % t).toNat with hj
  have hjz : (j : ℤ) = a % t := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hterm : ∀ m : ℕ, W ^ ((m : ℤ) * a) = W ^ (j * m) := by
    intro m
    have ha : a = j + t * (a / t) := by rw [hjz]; exact (Int.emod_add_mul_ediv a t).symm
    rw [ha, show (m : ℤ) * (j + t * (a / t)) = ((j * m : ℕ) : ℤ) + (t : ℤ) * (m * (a / t)) by
        push_cast; ring, zpow_add₀ hW0, zpow_natCast, zpow_mul, zpow_natCast, hWt, one_zpow,
      mul_one]
  simp only [hterm]
  split_ifs with hdvd
  · have : j = 0 := by
      have : a % t = 0 := Int.emod_eq_zero_of_dvd hdvd
      omega
    simp [this, ht]
  · apply Syn.sum_pow_eq_zero e W hW j
    intro hd
    apply hdvd
    have hjlt : j < t := by have := Int.emod_lt_of_pos a (show (0 : ℤ) < t by omega); omega
    obtain ⟨q, hq⟩ := hd
    have : j = 0 := by
      rcases q with _ | q
      · simpa using hq
      · exfalso; rw [← ht] at hq; nlinarith
    rw [this] at hjz
    exact Int.dvd_of_emod_eq_zero hjz.symm

/-- The convolution theorem on a box `∏ᵢ [0, tᵢ)`, for roots `Wᵢ` satisfying orthogonality. -/
theorem box_conv {d : ℕ} (t : Fin d → ℕ) (W : Fin d → ℂ) (hW0 : ∀ i, W i ≠ 0)
    (horth : ∀ i (a : ℤ), ∑ m ∈ Finset.range (t i), W i ^ ((m : ℤ) * a) =
      if (t i : ℤ) ∣ a then (t i : ℂ) else 0)
    (U V : (Fin d → ℕ) → ℂ) (k : Fin d → ℕ) (hk : ∀ i, k i < t i) :
    ∑ m ∈ Fintype.piFinset (fun i => Finset.range (t i)),
      (∏ i, W i ^ ((k i * m i : ℕ) : ℤ)) *
        ((∑ n ∈ Fintype.piFinset (fun i => Finset.range (t i)),
            (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * U n) *
          (∑ n ∈ Fintype.piFinset (fun i => Finset.range (t i)),
            (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * V n)) =
      (∏ i, (t i : ℂ)) * ∑ n ∈ Fintype.piFinset (fun i => Finset.range (t i)),
        U n * V (fun i => (k i + t i - n i) % t i) := by
  classical
  set box := Fintype.piFinset (fun i => Finset.range (t i))
  -- expand everything into a triple sum
  have h1 : ∀ m : Fin d → ℕ, (∏ i, W i ^ ((k i * m i : ℕ) : ℤ)) *
      ((∑ n ∈ box, (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * U n) *
        (∑ n ∈ box, (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * V n)) =
      ∑ n ∈ box, ∑ n' ∈ box, U n * V n' *
        ∏ i, W i ^ ((m i : ℤ) * ((k i : ℤ) - n i - n' i)) := by
    intro m
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _
    have : ∏ i, W i ^ ((m i : ℤ) * ((k i : ℤ) - n i - n' i)) =
        (∏ i, W i ^ ((k i * m i : ℕ) : ℤ)) * (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) *
          (∏ i, W i ^ (-((m i * n' i : ℕ) : ℤ))) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rw [← zpow_add₀ (hW0 i), ← zpow_add₀ (hW0 i)]
      congr 1; push_cast; ring
    rw [this]; ring
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n hn
  rw [Finset.sum_comm]
  have h2 : ∀ n' ∈ box, ∑ m ∈ box, U n * V n' * ∏ i, W i ^ ((m i : ℤ) * ((k i : ℤ) - n i - n' i)) =
      U n * V n' * (if ∀ i, (t i : ℤ) ∣ ((k i : ℤ) - n i - n' i) then ∏ i, (t i : ℂ) else 0) := by
    intro n' _
    rw [← Finset.mul_sum]
    congr 1
    rw [show box = Fintype.piFinset (fun i => Finset.range (t i)) from rfl,
      ← Finset.prod_univ_sum (fun i => Finset.range (t i))
        (fun i mi => W i ^ ((mi : ℤ) * ((k i : ℤ) - n i - n' i)))]
    simp only [horth]
    rw [Fintype.prod_ite_zero (p := fun i => (t i : ℤ) ∣ ((k i : ℤ) - n i - n' i))
      (f := fun i => (t i : ℂ))]
    congr 1
  rw [Finset.sum_congr rfl h2]
  set tgt : Fin d → ℕ := fun i => (k i + t i - n i) % t i
  have hn' : ∀ i, n i < t i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hn i)
  have hiff : ∀ n' ∈ box, (∀ i, (t i : ℤ) ∣ ((k i : ℤ) - n i - n' i)) ↔ n' = tgt := by
    intro n' hn'b
    have hb : ∀ i, n' i < t i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hn'b i)
    constructor
    · intro h; funext i
      have := h i
      simp only [tgt]
      have hti : 0 < t i := by have := hk i; omega
      rw [Int.dvd_iff_emod_eq_zero] at this
      have e1 : ((k i + t i - n i : ℕ) : ℤ) = (k i : ℤ) + t i - n i := by
        rw [Nat.cast_sub (show n i ≤ k i + t i by have := hn' i; omega)]; push_cast; ring
      zify
      rw [e1]
      have hlt : (n' i : ℤ) < t i := by exact_mod_cast hb i
      have h0 : (0 : ℤ) ≤ n' i := by positivity
      rw [show (k i : ℤ) + t i - n i = n' i + ((k i - n i - n' i) + t i) by ring,
        Int.add_emod, show ((k i : ℤ) - n i - n' i + t i) % t i = 0 by
          rw [Int.add_emod_right]; exact this]
      simp [Int.emod_eq_of_lt h0 hlt]
    · rintro rfl i
      simp only [tgt]
      have hti : 0 < t i := by have := hk i; omega
      rw [Int.dvd_iff_emod_eq_zero]
      push_cast [Nat.cast_sub (show n i ≤ k i + t i by have := hn' i; omega)]
      rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod]
      rw [show (k i : ℤ) - n i - (k i + t i - n i) = -1 * t i by ring, Int.mul_emod_left]
  have htgt : tgt ∈ box := by
    rw [Fintype.mem_piFinset]; intro i
    have hti : 0 < t i := by have := hk i; omega
    exact Finset.mem_range.2 (Nat.mod_lt _ hti)
  rw [Finset.sum_congr rfl (fun n' hn'b => by rw [if_congr (hiff n' hn'b) rfl rfl])]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' box tgt, if_pos htgt]
  ring

/-! ### The convolution identity over `R` -/

theorem rTensor_DFT (r : ℕ) (z : ℂ) {d : ℕ} (B : Fin d → ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ))
    (t : Fin d → ℕ) (ω : Fin d → ℂ) (hB : ∀ i, SliceDFT r z i (B i) (t i) (ω i))
    (u : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ) (hk : ∀ i, k i < t i) :
    E r z (rTensor B u) k = (∏ i, (1 / t i : ℂ)) *
      ∑ m ∈ Fintype.piFinset (fun i => Finset.range (t i)), (∏ i, ω i ^ (k i * m i)) * E r z u m := by
  have := rComp_DFT r z B t ω hB (List.finRange d) (List.nodup_finRange d) u k (fun i _ => hk i)
  simpa [rTensor, List.toFinset_finRange, List.mem_finRange] using this

lemma mulPt_eval (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) (hz0 : z ≠ 0) {d : ℕ}
    (u v : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ) :
    E r z (mulPt r u v) k = E r z u k * E r z v k / r := by
  unfold E
  rw [← ev_negaCoeff r hr z hz hz0, ev, ev, Finset.sum_div]
  apply Finset.sum_congr rfl; intro c hc; rw [Finset.mem_range] at hc
  unfold mulPt
  rw [Fin.snoc_last, if_pos hc]
  simp only [snoc_update_last]
  ring

lemma convR_eval (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) (hz0 : z ≠ 0) {d : ℕ}
    (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ) :
    E r z (convR r e u v) k = (1 / (r * 2 ^ (∑ i, e i)) : ℂ) *
      ∑ n ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
        E r z u n * E r z v (fun i => (k i + 2 ^ e i - n i) % 2 ^ e i) := by
  unfold E
  simp only [← ev_negaCoeff r hr z hz hz0]
  unfold ev convR
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro c _
  ring

theorem conv_eval (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : z ^ r = -1) {d : ℕ} (e : Fin d → ℕ)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (k : Fin d → ℕ) (hk : ∀ i, k i < 2 ^ e i) :
    (2 ^ (∑ i, e i) : ℂ) * E r z (synGdInv r e (mulPt r (synGd r e u) (synGd r e v))) k =
      E r z (convR r e u v) k := by
  have hz0 : z ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hz; norm_num at hz
  set W : Fin d → ℂ := fun i => z ^ (2 * r / 2 ^ e i) with hWdef
  have hW0 : ∀ i, W i ≠ 0 := fun i => pow_ne_zero _ hz0
  have hWh : ∀ i, W i ^ (2 ^ (e i - 1)) = -1 := by
    intro i
    simp only [W]
    rw [← pow_mul]
    have : 2 * r / 2 ^ e i * 2 ^ (e i - 1) = r := by
      obtain ⟨q, hq⟩ := he i
      have h2 : 2 ^ e i = 2 * 2 ^ (e i - 1) := by
        rw [← pow_succ']; congr 1; have := he1 i; omega
      rw [hq, Nat.mul_div_cancel_left _ (by positivity)]
      rw [h2] at hq
      have : r = 2 ^ (e i - 1) * q := by linarith
      rw [this]; ring
    rw [this, hz]
  have ht : ∀ i, 2 ^ e i = 2 ^ ((e i - 1) + 1) := fun i => by congr 1; have := he1 i; omega
  have horth : ∀ i (a : ℤ), ∑ m ∈ Finset.range (2 ^ e i), W i ^ ((m : ℤ) * a) =
      if ((2 ^ e i : ℕ) : ℤ) ∣ a then ((2 ^ e i : ℕ) : ℂ) else 0 := by
    intro i a; rw [ht i]; exact orth (e i - 1) (W i) (hWh i) a
  have hF : ∀ i, SliceDFT r z i (synG r (e i)) (2 ^ e i) (W i)⁻¹ :=
    fun i => sliceDFT_synG r hr z hz hz0 i (e i) (he i)
  have hI : ∀ i, SliceDFT r z i (negIdx (e i) ∘ synG r (e i)) (2 ^ e i) (W i) :=
    fun i => sliceDFT_synGinv r hr z hz hz0 i (e i) (he i)
  have hbox : ∀ m ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)), ∀ i, m i < 2 ^ e i :=
    fun m hm i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hm i)
  unfold synGdInv
  rw [rTensor_DFT r z _ _ _ hI _ k hk]
  have hinner : ∀ m ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
      (∏ i, W i ^ (k i * m i)) * E r z (mulPt r (synGd r e u) (synGd r e v)) m =
      (∏ i, (1 / (2 ^ e i : ℕ) : ℂ)) ^ 2 / r * ((∏ i, W i ^ ((k i * m i : ℕ) : ℤ)) *
        ((∑ n ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
            (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * E r z u n) *
          (∑ n ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
            (∏ i, W i ^ (-((m i * n i : ℕ) : ℤ))) * E r z v n))) := by
    intro m hm
    rw [mulPt_eval r hr z hz hz0]
    unfold synGd
    rw [rTensor_DFT r z _ _ _ hF _ m (hbox m hm), rTensor_DFT r z _ _ _ hF _ m (hbox m hm)]
    simp only [zpow_neg, zpow_natCast, inv_pow]
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum,
    box_conv (fun i => 2 ^ e i) W hW0 horth _ _ k hk, convR_eval r hr z hz hz0]
  have hprod : (∏ i, ((2 ^ e i : ℕ) : ℂ)) = 2 ^ (∑ i, e i) := by
    push_cast; rw [Finset.prod_pow_eq_pow_sum]
  have hprod' : (∏ i, (1 / (2 ^ e i : ℕ) : ℂ)) = 1 / 2 ^ (∑ i, e i) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, hprod]
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hprod hprod' ⊢
  rw [hprod', hprod]
  have h2 : (2 : ℂ) ^ (∑ i, e i) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/-- **Convolution over `R` via synthetic transforms** (identity (2.1) as used in Prop. 3.4):
`(T/r) · G*(G u · G v / r) = (1/T) u ∗ v` at every in-range index. -/
theorem synConv_eq (r : ℕ) (hr : 0 < r) {d : ℕ} (e : Fin d → ℕ) (he1 : ∀ i, 1 ≤ e i)
    (he : ∀ i, 2 ^ e i ∣ 2 * r) (u v : (Fin (d + 1) → ℕ) → ℂ) (j : Fin (d + 1) → ℕ)
    (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    (2 ^ (∑ i, e i) : ℂ) * synGdInv r e (mulPt r (synGd r e u) (synGd r e v)) j =
      convR r e u v j := by
  set k : Fin d → ℕ := Fin.init j with hk
  have hk' : ∀ i, k i < 2 ^ e i := fun i => hj i
  rw [← Fin.snoc_init_self j]
  refine ev_inj r hr (fun c => (2 ^ (∑ i, e i) : ℂ) *
      synGdInv r e (mulPt r (synGd r e u) (synGd r e v)) (Fin.snoc k c))
    (fun c => convR r e u v (Fin.snoc k c)) ?_ (j (Fin.last d)) hc
  intro z hz
  have := conv_eval r hr z hz e he1 he u v k hk'
  unfold E at this
  rw [← this]
  unfold ev
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _; ring

end IntMul.HvdH.SynId


open Complex

namespace IntMul.HvdH.CRProp
open IntMul.HvdH IntMul.HvdH.FPPf IntMul.HvdH.CRPf

lemma synG_zero (r : ℕ) : ∀ e, synG r e (fun _ => 0) = fun _ => 0
  | 0 => rfl
  | e + 1 => by
    funext kc
    simp only [synG]
    have h1 : (fun kc' : ℕ × ℕ => ((0 : ℂ) + 0) / 2) = fun _ => 0 := by funext; simp
    have h2 : (fun kc' : ℕ × ℕ => yShift r (-((2 * r / 2 ^ (e + 1) * kc'.1 : ℕ) : ℤ))
        (fun c => ((0 : ℂ) - 0) / 2) kc'.2) = fun _ => 0 := by
      funext kc'; simp [yShift]
    rw [h1, h2, synG_zero r e]; simp

lemma rComp_zero {d : ℕ} (A : Fin d → ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ))
    (hA : ∀ i, A i (fun _ => 0) = fun _ => 0) :
    ∀ l : List (Fin d), rComp A l (fun _ => 0) = fun _ => 0
  | [] => rfl
  | i :: l => by
    show rComp A l (rSlice i (A i) (fun _ => 0)) = _
    have : rSlice i (A i) (fun _ => (0 : ℂ)) = fun _ => 0 := by
      funext j; unfold rSlice; rw [hA i]
    rw [this, rComp_zero A hA l]

lemma bounded_of_lip {ι κ : Type*} (A : (ι → ℂ) → (κ → ℂ)) (hA : SupLip A)
    (h0 : A (fun _ => 0) = fun _ => 0) (u : ι → ℂ) (hu : ∀ x, ‖u x‖ ≤ 1) (k : κ) : ‖A u k‖ ≤ 1 := by
  have := hA u (fun _ => 0) 1 (fun x => by simpa using hu x) k
  rw [h0] at this; simpa using this

lemma synGd_bdd {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u : (Fin (d + 1) → ℕ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (k : Fin (d + 1) → ℕ) : ‖synGd r e u k‖ ≤ 1 :=
  bounded_of_lip _ (synGad_approx 0 r e).2 (rComp_zero _ (fun i => synG_zero r (e i)) _) u hu k

lemma synGdInv_bdd {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u : (Fin (d + 1) → ℕ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (k : Fin (d + 1) → ℕ) : ‖synGdInv r e u k‖ ≤ 1 :=
  bounded_of_lip _ (synGadInv_approx 0 r e).2
    (rComp_zero _ (fun i => by
      funext kc; simp only [Function.comp, negIdx, synG_zero r (e i)]) _) u hu k

lemma convR_norm {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (j : Fin (d + 1) → ℕ) (hc : j (Fin.last d) < r) :
    ‖convR r e u v j‖ ≤ 1 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  unfold convR
  rw [norm_mul]
  have hcard : (Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i))).card = 2 ^ (∑ i, e i) := by
    rw [Fintype.card_piFinset]; simp [Finset.prod_pow_eq_pow_sum]
  have hs : ‖∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
      negaCoeff r (fun c => u (Fin.snoc (fun i => k i) c))
        (fun c => v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c))
        (j (Fin.last d))‖ ≤ 2 ^ (∑ i, e i) * (r * (1 * 1)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun k _ => negaCoeff_bound r _ _ _ hc 1 1 (fun i _ => hu _)
      (fun i _ => hv _) zero_le_one)).trans ?_
    rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring_nf; rfl
  have h2 : (0 : ℝ) < 2 ^ (∑ i, e i) := by positivity
  calc _ ≤ ‖(1 / (r * 2 ^ (∑ i, e i)) : ℂ)‖ * (2 ^ (∑ i, e i) * (r * (1 * 1))) :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = 1 := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_two]
      field_simp

/-- **Proposition 3.4** (convolution over `R`). -/
theorem prop_3_4 {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc p U) (hV : InDisc p V) :
    InDisc p (convRa p r e U V) ∧
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (convRa p r e U V j) - 2 ^ p *
          convR r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤
          2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 3 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hpC : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  set K := ∑ i, e i with hK
  set L : ℝ := ∑ i, (e i : ℝ) with hL
  have hLK : L = K := by rw [hL, hK]; push_cast; rfl
  -- the unit-disc vectors
  have hdisc : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ), InDisc p X → ∀ x, ‖gC (X x) / 2 ^ p‖ ≤ 1 := by
    intro X hX x
    rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact hX x
  have herr : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ) (w : (Fin (d + 1) → ℕ) → ℂ) (δ : ℝ),
      (∀ x, ‖gC (X x) - 2 ^ p * w x‖ ≤ δ) → ∀ x, ‖gC (X x) / 2 ^ p - w x‖ ≤ δ / 2 ^ p := by
    intro X w δ h x
    rw [show gC (X x) / 2 ^ p - w x = (gC (X x) - 2 ^ p * w x) / 2 ^ p by field_simp,
      norm_div, norm_pow, Complex.norm_two]
    exact div_le_div_of_nonneg_right (h x) hp.le
  set u : (Fin (d + 1) → ℕ) → ℂ := fun x => gC (U x) / 2 ^ p
  set v : (Fin (d + 1) → ℕ) → ℂ := fun x => gC (V x) / 2 ^ p
  obtain ⟨hFa, -⟩ := synGad_approx p r e
  obtain ⟨hIa, hIl⟩ := synGadInv_approx p r e
  obtain ⟨hU1, hU2⟩ := hFa U hU
  obtain ⟨hV1, hV2⟩ := hFa V hV
  set U' := synGad r e U
  set V' := synGad r e V
  set u0 := synGd r e u
  set v0 := synGd r e v
  have hu0 : ∀ x, ‖u0 x‖ ≤ 1 := synGd_bdd r e u (hdisc U hU)
  -- step 2: pointwise products
  set Z := mulPtZ p r U' V'
  have hZ : ∀ x, gC (Z x) = rho0C ((2 : ℂ) ^ p * mulPt r (fun y => gC (U' y) / 2 ^ p)
      (fun y => gC (V' y) / 2 ^ p) x) := mulPtZ_gC p r hr hrp U' V' hU1 hV1
  have hmn : ∀ x, ‖(2 : ℂ) ^ p * mulPt r (fun y => gC (U' y) / 2 ^ p) (fun y => gC (V' y) / 2 ^ p) x‖
      ≤ 2 ^ p := by
    intro x
    rw [norm_mul, norm_pow, Complex.norm_two]
    calc _ ≤ (2 : ℝ) ^ p * 1 := mul_le_mul_of_nonneg_left
          (mulPt_norm r _ _ (hdisc U' hU1) (hdisc V' hV1) x) hp.le
      _ = _ := mul_one _
  have hZd : InDisc p Z := fun x => by rw [hZ]; exact (FP.norm_rho0C_le _).trans (hmn x)
  set z0 := mulPt r u0 v0
  have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hZe : ∀ x, ‖gC (Z x) - 2 ^ p * z0 x‖ ≤ 2 * L + Real.sqrt 2 := by
    intro x
    rw [hZ]
    set w := (2 : ℂ) ^ p * mulPt r (fun y => gC (U' y) / 2 ^ p) (fun y => gC (V' y) / 2 ^ p) x
    have e : rho0C w - 2 ^ p * z0 x = (rho0C w - w) +
        2 ^ p * (mulPt r (fun y => gC (U' y) / 2 ^ p) (fun y => gC (V' y) / 2 ^ p) x - z0 x) := by
      simp only [w]; ring
    rw [e]
    have h1 := FP.norm_rho0C_sub_lt w
    have h2 := mulPt_lip r (fun y => gC (U' y) / 2 ^ p) (fun y => gC (V' y) / 2 ^ p) u0 v0
      (L / 2 ^ p) (L / 2 ^ p) hu0 (hdisc V' hV1) (herr U' u0 L hU2) (herr V' v0 L hV2) x
    calc _ ≤ ‖rho0C w - w‖ + ‖(2 : ℂ) ^ p * (mulPt r (fun y => gC (U' y) / 2 ^ p)
          (fun y => gC (V' y) / 2 ^ p) x - z0 x)‖ := norm_add_le _ _
      _ ≤ Real.sqrt 2 + 2 ^ p * (L / 2 ^ p + L / 2 ^ p) := by
          rw [norm_mul, norm_pow, Complex.norm_two]
          exact add_le_add h1.le (mul_le_mul_of_nonneg_left h2 hp.le)
      _ = 2 * L + Real.sqrt 2 := by field_simp; ring
  -- step 3: inverse transform
  obtain ⟨hW1, hW2⟩ := hIa Z hZd
  set Wv := synGadInv r e Z
  set w0 := synGdInv r e z0
  have hWe : ∀ x, ‖gC (Wv x) - 2 ^ p * w0 x‖ ≤ 3 * L + Real.sqrt 2 := by
    intro x
    have hlip := hIl (fun y => gC (Z y) / 2 ^ p) z0 _ (herr Z z0 _ hZe) x
    have e : gC (Wv x) - 2 ^ p * w0 x = (gC (Wv x) - 2 ^ p * synGdInv r e (fun y => gC (Z y) / 2 ^ p) x)
        + 2 ^ p * (synGdInv r e (fun y => gC (Z y) / 2 ^ p) x - w0 x) := by ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ L + 2 ^ p * ((2 * L + Real.sqrt 2) / 2 ^ p) := by
          rw [norm_mul, norm_pow, Complex.norm_two]
          exact add_le_add (hW2 x) (mul_le_mul_of_nonneg_left hlip hp.le)
      _ = 3 * L + Real.sqrt 2 := by field_simp; ring
  -- step 4: scaling
  refine ⟨fun j => (scaleZ_bound p K (Wv j) 0 (by simp)).1, ?_⟩
  intro j hj hc
  have hid := SynId.synConv_eq r (by omega) e he1 he u v j hj hc
  have hcn : ‖(2 : ℂ) ^ K * w0 j‖ ≤ 1 := by
    rw [hid]; exact convR_norm r e u v (hdisc U hU) (hdisc V hV) j hc
  obtain ⟨-, hsc⟩ := scaleZ_bound p K (Wv j) (w0 j) hcn
  show ‖gC (scaleZ p K (Wv j)) - 2 ^ p * convR r e u v j‖ ≤ _
  rw [← hid]
  have h2K : (0 : ℝ) ≤ 2 ^ K := by positivity
  calc _ ≤ 2 * 2 ^ K * ‖gC (Wv j) - 2 ^ p * w0 j‖ + 3 := hsc
    _ ≤ 2 * 2 ^ K * (3 * L + Real.sqrt 2) + 3 := by gcongr; exact hWe j
    _ ≤ 2 ^ K * (6 * K + 3) + 3 := by
        rw [hLK]
        have hs : Real.sqrt 2 ≤ 3 / 2 :=
          (Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 / 2) ^ 2 by norm_num)).trans_eq
            (Real.sqrt_sq (by norm_num))
        nlinarith [mul_le_mul_of_nonneg_left hs h2K]

end IntMul.HvdH.CRProp


open Complex

namespace IntMul.HvdH.CCPf
open IntMul.HvdH IntMul.HvdH.FPPf IntMul.HvdH.CRPf IntMul.HvdH.CRProp

lemma mulZ_gC (p : ℕ) (a b : ℤ × ℤ) : gC (mulZ p a b) = rho0C (gC a * gC b / 2 ^ p) := by
  unfold mulZ
  rw [show ((2 : ℤ) ^ p) = ((2 ^ p : ℕ) : ℤ) by push_cast; rfl]
  apply gC_tdiv_eq _ _ _ (by positivity)
  rw [gC_mul]; push_cast; ring

lemma mulZ_disc (p : ℕ) (a b : ℤ × ℤ) (ha : ‖gC a‖ ≤ 2 ^ p) (hb : ‖gC b‖ ≤ 2 ^ p) :
    ‖gC (mulZ p a b)‖ ≤ 2 ^ p := by
  rw [mulZ_gC]
  refine (FP.norm_rho0C_le _).trans ?_
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [norm_div, norm_mul, norm_pow, Complex.norm_two, div_le_iff₀ hp]
  calc _ ≤ (2 : ℝ) ^ p * 2 ^ p := mul_le_mul ha hb (norm_nonneg _) hp.le

lemma mulZ_err (p : ℕ) (a b : ℤ × ℤ) (x y : ℂ) (ha : ‖gC a‖ ≤ 2 ^ p) (hy : ‖y‖ ≤ 1) :
    ‖gC (mulZ p a b) - 2 ^ p * (x * y)‖ ≤
      ‖gC a - 2 ^ p * x‖ + ‖gC b - 2 ^ p * y‖ + Real.sqrt 2 := by
  rw [mulZ_gC]
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hpC : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  set w := gC a * gC b / 2 ^ p
  have e : rho0C w - 2 ^ p * (x * y) = (rho0C w - w) +
      ((gC a / 2 ^ p) * (gC b - 2 ^ p * y) + y * (gC a - 2 ^ p * x)) := by
    simp only [w]; field_simp; ring
  rw [e]
  have h1 := FP.norm_rho0C_sub_lt w
  have ha' : ‖gC a / 2 ^ p‖ ≤ 1 := by
    rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact ha
  calc _ ≤ ‖rho0C w - w‖ + (‖(gC a / 2 ^ p) * (gC b - 2 ^ p * y)‖ + ‖y * (gC a - 2 ^ p * x)‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ Real.sqrt 2 + (1 * ‖gC b - 2 ^ p * y‖ + 1 * ‖gC a - 2 ^ p * x‖) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ = _ := by ring

lemma twD_bound (p n j : ℕ) (hn : 0 < n) :
    ‖gC (twD p n j)‖ ≤ 2 ^ p ∧
      ‖gC (twD p n j) - 2 ^ p * Complex.exp (2 * Real.pi * Complex.I * j / n)‖ ≤ 5 := by
  have hw : ‖(2 : ℂ) ^ 0 * Complex.exp (2 * Real.pi * Complex.I * j / n)‖ ≤ 1 := by
    rw [pow_zero, one_mul, Complex.norm_exp]
    have : (2 * Real.pi * Complex.I * j / n).re = 0 := by
      simp [Complex.div_re, Complex.mul_re]
    rw [this, Real.exp_zero]
  obtain ⟨h1, h2⟩ := scaleZ_bound p 0 (twiddle p n j) _ hw
  refine ⟨h1, ?_⟩
  have ht := IntMul.HvdH.twiddle_bound p n j hn
  have hg : gC (twiddle p n j) = ((twiddle p n j).1 : ℂ) + ((twiddle p n j).2 : ℂ) * Complex.I := rfl
  rw [pow_zero, one_mul] at h2
  unfold twD
  calc _ ≤ 2 * 2 ^ 0 * ‖gC (twiddle p n j) - 2 ^ p * Complex.exp (2 * Real.pi * Complex.I * j / n)‖ + 3 := h2
    _ ≤ 2 * 1 * 1 + 3 := by rw [hg]; gcongr; norm_num
    _ = 5 := by norm_num

lemma card_box {d : ℕ} (e : Fin d → ℕ) :
    (Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i))).card = 2 ^ (∑ i, e i) := by
  rw [Fintype.card_piFinset]; simp [Finset.prod_pow_eq_pow_sum]

lemma convR_lip {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u v u' v' : (Fin (d + 1) → ℕ) → ℂ) (δ₁ δ₂ : ℝ)
    (hu' : ∀ x, ‖u' x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (h₁ : ∀ x, ‖u x - u' x‖ ≤ δ₁) (h₂ : ∀ x, ‖v x - v' x‖ ≤ δ₂) (j : Fin (d + 1) → ℕ)
    (hc : j (Fin.last d) < r) :
    ‖convR r e u v j - convR r e u' v' j‖ ≤ δ₁ + δ₂ := by
  have hδ₁ : 0 ≤ δ₁ := (norm_nonneg _).trans (h₁ j)
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  unfold convR
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  have hs : ‖∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
      (negaCoeff r (fun c => u (Fin.snoc (fun i => k i) c))
        (fun c => v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c)) (j (Fin.last d)) -
       negaCoeff r (fun c => u' (Fin.snoc (fun i => k i) c))
        (fun c => v' (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c)) (j (Fin.last d)))‖
      ≤ 2 ^ (∑ i, e i) * (r * (δ₁ + δ₂)) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
        ‖negaCoeff r (fun c => u (Fin.snoc (fun i => k i) c))
          (fun c => v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c)) (j (Fin.last d)) -
         negaCoeff r (fun c => u' (Fin.snoc (fun i => k i) c))
          (fun c => v' (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c)) (j (Fin.last d))‖
        ≤ r * (δ₁ + δ₂) := by
      intro k _
      rw [negaCoeff_sub]
      have e1 := negaCoeff_bound r (fun c => u (Fin.snoc (fun i => k i) c) - u' (Fin.snoc (fun i => k i) c))
        (fun c => v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c)) _ hc δ₁ 1
        (fun i _ => h₁ _) (fun i _ => hv _) hδ₁
      have e2 := negaCoeff_bound r (fun c => u' (Fin.snoc (fun i => k i) c))
        (fun c => v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c) -
          v' (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c)) _ hc 1 δ₂
        (fun i _ => hu' _) (fun i _ => h₂ _) zero_le_one
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add e1 e2
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, card_box, nsmul_eq_mul]; push_cast; rfl
  have h2 : (0 : ℝ) < 2 ^ (∑ i, e i) := by positivity
  calc _ ≤ ‖(1 / (r * 2 ^ (∑ i, e i)) : ℂ)‖ * (2 ^ (∑ i, e i) * (r * (δ₁ + δ₂))) :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = δ₁ + δ₂ := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_two]
      field_simp

/-- `ζ = e^{πi/r}` as `e^{2πi/(2r)}`. -/
lemma exp_twist (r c : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) / ((2 * r : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / ((2 * r : ℕ) : ℂ)) ^ c := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

lemma zeta_pow_r (r : ℕ) (hr : 0 < r) :
    Complex.exp (2 * Real.pi * Complex.I / ((2 * r : ℕ) : ℂ)) ^ r = -1 := by
  rw [← Complex.exp_nat_mul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [show (r : ℂ) * (2 * Real.pi * Complex.I / ((2 * r : ℕ) : ℂ)) = Real.pi * Complex.I by
    push_cast; field_simp]
  exact Complex.exp_pi_mul_I

/-- The twist `T` turns negacyclic convolution into cyclic convolution (Prop. 3.5). -/
theorem twist_conv {d : ℕ} (r : ℕ) (hr : 0 < r) (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) (hc : j (Fin.last d) < r) :
    Complex.exp (2 * Real.pi * Complex.I * ((2 * r - j (Fin.last d) : ℕ) : ℂ) / ((2 * r : ℕ) : ℂ)) *
      convR r e (fun x => Complex.exp (2 * Real.pi * Complex.I * (x (Fin.last d) : ℂ) / ((2 * r : ℕ) : ℂ)) * u x)
        (fun x => Complex.exp (2 * Real.pi * Complex.I * (x (Fin.last d) : ℂ) / ((2 * r : ℕ) : ℂ)) * v x) j =
      convC r e u v j := by
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ((2 * r : ℕ) : ℂ)) with hζ
  have hζr : ζ ^ r = -1 := zeta_pow_r r hr
  set c := j (Fin.last d)
  simp only [exp_twist r]
  unfold convR convC
  simp only [Fin.snoc_last]
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro k _
  set a : ℕ → ℂ := fun c' => u (Fin.snoc (fun i => k i) c')
  set b : ℕ → ℂ := fun c' => v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) c')
  show ζ ^ (2 * r - c) * negaCoeff r (fun c' => ζ ^ c' * a c') (fun c' => ζ ^ c' * b c') c =
    ∑ c' ∈ Finset.range r, a c' * b ((c + r - c') % r)
  have hζc : ζ ^ (2 * r - c) * ζ ^ c = 1 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega), pow_mul', hζr]; norm_num
  unfold negaCoeff
  rw [← Finset.sum_range_add_sum_Ico _ (show c + 1 ≤ r by omega)]
  have h1 : ∑ i ∈ Finset.range (c + 1), ζ ^ i * a i * (ζ ^ (c - i) * b (c - i)) =
      ζ ^ c * ∑ i ∈ Finset.range (c + 1), a i * b ((c + r - i) % r) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    rw [show (c + r - i) % r = c - i by
      rw [show c + r - i = (c - i) + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
    rw [show ζ ^ i * a i * (ζ ^ (c - i) * b (c - i)) = (ζ ^ i * ζ ^ (c - i)) * (a i * b (c - i)) by ring,
      ← pow_add, Nat.add_sub_cancel' (by omega)]
  have h2 : ∑ i ∈ Finset.Ico (c + 1) r, ζ ^ i * a i * (ζ ^ (c + r - i) * b (c + r - i)) =
      -(ζ ^ c * ∑ i ∈ Finset.Ico (c + 1) r, a i * b ((c + r - i) % r)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_Ico] at hi
    rw [Nat.mod_eq_of_lt (show c + r - i < r by omega)]
    rw [show ζ ^ i * a i * (ζ ^ (c + r - i) * b (c + r - i)) = (ζ ^ i * ζ ^ (c + r - i)) * (a i * b (c + r - i)) by ring,
      ← pow_add, show i + (c + r - i) = c + r by omega, pow_add, hζr]
    ring
  rw [h1, h2]
  linear_combination (∑ i ∈ Finset.range (c + 1), a i * b ((c + r - i) % r) +
    ∑ i ∈ Finset.Ico (c + 1) r, a i * b ((c + r - i) % r)) * hζc

lemma norm_exp_I (x : ℝ) : ‖Complex.exp (x * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x

lemma norm_tw (n c : ℕ) : ‖Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) / (n : ℂ))‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I * (c : ℂ) / (n : ℂ) = ((2 * Real.pi * c / n : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact norm_exp_I _

/-- **Proposition 3.5** (convolution over `ℂ`). -/
theorem prop_3_5 {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc p U) (hV : InDisc p V) :
    InDisc p (convCa p r e U V) ∧
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (convCa p r e U V j) - 2 ^ p *
          convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤
          2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 23 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hpC : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2r : 0 < 2 * r := by omega
  have hdisc : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ), InDisc p X → ∀ x, ‖gC (X x) / 2 ^ p‖ ≤ 1 := by
    intro X hX x
    rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact hX x
  set u : (Fin (d + 1) → ℕ) → ℂ := fun x => gC (U x) / 2 ^ p
  set v : (Fin (d + 1) → ℕ) → ℂ := fun x => gC (V x) / 2 ^ p
  set τ : ℕ → ℂ := fun c => Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) / ((2 * r : ℕ) : ℂ))
  have hτ : ∀ c, ‖τ c‖ = 1 := fun c => norm_tw _ c
  set Tu : (Fin (d + 1) → ℕ) → ℂ := fun x => τ (x (Fin.last d)) * u x
  set Tv : (Fin (d + 1) → ℕ) → ℂ := fun x => τ (x (Fin.last d)) * v x
  have hTb : ∀ (w : (Fin (d + 1) → ℕ) → ℂ), (∀ x, ‖w x‖ ≤ 1) → ∀ x, ‖τ (x (Fin.last d)) * w x‖ ≤ 1 := by
    intro w hw x; rw [norm_mul, hτ, one_mul]; exact hw x
  -- the twist step
  have htw : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ), InDisc p X →
      InDisc p (twistZ p r X) ∧ ∀ x, ‖gC (twistZ p r X x) - 2 ^ p * (τ (x (Fin.last d)) * (gC (X x) / 2 ^ p))‖
        ≤ 5 + Real.sqrt 2 := by
    intro X hX
    refine ⟨fun x => mulZ_disc p _ _ (twD_bound p (2 * r) _ h2r).1 (hX x), fun x => ?_⟩
    have := mulZ_err p (twD p (2 * r) (x (Fin.last d))) (X x) (τ (x (Fin.last d))) (gC (X x) / 2 ^ p)
      (twD_bound p (2 * r) _ h2r).1 (hdisc X hX x)
    have h0 : ‖gC (X x) - 2 ^ p * (gC (X x) / 2 ^ p)‖ = 0 := by
      rw [mul_div_cancel₀ _ hpC, sub_self, norm_zero]
    rw [h0] at this
    have h5 := (twD_bound p (2 * r) (x (Fin.last d)) h2r).2
    unfold twistZ
    linarith
  obtain ⟨hU1, hU2⟩ := htw U hU
  obtain ⟨hV1, hV2⟩ := htw V hV
  set U' := twistZ p r U
  set V' := twistZ p r V
  obtain ⟨hW1, hW2⟩ := prop_3_4 p r e hr hrp he1 he U' V' hU1 hV1
  set W := convRa p r e U' V'
  have herr : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ) (w : (Fin (d + 1) → ℕ) → ℂ) (δ : ℝ),
      (∀ x, ‖gC (X x) - 2 ^ p * w x‖ ≤ δ) → ∀ x, ‖gC (X x) / 2 ^ p - w x‖ ≤ δ / 2 ^ p := by
    intro X w δ h x
    rw [show gC (X x) / 2 ^ p - w x = (gC (X x) - 2 ^ p * w x) / 2 ^ p by field_simp,
      norm_div, norm_pow, Complex.norm_two]
    exact div_le_div_of_nonneg_right (h x) hp.le
  refine ⟨fun j => mulZ_disc p _ _ (twD_bound p (2 * r) _ h2r).1 (hW1 j), ?_⟩
  intro j hj hc
  have hlip := convR_lip r e (fun x => gC (U' x) / 2 ^ p) (fun x => gC (V' x) / 2 ^ p) Tu Tv
    ((5 + Real.sqrt 2) / 2 ^ p) ((5 + Real.sqrt 2) / 2 ^ p) (hTb u (hdisc U hU)) (hdisc V' hV1)
    (herr U' Tu _ hU2) (herr V' Tv _ hV2) j hc
  have hWe : ‖gC (W j) - 2 ^ p * convR r e Tu Tv j‖ ≤
      2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 3 + 2 * (5 + Real.sqrt 2) := by
    have e1 : gC (W j) - 2 ^ p * convR r e Tu Tv j =
        (gC (W j) - 2 ^ p * convR r e (fun x => gC (U' x) / 2 ^ p) (fun x => gC (V' x) / 2 ^ p) j) +
          2 ^ p * (convR r e (fun x => gC (U' x) / 2 ^ p) (fun x => gC (V' x) / 2 ^ p) j -
            convR r e Tu Tv j) := by ring
    rw [e1]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 3 : ℝ) +
          2 ^ p * ((5 + Real.sqrt 2) / 2 ^ p + (5 + Real.sqrt 2) / 2 ^ p) := by
          rw [norm_mul, norm_pow, Complex.norm_two]
          exact add_le_add (hW2 j hj hc) (mul_le_mul_of_nonneg_left hlip hp.le)
      _ = _ := by field_simp; ring
  have hy : ‖convR r e Tu Tv j‖ ≤ 1 :=
    convR_norm r e Tu Tv (hTb u (hdisc U hU)) (hTb v (hdisc V hV)) j hc
  have hm := mulZ_err p (twD p (2 * r) (2 * r - j (Fin.last d))) (W j) (τ (2 * r - j (Fin.last d)))
    (convR r e Tu Tv j) (twD_bound p (2 * r) _ h2r).1 hy
  have h5 := (twD_bound p (2 * r) (2 * r - j (Fin.last d)) h2r).2
  have hid := twist_conv r (by omega) e u v j hc
  show ‖gC (mulZ p (twD p (2 * r) (2 * r - j (Fin.last d))) (W j)) - 2 ^ p * convC r e u v j‖ ≤ _
  rw [← hid]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 :=
    (Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 / 2) ^ 2 by norm_num)).trans_eq (Real.sqrt_sq (by norm_num))
  calc _ ≤ _ := hm
    _ ≤ 5 + (2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 3 + 2 * (5 + Real.sqrt 2)) + Real.sqrt 2 := by
        gcongr
    _ ≤ _ := by linarith

/-! ### Theorem 3.1 (Bluestein) -/

lemma convC_lip {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u v u' v' : (Fin (d + 1) → ℕ) → ℂ) (δ₁ δ₂ : ℝ)
    (hu' : ∀ x, ‖u' x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (h₁ : ∀ x, ‖u x - u' x‖ ≤ δ₁) (h₂ : ∀ x, ‖v x - v' x‖ ≤ δ₂) (j : Fin (d + 1) → ℕ)
    (hr : 0 < r) :
    ‖convC r e u v j - convC r e u' v' j‖ ≤ δ₁ + δ₂ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  unfold convC
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  have hs : ‖∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
      ((∑ c ∈ Finset.range r, u (Fin.snoc (fun i => k i) c) *
          v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))) -
       (∑ c ∈ Finset.range r, u' (Fin.snoc (fun i => k i) c) *
          v' (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))))‖
      ≤ 2 ^ (∑ i, e i) * (r * (δ₁ + δ₂)) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
        ‖(∑ c ∈ Finset.range r, u (Fin.snoc (fun i => k i) c) *
          v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))) -
         (∑ c ∈ Finset.range r, u' (Fin.snoc (fun i => k i) c) *
          v' (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r)))‖
        ≤ r * (δ₁ + δ₂) := by
      intro k _
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have : ∀ c ∈ Finset.range r, ‖u (Fin.snoc (fun i => k i) c) *
          v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r)) -
          u' (Fin.snoc (fun i => k i) c) *
          v' (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))‖
          ≤ δ₁ + δ₂ := by
        intro c _
        set a := u (Fin.snoc (fun i => k i) c)
        set a' := u' (Fin.snoc (fun i => k i) c)
        set b := v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))
        set b' := v' (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))
        rw [show a * b - a' * b' = (a - a') * b + a' * (b - b') by ring]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        have := h₁ (Fin.snoc (fun i => k i) c)
        have := h₂ (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))
        have := hv (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r))
        have := hu' (Fin.snoc (fun i => k i) c)
        have hδ₁ : 0 ≤ δ₁ := (norm_nonneg _).trans (h₁ (Fin.snoc (fun i => k i) c))
        nlinarith [norm_nonneg (a - a'), norm_nonneg b, norm_nonneg a', norm_nonneg (b - b')]
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, card_box, nsmul_eq_mul]; push_cast; rfl
  have h2 : (0 : ℝ) < 2 ^ (∑ i, e i) := by positivity
  calc _ ≤ ‖(1 / (r * 2 ^ (∑ i, e i)) : ℂ)‖ * (2 ^ (∑ i, e i) * (r * (δ₁ + δ₂))) :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = δ₁ + δ₂ := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_two]
      field_simp

lemma convC_norm {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (j : Fin (d + 1) → ℕ) (hr : 0 < r) :
    ‖convC r e u v j‖ ≤ 1 := by
  have := convC_lip r e u v (fun _ => 0) v 1 0 (fun _ => by simp) hv
    (fun x => by simpa using hu x) (fun x => by simp) j hr
  have h0 : convC r e (fun _ => 0) v j = 0 := by simp [convC]
  rw [h0, sub_zero] at this; linarith

/-- The chirp `χ_t(x) = e^{πi x²/t}`. -/
noncomputable def chi (t : ℕ) (x : ℤ) : ℂ := Complex.exp (Real.pi * Complex.I * (x : ℂ) ^ 2 / t)

lemma chi_shift (t : ℕ) (ht : Even t) (ht0 : 0 < t) (x q : ℤ) : chi t (x + t * q) = chi t x := by
  unfold chi
  obtain ⟨s, hs⟩ := ht
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have e : Real.pi * Complex.I * ((x + t * q : ℤ) : ℂ) ^ 2 / t =
      Real.pi * Complex.I * (x : ℂ) ^ 2 / t + ((x * q + s * q ^ 2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
    rw [show (t : ℂ) = s + s by exact_mod_cast hs] at ht' ⊢
    field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma chi_mod (t : ℕ) (ht : Even t) (ht0 : 0 < t) (j k : ℕ) (hj : j < t) (hk : k < t) :
    chi t (((j + t - k) % t : ℕ) : ℤ) = chi t ((j : ℤ) - k) := by
  by_cases h : k ≤ j
  · rw [show (j + t - k) % t = j - k by
      rw [show j + t - k = (j - k) + t by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
    push_cast [Nat.cast_sub h]; rfl
  · rw [Nat.mod_eq_of_lt (show j + t - k < t by omega)]
    rw [show (((j + t - k : ℕ)) : ℤ) = ((j : ℤ) - k) + t * 1 by push_cast [Nat.cast_sub (show k ≤ j + t by omega)]; ring]
    exact chi_shift t ht ht0 _ 1

lemma conj_chi (t : ℕ) (x : ℤ) :
    (starRingEnd ℂ) (chi t x) = Complex.exp (-(Real.pi * Complex.I * (x : ℂ) ^ 2 / t)) := by
  unfold chi
  rw [← Complex.exp_conj]
  congr 1
  simp [map_div₀, Complex.conj_ofReal]
  ring

/-- Per-axis Bluestein identity `e^{-2πijk/t} = χ̄(j) χ̄(k) χ(j - k)`. -/
lemma axis_id (t : ℕ) (ht : Even t) (ht0 : 0 < t) (j k : ℕ) (hj : j < t) (hk : k < t) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((j * k : ℕ) : ℂ) / t)) =
      (starRingEnd ℂ) (chi t j) * (starRingEnd ℂ) (chi t k) * chi t (((j + t - k) % t : ℕ) : ℤ) := by
  rw [chi_mod t ht ht0 j k hj hk, conj_chi, conj_chi]
  unfold chi
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma chirp_eq (r : ℕ) (hr : 0 < r) {d : ℕ} (e : Fin d → ℕ) (he : ∀ i, 2 ^ e i ∣ r)
    (x : Fin (d + 1) → ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e x : ℂ) / ((2 * r : ℕ) : ℂ)) =
      (∏ i, chi (2 ^ e i) (x i.castSucc)) * chi r (x (Fin.last d)) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdiv : ∀ i, ((r / 2 ^ e i : ℕ) : ℂ) = r / 2 ^ e i := fun i => by
    rw [Nat.cast_div (he i) (by exact_mod_cast (by positivity : (0 : ℕ) < 2 ^ e i).ne')]; push_cast; rfl
  unfold chirpIdx chi
  rw [← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, hdiv, Nat.cast_pow, Int.cast_natCast]
  rw [mul_add, Finset.mul_sum, add_div, Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    have : (2 : ℂ) ^ e i ≠ 0 := pow_ne_zero _ two_ne_zero
    push_cast; field_simp; try ring
  · push_cast; field_simp; try ring

/-- Bluestein's identity in the form used by Theorem 3.1: `F u = ā · M_ℂ(ā · u, a)`. -/
theorem bluestein_eq (r : ℕ) (hr : 0 < r) (hr2 : Even r) {d : ℕ} (e : Fin d → ℕ)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ r) (u : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    dftC r e u j =
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e j : ℂ) / ((2 * r : ℕ) : ℂ))) *
        convC r e (fun k => (starRingEnd ℂ)
            (Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e k : ℂ) / ((2 * r : ℕ) : ℂ))) * u k)
          (fun k => Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e k : ℂ) / ((2 * r : ℕ) : ℂ))) j := by
  have hte : ∀ i, Even (2 ^ e i) := fun i => by
    have := he1 i
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  simp only [chirp_eq r hr e he, Fin.snoc_castSucc, Fin.snoc_last]
  unfold dftC convC
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  conv_rhs => rw [mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro k hk
  have hk' : ∀ i, k i < 2 ^ e i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hk i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c hc'
  rw [Finset.mem_range] at hc'
  have hsplit : Complex.exp (-(2 * Real.pi * Complex.I *
      (∑ i : Fin d, ((j i.castSucc : ℂ) * (k i : ℂ)) / 2 ^ e i + (j (Fin.last d) : ℂ) * (c : ℂ) / r))) =
      (∏ i : Fin d, Complex.exp (-(2 * Real.pi * Complex.I * (((j i.castSucc * k i : ℕ)) : ℂ) /
        ((2 ^ e i : ℕ) : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((j (Fin.last d) * c : ℕ) : ℂ) / (r : ℂ))) := by
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    rw [mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; push_cast; ring
    · push_cast; ring
  rw [hsplit]
  rw [Finset.prod_congr rfl (fun i _ => axis_id (2 ^ e i) (hte i) (by positivity) _ _ (hj i) (hk' i)),
    axis_id r hr2 hr _ _ hc hc']
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, map_mul, map_mul, map_prod, map_prod]
  ring

lemma gC_conjZ (z : ℤ × ℤ) : gC (conjZ z) = (starRingEnd ℂ) (gC z) := by
  simp [gC, conjZ, map_add, map_mul, Complex.conj_I]

lemma conj_err (p : ℕ) (z : ℤ × ℤ) (w : ℂ) :
    ‖gC (conjZ z) - 2 ^ p * (starRingEnd ℂ) w‖ = ‖gC z - 2 ^ p * w‖ := by
  rw [gC_conjZ, show (2 : ℂ) ^ p * (starRingEnd ℂ) w = (starRingEnd ℂ) (2 ^ p * w) by rw [map_mul, map_pow, map_ofNat],
    ← map_sub, Complex.norm_conj]

/-- **Theorem 3.1** (power-of-two complex transforms, fixed point). -/
theorem thm_3_1 {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hr2 : Even r) (hrp : 2 * r < 2 ^ p)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ r)
    (U : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc p U) :
    InDisc p (fftCa p r e U) ∧
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (fftCa p r e U j) - 2 ^ p * dftC r e (fun x => gC (U x) / 2 ^ p) j‖ ≤
          2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 41 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hpC : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2r : 0 < 2 * r := by omega
  have he' : ∀ i, 2 ^ e i ∣ 2 * r := fun i => Dvd.dvd.mul_left (he i) 2
  have hdisc : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ), InDisc p X → ∀ x, ‖gC (X x) / 2 ^ p‖ ≤ 1 := by
    intro X hX x
    rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact hX x
  have herr : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ) (w : (Fin (d + 1) → ℕ) → ℂ) (δ : ℝ),
      (∀ x, ‖gC (X x) - 2 ^ p * w x‖ ≤ δ) → ∀ x, ‖gC (X x) / 2 ^ p - w x‖ ≤ δ / 2 ^ p := by
    intro X w δ h x
    rw [show gC (X x) / 2 ^ p - w x = (gC (X x) - 2 ^ p * w x) / 2 ^ p by field_simp,
      norm_div, norm_pow, Complex.norm_two]
    exact div_le_div_of_nonneg_right (h x) hp.le
  have hs2 : Real.sqrt 2 ≤ 3 / 2 :=
    (Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 / 2) ^ 2 by norm_num)).trans_eq (Real.sqrt_sq (by norm_num))
  set u : (Fin (d + 1) → ℕ) → ℂ := fun x => gC (U x) / 2 ^ p
  set a : (Fin (d + 1) → ℕ) → ℂ := fun x =>
    Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e x : ℂ) / ((2 * r : ℕ) : ℂ))
  have ha1 : ∀ x, ‖a x‖ = 1 := fun x => norm_tw _ _
  set A : (Fin (d + 1) → ℕ) → ℤ × ℤ := fun x => twD p (2 * r) (chirpIdx r e x)
  have hA1 : InDisc p A := fun x => (twD_bound p (2 * r) _ h2r).1
  have hA2 : ∀ x, ‖gC (A x) - 2 ^ p * a x‖ ≤ 5 := fun x => (twD_bound p (2 * r) _ h2r).2
  have hAc : ∀ x, ‖gC (conjZ (A x))‖ ≤ 2 ^ p := fun x => by
    rw [gC_conjZ, Complex.norm_conj]; exact hA1 x
  set B : (Fin (d + 1) → ℕ) → ℤ × ℤ := fun k => mulZ p (conjZ (A k)) (U k)
  have hB1 : InDisc p B := fun x => mulZ_disc p _ _ (hAc x) (hU x)
  set au : (Fin (d + 1) → ℕ) → ℂ := fun k => (starRingEnd ℂ) (a k) * u k
  have hau : ∀ x, ‖au x‖ ≤ 1 := fun x => by
    simp only [au]; rw [norm_mul, Complex.norm_conj, ha1, one_mul]; exact hdisc U hU x
  have hB2 : ∀ x, ‖gC (B x) - 2 ^ p * au x‖ ≤ 5 + Real.sqrt 2 := by
    intro x
    have := mulZ_err p (conjZ (A x)) (U x) ((starRingEnd ℂ) (a x)) (u x) (hAc x) (hdisc U hU x)
    rw [conj_err] at this
    have h0 : ‖gC (U x) - 2 ^ p * u x‖ = 0 := by
      simp only [u]; rw [mul_div_cancel₀ _ hpC, sub_self, norm_zero]
    rw [h0] at this
    linarith [hA2 x]
  obtain ⟨hC1, hC2⟩ := prop_3_5 p r e hr hrp he1 he' B A hB1 hA1
  have hF : ∀ j, fftCa p r e U j = mulZ p (conjZ (A j)) (convCa p r e B A j) := fun j => rfl
  set C := convCa p r e B A
  refine ⟨fun j => by rw [hF]; exact mulZ_disc p _ _ (hAc j) (hC1 j), ?_⟩
  intro j hj hc
  have hlip := convC_lip r e (fun x => gC (B x) / 2 ^ p) (fun x => gC (A x) / 2 ^ p) au a
    ((5 + Real.sqrt 2) / 2 ^ p) (5 / 2 ^ p) hau (hdisc A hA1) (herr B au _ hB2) (herr A a _ hA2) j
    (by omega)
  have hCe : ‖gC (C j) - 2 ^ p * convC r e au a j‖ ≤
      2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 23 + (10 + Real.sqrt 2) := by
    have e1 : gC (C j) - 2 ^ p * convC r e au a j =
        (gC (C j) - 2 ^ p * convC r e (fun x => gC (B x) / 2 ^ p) (fun x => gC (A x) / 2 ^ p) j) +
          2 ^ p * (convC r e (fun x => gC (B x) / 2 ^ p) (fun x => gC (A x) / 2 ^ p) j -
            convC r e au a j) := by ring
    rw [e1]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 23 : ℝ) +
          2 ^ p * ((5 + Real.sqrt 2) / 2 ^ p + 5 / 2 ^ p) := by
          rw [norm_mul, norm_pow, Complex.norm_two]
          exact add_le_add (hC2 j hj hc) (mul_le_mul_of_nonneg_left hlip hp.le)
      _ = _ := by field_simp; ring
  have hy : ‖convC r e au a j‖ ≤ 1 :=
    convC_norm r e au a hau (fun x => (ha1 x).le) j (by omega)
  have hm := mulZ_err p (conjZ (A j)) (C j) ((starRingEnd ℂ) (a j)) (convC r e au a j) (hAc j) hy
  rw [conj_err] at hm
  have hid := bluestein_eq r (by omega) hr2 e he1 he u j hj hc
  rw [hF, hid]
  calc _ ≤ _ := hm
    _ ≤ 5 + (2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 23 + (10 + Real.sqrt 2)) + Real.sqrt 2 := by
        gcongr
        · exact hA2 j
    _ ≤ _ := by linarith

end IntMul.HvdH.CCPf


open Complex

namespace IntMul.HvdH.BFP
open IntMul.HvdH IntMul.HvdH.FPPf IntMul.HvdH.CRPf IntMul.HvdH.CRProp IntMul.HvdH.CCPf

/-- In-range indices of `t₁ × ⋯ × t_d × r`. -/
def InR {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (x : Fin (d + 1) → ℕ) : Prop :=
  (∀ i : Fin d, x i.castSucc < 2 ^ e i) ∧ x (Fin.last d) < r

open Classical in
/-- Zero outside the in-range box. -/
noncomputable def restr {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u : (Fin (d + 1) → ℕ) → ℂ) :
    (Fin (d + 1) → ℕ) → ℂ :=
  fun x => if InR r e x then u x else 0

lemma inR_k {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (k : Fin d → ℕ)
    (hk : k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i))) (c : ℕ) (hc : c < r) :
    InR r e (Fin.snoc (fun i => k i) c) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [Fin.snoc_castSucc]; exact Finset.mem_range.1 (Fintype.mem_piFinset.1 hk i)
  · rw [Fin.snoc_last]; exact hc


lemma convC_restr {d : ℕ} (r : ℕ) (hr : 0 < r) (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) :
    convC r e u v j = convC r e (restr r e u) (restr r e v) j := by
  unfold convC
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro c hc
  have h1 := inR_k r e k hk c (Finset.mem_range.1 hc)
  have h2 : InR r e (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i)
      ((j (Fin.last d) + r - c) % r) : Fin (d + 1) → ℕ) := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [Fin.snoc_castSucc]; exact Nat.mod_lt _ (by positivity)
    · rw [Fin.snoc_last]; exact Nat.mod_lt _ hr
  simp only [restr, if_pos h1, if_pos h2]

lemma convC_lip_R {d : ℕ} (r : ℕ) (hr : 0 < r) (e : Fin d → ℕ) (u v u' v' : (Fin (d + 1) → ℕ) → ℂ)
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hu' : ∀ x, InR r e x → ‖u' x‖ ≤ 1) (hv : ∀ x, InR r e x → ‖v x‖ ≤ 1)
    (h₁ : ∀ x, InR r e x → ‖u x - u' x‖ ≤ δ₁) (h₂ : ∀ x, InR r e x → ‖v x - v' x‖ ≤ δ₂)
    (j : Fin (d + 1) → ℕ) :
    ‖convC r e u v j - convC r e u' v' j‖ ≤ δ₁ + δ₂ := by
  rw [convC_restr r hr e u v, convC_restr r hr e u' v']
  apply convC_lip r e _ _ _ _ δ₁ δ₂ _ _ _ _ j hr
  · intro x; unfold restr; split_ifs with h
    · exact hu' x h
    · simp
  · intro x; unfold restr; split_ifs with h
    · exact hv x h
    · simp
  · intro x; unfold restr; split_ifs with h
    · exact h₁ x h
    · simpa using hδ₁
  · intro x; unfold restr; split_ifs with h
    · exact h₂ x h
    · simpa using hδ₂

lemma convC_norm_R {d : ℕ} (r : ℕ) (hr : 0 < r) (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (hu : ∀ x, InR r e x → ‖u x‖ ≤ 1) (hv : ∀ x, InR r e x → ‖v x‖ ≤ 1) (j : Fin (d + 1) → ℕ) :
    ‖convC r e u v j‖ ≤ 1 := by
  rw [convC_restr r hr e u v]
  apply convC_norm r e _ _ _ _ j hr
  · intro x; unfold restr; split_ifs with h
    · exact hu x h
    · simp
  · intro x; unfold restr; split_ifs with h
    · exact hv x h
    · simp

/-- **Bluestein reduction with an arbitrary fixed-point convolution oracle `M` and chirp table `A`.**
If `M` approximates the normalised cyclic convolution `convC` with error `δ` and `A` approximates
the chirp `e^{2πi η_x/(2r)}` with error `εa` (on in-range indices), then
`conj(A)·M(conj(A)·U, A)` approximates the normalised DFT with error `δ + 3εa + 3`. -/
theorem bluestein_fp {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hr2 : Even r)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ r)
    (M : ((Fin (d + 1) → ℕ) → ℤ × ℤ) → ((Fin (d + 1) → ℕ) → ℤ × ℤ) → (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (δ : ℝ)
    (hM : ∀ U V : (Fin (d + 1) → ℕ) → ℤ × ℤ,
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (U x)‖ ≤ 2 ^ p) →
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (V x)‖ ≤ 2 ^ p) →
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (M U V j)‖ ≤ 2 ^ p ∧
        ‖gC (M U V j) - 2 ^ p *
          convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤ δ)
    (A : (Fin (d + 1) → ℕ) → ℤ × ℤ) (εa : ℝ)
    (hA : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (A x)‖ ≤ 2 ^ p ∧
      ‖gC (A x) - 2 ^ p *
        Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e x : ℂ) / ((2 * r : ℕ) : ℂ))‖ ≤ εa)
    (U : (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (hU : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (U x)‖ ≤ 2 ^ p) :
    ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
      ‖gC (mulZ p (conjZ (A j)) (M (fun k => mulZ p (conjZ (A k)) (U k)) A j))‖ ≤ 2 ^ p ∧
      ‖gC (mulZ p (conjZ (A j)) (M (fun k => mulZ p (conjZ (A k)) (U k)) A j)) -
        2 ^ p * dftC r e (fun x => gC (U x) / 2 ^ p) j‖ ≤ δ + 3 * εa + 3 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hpC : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ two_ne_zero
  have hr0 : 0 < r := by omega
  have hdisc : ∀ (X : (Fin (d + 1) → ℕ) → ℤ × ℤ) x, ‖gC (X x)‖ ≤ 2 ^ p → ‖gC (X x) / 2 ^ p‖ ≤ 1 := by
    intro X x hX
    rw [norm_div, norm_pow, Complex.norm_two, div_le_one hp]; exact hX
  have herr : ∀ (z : ℤ × ℤ) (w : ℂ) (δ' : ℝ), ‖gC z - 2 ^ p * w‖ ≤ δ' →
      ‖gC z / 2 ^ p - w‖ ≤ δ' / 2 ^ p := by
    intro z w δ' h
    rw [show gC z / 2 ^ p - w = (gC z - 2 ^ p * w) / 2 ^ p by field_simp,
      norm_div, norm_pow, Complex.norm_two]
    exact div_le_div_of_nonneg_right h hp.le
  have hs2 : Real.sqrt 2 ≤ 3 / 2 :=
    (Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 / 2) ^ 2 by norm_num)).trans_eq (Real.sqrt_sq (by norm_num))
  intro j hj hc
  have hεa : 0 ≤ εa := (norm_nonneg _).trans (hA j hj hc).2
  set u : (Fin (d + 1) → ℕ) → ℂ := fun x => gC (U x) / 2 ^ p
  set a : (Fin (d + 1) → ℕ) → ℂ := fun x =>
    Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e x : ℂ) / ((2 * r : ℕ) : ℂ))
  have ha1 : ∀ x, ‖a x‖ = 1 := fun x => norm_tw _ _
  have hAc : ∀ x, InR r e x → ‖gC (conjZ (A x))‖ ≤ 2 ^ p := fun x hx => by
    rw [gC_conjZ, Complex.norm_conj]; exact (hA x hx.1 hx.2).1
  set B : (Fin (d + 1) → ℕ) → ℤ × ℤ := fun k => mulZ p (conjZ (A k)) (U k)
  have hB1 : ∀ x, InR r e x → ‖gC (B x)‖ ≤ 2 ^ p := fun x hx =>
    mulZ_disc p _ _ (hAc x hx) (hU x hx.1 hx.2)
  set au : (Fin (d + 1) → ℕ) → ℂ := fun k => (starRingEnd ℂ) (a k) * u k
  have hau : ∀ x, InR r e x → ‖au x‖ ≤ 1 := fun x hx => by
    simp only [au]; rw [norm_mul, Complex.norm_conj, ha1, one_mul]
    exact hdisc U x (hU x hx.1 hx.2)
  have hB2 : ∀ x, InR r e x → ‖gC (B x) - 2 ^ p * au x‖ ≤ εa + Real.sqrt 2 := by
    intro x hx
    have := mulZ_err p (conjZ (A x)) (U x) ((starRingEnd ℂ) (a x)) (u x) (hAc x hx)
      (hdisc U x (hU x hx.1 hx.2))
    rw [conj_err] at this
    have h0 : ‖gC (U x) - 2 ^ p * u x‖ = 0 := by
      simp only [u]; rw [mul_div_cancel₀ _ hpC, sub_self, norm_zero]
    rw [h0] at this
    linarith [(hA x hx.1 hx.2).2]
  obtain ⟨hC1, hC2⟩ := hM B A (fun x h1 h2 => hB1 x ⟨h1, h2⟩) (fun x h1 h2 => (hA x h1 h2).1) j hj hc
  set C := M B A
  refine ⟨mulZ_disc p _ _ (hAc j ⟨hj, hc⟩) hC1, ?_⟩
  have hlip := convC_lip_R r hr0 e (fun x => gC (B x) / 2 ^ p) (fun x => gC (A x) / 2 ^ p) au a
    ((εa + Real.sqrt 2) / 2 ^ p) (εa / 2 ^ p) (by positivity) (by positivity) hau
    (fun x hx => hdisc A x (hA x hx.1 hx.2).1) (fun x hx => herr _ _ _ (hB2 x hx))
    (fun x hx => herr _ _ _ (hA x hx.1 hx.2).2) j
  have hCe : ‖gC (C j) - 2 ^ p * convC r e au a j‖ ≤ δ + (2 * εa + Real.sqrt 2) := by
    have e1 : gC (C j) - 2 ^ p * convC r e au a j =
        (gC (C j) - 2 ^ p * convC r e (fun x => gC (B x) / 2 ^ p) (fun x => gC (A x) / 2 ^ p) j) +
          2 ^ p * (convC r e (fun x => gC (B x) / 2 ^ p) (fun x => gC (A x) / 2 ^ p) j -
            convC r e au a j) := by ring
    rw [e1]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ δ + 2 ^ p * ((εa + Real.sqrt 2) / 2 ^ p + εa / 2 ^ p) := by
          rw [norm_mul, norm_pow, Complex.norm_two]
          exact add_le_add hC2 (mul_le_mul_of_nonneg_left hlip hp.le)
      _ = _ := by field_simp; ring
  have hy : ‖convC r e au a j‖ ≤ 1 :=
    convC_norm_R r hr0 e au a hau (fun x _ => (ha1 x).le) j
  have hm := mulZ_err p (conjZ (A j)) (C j) ((starRingEnd ℂ) (a j)) (convC r e au a j) (hAc j ⟨hj, hc⟩) hy
  rw [conj_err] at hm
  have hid := bluestein_eq r hr0 hr2 e he1 he u j hj hc
  rw [hid]
  calc _ ≤ _ := hm
    _ ≤ εa + (δ + (2 * εa + Real.sqrt 2)) + Real.sqrt 2 := by
        gcongr
        exact (hA j hj hc).2
    _ ≤ _ := by linarith

end IntMul.HvdH.BFP

open IntMul.HvdH

theorem solution (p : ℕ) (a b : ℤ × ℤ) (ha : ‖gC a‖ ≤ 2 ^ p) (hb : ‖gC b‖ ≤ 2 ^ p) :
    ‖gC (mulZ p a b)‖ ≤ 2 ^ p :=
  IntMul.HvdH.CCPf.mulZ_disc p a b ha hb
