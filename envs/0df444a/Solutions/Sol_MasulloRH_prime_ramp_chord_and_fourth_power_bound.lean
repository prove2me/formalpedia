-- Prove2me | solution 1 for MasulloRH.prime_ramp_chord_and_fourth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:43:21.444184+00:00
-- url     : https://prove2.me/submissions/9ee070d0-d418-4949-9246-6882820b7013

import Mathlib
open Finset ArithmeticFunction

private noncomputable def term (x : ℝ) (n : ℕ) := vonMangoldt n * max (x/(n:ℝ)-1) 0
private noncomputable def raw (x : ℝ) := ∑ n ∈ range (⌊x⌋₊+1), term x n
private noncomputable def rampVal (x : ℝ) := raw x - x*(Real.log x-1-Real.eulerMascheroniConstant)

private theorem common_cutoff {a b : ℝ} (h : a ≤ b) : raw a = ∑ n ∈ range (⌊b⌋₊+1),term a n := by
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.floor_mono h)))
  intro n _ hn
  have hna : ⌊a⌋₊ < n := by have hh := mt Finset.mem_range.mpr hn; omega
  have hlt : a < (n:ℝ) := (Nat.lt_floor_add_one a).trans_le (by exact_mod_cast Nat.succ_le_of_lt hna)
  have hn0 : (0:ℝ)<n := by exact_mod_cast Nat.zero_lt_of_lt hna
  have hneg : a/(n:ℝ)-1 ≤ 0 := sub_nonpos.mpr ((div_le_one hn0).mpr hlt.le)
  simp [term,max_eq_right hneg]

private theorem raw_chord {a b t : ℝ} (hab : a ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    raw ((1-t)*a+t*b) ≤ (1-t)*raw a+t*raw b := by
  let y := (1-t)*a+t*b
  have hyb : y≤b := by dsimp [y];nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hab)]
  change raw y ≤ _
  rw [common_cutoff hyb,common_cutoff hab,raw,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply sum_le_sum
  intro n _
  let A := max (a/(n:ℝ)-1) 0
  let B := max (b/(n:ℝ)-1) 0
  have hA : a/(n:ℝ)-1 ≤ A := le_max_left ..
  have hB : b/(n:ℝ)-1 ≤ B := le_max_left ..
  have hA0 : 0 ≤ A := le_max_right ..
  have hB0 : 0 ≤ B := le_max_right ..
  have ht' : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hf : max (y/(n:ℝ)-1) 0 ≤ (1-t)*A+t*B := by
    apply max_le
    · calc y/n-1 = (1-t)*(a/n-1)+t*(b/n-1) := by dsimp [y]; ring
           _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hA ht') (mul_le_mul_of_nonneg_left hB ht0)
    · exact add_nonneg (mul_nonneg ht' hA0) (mul_nonneg ht0 hB0)
  apply (mul_le_mul_of_nonneg_left hf vonMangoldt_nonneg).trans_eq
  change vonMangoldt n*((1-t)*A+t*B)=(1-t)*(vonMangoldt n*A)+t*(vonMangoldt n*B)
  ring

private theorem log_chord {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    let y := (1-t)*a+t*b
    (1-t)*a*Real.log a+t*b*Real.log b-y*Real.log y ≤ t*(1-t)*(b-a)^2/y := by
  let y := (1-t)*a+t*b
  have hb := ha.trans_le hab
  have ht : 0 ≤ 1-t := sub_nonneg.mpr h1
  have hya : a ≤ y := by dsimp [y]; nlinarith [mul_nonneg h0 (sub_nonneg.mpr hab)]
  have hy := ha.trans_le hya
  have hlog (v : ℝ) (hv : 0 < v) : Real.log v - Real.log y ≤ v/y-1 := by
    rw [←Real.log_div hv.ne' hy.ne'];exact Real.log_le_sub_one_of_pos (div_pos hv hy)
  change (1-t)*a*Real.log a+t*b*Real.log b-y*Real.log y ≤ _
  calc _ = ((1-t)*a)*(Real.log a-Real.log y)+(t*b)*(Real.log b-Real.log y) := by dsimp [y];ring
       _ ≤ ((1-t)*a)*(a/y-1)+(t*b)*(b/y-1) := add_le_add
          (mul_le_mul_of_nonneg_left (hlog a ha) (mul_nonneg ht ha.le))
          (mul_le_mul_of_nonneg_left (hlog b hb) (mul_nonneg h0 hb.le))
       _ = t*(1-t)*(b-a)^2/y := by field_simp [hy.ne'];dsimp [y];ring

private theorem chord {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let y := (1-t)*a+t*b
    rampVal y ≤ (1-t)*rampVal a+t*rampVal b+t*(1-t)*(b-a)^2/y := by
  have h := raw_chord hab ht0 ht1
  have hlog := log_chord ha hab ht0 ht1
  dsimp only at hlog ⊢
  unfold rampVal
  linarith only [h,hlog]

private theorem quartic_sampling (k : ℕ) (hk : 1 ≤ k) (θ C : ℝ) (hθ : 1/2 ≤ θ) (h1 : θ ≤ 1) (hC : 0 ≤ C)
    (ha : rampVal ((k:ℝ)^4) ≤ C*((k:ℝ)^4)^θ)
    (hb : rampVal (((k:ℝ)+1)^4) ≤ C*(((k:ℝ)+1)^4)^θ) (y : ℝ)
    (hya : (k:ℝ)^4 ≤ y) (hyb : y ≤ ((k:ℝ)+1)^4) :
    rampVal y ≤ (C+225/4)*y^θ := by
  let a : ℝ := (k:ℝ)^4
  let b : ℝ := ((k:ℝ)+1)^4
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by linarith
  have ha0 : 0 < a := by dsimp [a];positivity
  have hab : a < b := pow_lt_pow_left₀ (by linarith) hk0.le (by norm_num)
  have hy := ha0.trans_le hya
  let t := (y-a)/(b-a)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hya) (sub_nonneg.mpr hab.le)
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith only [hyb])
  have he : (1-t)*a+t*b=y := by dsimp [t];field_simp [sub_ne_zero.mpr hab.ne'];ring
  have h := chord ha0 hab.le ht0 ht1
  dsimp only at h
  rw [he] at h
  have hconc := (Real.concaveOn_rpow (by linarith : 0≤θ) h1).2
    (show a∈Set.Ici (0:ℝ) from ha0.le) (show b∈Set.Ici (0:ℝ) from ha0.le.trans hab.le)
    (sub_nonneg.mpr ht1) ht0 (show (1-t)+t=1 by ring)
  simp only [smul_eq_mul,he] at hconc
  have hend : (1-t)*rampVal a + t*rampVal b ≤ C*y^θ := by
    calc _ ≤ (1-t)*(C*a^θ)+t*(C*b^θ) := add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hb ht0)
         _ = C*((1-t)*a^θ+t*b^θ) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hconc hC
  have hk2 : (k:ℝ) ≤ (k:ℝ)^2 := by nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hk')]
  have hk3 : (k:ℝ)^2 ≤ (k:ℝ)^3 := by nlinarith [mul_nonneg (sq_nonneg (k:ℝ)) (sub_nonneg.mpr hk')]
  have hgap : b-a ≤ 15*(k:ℝ)^3 := by dsimp [a,b]; linarith only [hk',hk2,hk3]
  have htq : t*(1-t) ≤ 1/4 := by nlinarith [sq_nonneg (t-1/2)]
  have hfrac : (b-a)^2/y ≤ 225*(k:ℝ)^2 := by
    apply (div_le_iff₀ hy).2
    have hs := (sq_le_sq₀ (sub_nonneg.mpr hab.le) (by positivity)).mpr hgap
    have hm := mul_le_mul_of_nonneg_left hya (show 0 ≤ 225*(k:ℝ)^2 by positivity)
    dsimp [a,b] at hs hm ⊢
    nlinarith only [hs,hm]
  have h1y : 1 ≤ y := (one_le_pow₀ hk').trans hya
  have hky : (k:ℝ)^2 ≤ y^θ := by
    calc _ ≤ Real.sqrt y := (Real.le_sqrt (sq_nonneg _) hy.le).2 (by nlinarith only [hya])
         _ = y^(1/2:ℝ) := Real.sqrt_eq_rpow _
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1y hθ
  have hrem : t*(1-t)*(b-a)^2/y ≤ (225/4)*y^θ := by
    calc _ = (t*(1-t))*((b-a)^2/y) := by ring
         _ ≤ (1/4)*(225*(k:ℝ)^2) := mul_le_mul htq hfrac (by positivity) (by norm_num)
         _ = (225/4)*(k:ℝ)^2 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hky (by norm_num)
  exact h.trans ((add_le_add hend hrem).trans_eq (by ring))

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    (∀ a b t : ℝ, 0<a → a≤b → 0≤t → t≤1 → let y := (1-t)*a+t*b
      G y ≤ (1-t)*G a+t*G b+t*(1-t)*(b-a)^2/y) ∧
    (∀ k : ℕ, 1≤k → ∀ θ C : ℝ, 1/2≤θ → θ≤1 → 0≤C →
      G ((k:ℝ)^4) ≤ C*((k:ℝ)^4)^θ → G (((k:ℝ)+1)^4) ≤ C*(((k:ℝ)+1)^4)^θ →
      ∀ y : ℝ, (k:ℝ)^4 ≤ y → y ≤ ((k:ℝ)+1)^4 → G y ≤ (C+225/4)*y^θ) := by
  exact ⟨fun a b t ha hab ht0 ht1 => chord ha hab ht0 ht1, quartic_sampling⟩
