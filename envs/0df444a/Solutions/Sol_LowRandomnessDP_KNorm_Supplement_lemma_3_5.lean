-- Prove2me | solution 1 for LowRandomnessDP.KNorm.Supplement.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:29:39.249522+00:00
-- url     : https://prove2.me/submissions/ad762b18-265f-4524-a80c-5ec86b801ae2

import Mathlib
import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

set_option autoImplicit false

open Classical
open LowRandomnessDP.KNorm LowRandomnessDP.KNorm.Supplement

theorem LRDP34_step (w t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Int.fract (w + t) - Int.fract w = t - (if 1 - t ≤ Int.fract w then 1 else 0) := by
  have hf0 := Int.fract_nonneg w
  have hf1 := Int.fract_lt_one w
  have e : w + t = (Int.fract w + t) + ((⌊w⌋ : ℤ) : ℝ) := by
    linarith [Int.floor_add_fract w]
  rw [e, Int.fract_add_intCast]
  split_ifs with h
  · have : Int.fract (Int.fract w + t) = Int.fract w + t - 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, 1, by push_cast; ring⟩
    rw [this]; ring
  · push Not at h
    have : Int.fract (Int.fract w + t) = Int.fract w + t :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [this]; ring

theorem LRDP34_main (d : ℕ) (hd : 0 < d) (x : Vec d) (a b m : Fin d)
    (hcong : Int.ModEq (d : ℤ) (b.val : ℤ) ((a.val : ℤ) - (m.val : ℤ))) :
    phi x b - phi x a = (m.val : ℝ) -
      ((Finset.univ.filter (fun i : Fin d =>
        1 - (m.val : ℝ) / d ≤ Int.fract (x i - (a.val : ℝ) / d))).card : ℝ) := by
  obtain ⟨k, hk⟩ := hcong.dvd
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hkR : ((a.val : ℝ) - m.val) - b.val = d * k := by exact_mod_cast hk
  have ht0 : (0:ℝ) ≤ (m.val : ℝ) / d := by positivity
  have ht1 : (m.val : ℝ) / d < 1 := by
    rw [div_lt_one hdR]; exact_mod_cast m.2
  have hshift : ∀ i, x i - (b.val : ℝ) / d = (x i - (a.val : ℝ) / d + (m.val : ℝ) / d) + (k : ℝ) := by
    intro i
    have : (b.val : ℝ) = a.val - m.val - d * k := by linarith
    rw [this]; field_simp; ring
  unfold phi
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Int.fract (x i - (b.val : ℝ) / d) - Int.fract (x i - (a.val : ℝ) / d)
        = (m.val : ℝ) / d - (if 1 - (m.val : ℝ) / d ≤ Int.fract (x i - (a.val : ℝ) / d) then 1 else 0) := by
    intro i _
    rw [hshift i, Int.fract_add_intCast]
    exact LRDP34_step _ _ ht0 ht1
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_boole]
  field_simp

theorem solution (d : ℕ) (hd : 0 < d) (x : Vec d)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ((Finset.univ.filter (fun i : Fin d =>
      1 - θ ≤ Int.fract (x i - ((A hd x).val : ℝ) / d))).card : ℝ) ≤
      (d : ℝ) * θ + 1 := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  set a := A hd x with ha
  set M := ⌈θ * d⌉₊ with hM
  have hMlt : (M : ℝ) < θ * d + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMge : θ * d ≤ M := Nat.le_ceil _
  by_cases hMd : d ≤ M
  · -- then θ d > d - 1
    have h1 : ((d - 1 : ℕ) : ℝ) < θ * d := by
      rw [← Nat.lt_ceil]; omega
    have h2 : ((Finset.univ.filter (fun i : Fin d =>
        1 - θ ≤ Int.fract (x i - (a.val : ℝ) / d))).card : ℝ) ≤ d := by
      have := Finset.card_filter_le (Finset.univ : Finset (Fin d)) (fun i : Fin d =>
        1 - θ ≤ Int.fract (x i - (a.val : ℝ) / d))
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    have h3 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [h3] at h1
    linarith
  · push Not at hMd
    set m : Fin d := ⟨M, hMd⟩ with hm
    set b : Fin d := ⟨(a.val + (d - M)) % d, Nat.mod_lt _ hd⟩ with hb
    have hcong : Int.ModEq (d : ℤ) (b.val : ℤ) ((a.val : ℤ) - (m.val : ℤ)) := by
      unfold Int.ModEq
      simp only [hb, hm]
      push_cast [Nat.cast_sub (le_of_lt hMd)]
      rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
      rw [show (a.val : ℤ) + ((d : ℤ) - M) = ((a.val : ℤ) - M) + d by ring, Int.add_emod_right]
    have key := LRDP34_main d hd x a b m hcong
    have hmin : phi x a ≤ phi x b := A_minimizes hd x b
    have hsub : Finset.univ.filter (fun i : Fin d =>
        1 - θ ≤ Int.fract (x i - (a.val : ℝ) / d)) ⊆
        Finset.univ.filter (fun i : Fin d =>
        1 - (m.val : ℝ) / d ≤ Int.fract (x i - (a.val : ℝ) / d)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have : θ ≤ (m.val : ℝ) / d := by
        rw [le_div_iff₀ hdR]; simp only [hm]; linarith
      linarith
    have hc := Finset.card_le_card hsub
    have hc' : ((Finset.univ.filter (fun i : Fin d =>
        1 - θ ≤ Int.fract (x i - (a.val : ℝ) / d))).card : ℝ) ≤
        ((Finset.univ.filter (fun i : Fin d =>
        1 - (m.val : ℝ) / d ≤ Int.fract (x i - (a.val : ℝ) / d))).card : ℝ) := by
      exact_mod_cast hc
    have hmv : (m.val : ℝ) = M := rfl
    linarith
