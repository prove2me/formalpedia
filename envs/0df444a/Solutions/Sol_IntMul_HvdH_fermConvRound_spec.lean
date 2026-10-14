-- Prove2me | solution 1 for IntMul.HvdH.fermConvRound_spec
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:00:11.826764+00:00
-- url     : https://prove2.me/submissions/d5d2b287-ef4d-4122-8169-6c21dc8972f5

import Theorems.Thm_IntMul_HvdH_fermConv_eq
import Theorems.Thm_IntMul_HvdH_convC_round

open Finset Complex

namespace IntMul.HvdH.FOr
open IntMul.HvdH

lemma part_bound (p : ℕ) (z : ℤ × ℤ) (h : ‖gC z‖ ≤ 2 ^ p) :
    |z.1| ≤ (2 : ℤ) ^ p ∧ |z.2| ≤ (2 : ℤ) ^ p := by
  have h1 : |(gC z).re| ≤ ‖gC z‖ := Complex.abs_re_le_norm _
  have h2 : |(gC z).im| ≤ ‖gC z‖ := Complex.abs_im_le_norm _
  simp only [gC] at h1 h2 h
  simp at h1 h2
  constructor
  · have : ((|z.1| : ℤ) : ℝ) ≤ ((2 ^ p : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((|z.2| : ℤ) : ℝ) ≤ ((2 ^ p : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- The Gaussian combination of four Fermat-ring convolutions is the exact complex cyclic
convolution. -/
theorem fermConvZ_eq {d : ℕ} (p P r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (hU : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (U x)‖ ≤ 2 ^ p)
    (hV : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (V x)‖ ≤ 2 ^ p)
    (hPM : 2 * (2 ^ (∑ i, e i)) ^ 2 * r * ((2 : ℤ) ^ p) ^ 2 < (2 : ℤ) ^ P)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    gC (fermConvZ P r e U V j) = ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
      ∑ c ∈ Finset.range r, gC (U (Fin.snoc (fun i => k i) c)) *
        gC (V (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i)
          ((j (Fin.last d) + r - c) % r))) := by
  have h0 : (0 : ℤ) ≤ 2 ^ p := by positivity
  have hU1 := fun x h1 h2 => (part_bound p (U x) (hU x h1 h2)).1
  have hU2 := fun x h1 h2 => (part_bound p (U x) (hU x h1 h2)).2
  have hV1 := fun x h1 h2 => (part_bound p (V x) (hV x h1 h2)).1
  have hV2 := fun x h1 h2 => (part_bound p (V x) (hV x h1 h2)).2
  simp only [fermConvZ, gC]
  rw [IntMul.HvdH.fermConv_eq P r e hr hP he1 he _ _ _ h0 hU1 hV1 hPM j hj hc,
    IntMul.HvdH.fermConv_eq P r e hr hP he1 he _ _ _ h0 hU2 hV2 hPM j hj hc,
    IntMul.HvdH.fermConv_eq P r e hr hP he1 he _ _ _ h0 hU1 hV2 hPM j hj hc,
    IntMul.HvdH.fermConv_eq P r e hr hP he1 he _ _ _ h0 hU2 hV1 hPM j hj hc]
  push_cast
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun c _ => ?_))
  ring_nf
  rw [Complex.I_sq]; ring

/-- **The Fermat-ring convolution oracle meets `bluestein_fp`'s hypothesis with `δ = √2`.** -/
theorem fermConvRound_spec {d : ℕ} (p P r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (hPM : 2 * (2 ^ (∑ i, e i)) ^ 2 * r * ((2 : ℤ) ^ p) ^ 2 < (2 : ℤ) ^ P) :
    ∀ U V : (Fin (d + 1) → ℕ) → ℤ × ℤ,
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (U x)‖ ≤ 2 ^ p) →
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (V x)‖ ≤ 2 ^ p) →
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (fermConvRound p P r e U V j)‖ ≤ 2 ^ p ∧
        ‖gC (fermConvRound p P r e U V j) - 2 ^ p *
          convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤ Real.sqrt 2 := by
  intro U V hU hV j hj hc
  exact IntMul.HvdH.convC_round p r e (by omega) U V (fun j => fermConvZ P r e U V j) hU hV j
    (fermConvZ_eq p P r e hr hP he1 he U V hU hV hPM j hj hc)

end IntMul.HvdH.FOr

open IntMul.HvdH

theorem solution {d : ℕ} (p P r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (hPM : 2 * (2 ^ (∑ i, e i)) ^ 2 * r * ((2 : ℤ) ^ p) ^ 2 < (2 : ℤ) ^ P) :
    ∀ U V : (Fin (d + 1) → ℕ) → ℤ × ℤ,
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (U x)‖ ≤ 2 ^ p) →
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (V x)‖ ≤ 2 ^ p) →
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (fermConvRound p P r e U V j)‖ ≤ 2 ^ p ∧
        ‖gC (fermConvRound p P r e U V j) - 2 ^ p *
          convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤ Real.sqrt 2 := IntMul.HvdH.FOr.fermConvRound_spec p P r e hr hP he1 he hPM
