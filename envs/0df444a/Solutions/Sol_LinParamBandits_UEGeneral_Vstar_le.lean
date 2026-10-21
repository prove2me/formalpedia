-- Prove2me | solution 1 for LinParamBandits.UEGeneral.Vstar_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:53:29.605984+00:00
-- url     : https://prove2.me/submissions/652b9540-4097-4ce5-a1b8-6ae093f56854

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Vstar

set_option autoImplicit false
open LinParamBandits.UEGeneral

namespace LPUhelp

theorem sub_le_log {c0 y : ℝ} (hc0 : 1 ≤ c0) (hy0 : 0 ≤ y) (hy : y ≤ c0) :
    y ≤ 2 * c0 * Real.log (1 + y) := by
  have h1 : 1 - (1 + y)⁻¹ ≤ Real.log (1 + y) := Real.one_sub_inv_le_log_of_pos (by linarith)
  have h2 : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
  rw [h2] at h1
  have h3 : y ≤ 2 * c0 * (y / (1 + y)) := by
    rw [mul_div_assoc', le_div_iff₀ (by linarith)]
    nlinarith
  calc y ≤ 2 * c0 * (y / (1 + y)) := h3
    _ ≤ 2 * c0 * Real.log (1 + y) := by
      apply mul_le_mul_of_nonneg_left h1; linarith

theorem Iio_eq {t : ℕ} (s : Fin t) :
    Finset.Iio s = Finset.univ.filter (fun q : Fin t => (q : ℕ) < s) := by
  ext q; simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and]; exact Fin.lt_def

theorem prod_bound {r : ℕ} {c : ℝ} (hc : 0 ≤ c) {t : ℕ} (y : Fin t → ℝ)
    (hy : y ∈ VstarFeasible r c t) (c0 : ℝ) (hc0 : c ≤ c0) :
    ∀ k : ℕ, k ≤ t →
      ∏ q ∈ Finset.univ.filter (fun q : Fin t => (q : ℕ) < k), (1 + y q) ≤
        1 + k * (c0 * ((r : ℝ) + t)) ^ r := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkt : k < t := hk
    have ih' := ih hkt.le
    set s : Fin t := ⟨k, hkt⟩ with hs
    have hfil : Finset.univ.filter (fun q : Fin t => (q : ℕ) < k + 1) =
        insert s (Finset.univ.filter (fun q : Fin t => (q : ℕ) < k)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hs, Fin.ext_iff]
      omega
    have hns : s ∉ Finset.univ.filter (fun q : Fin t => (q : ℕ) < k) := by
      simp [hs]
    rw [hfil, Finset.prod_insert hns]
    set Pk := ∏ q ∈ Finset.univ.filter (fun q : Fin t => (q : ℕ) < k), (1 + y q) with hPk
    have hy0 : ∀ q, 0 ≤ y q := fun q => (hy q).1
    have hPk1 : 1 ≤ Pk := by
      have := Finset.prod_le_prod (s := Finset.univ.filter (fun q : Fin t => (q : ℕ) < k))
        (f := fun _ => (1 : ℝ)) (g := fun q => 1 + y q) (fun _ _ => zero_le_one)
        (fun q _ => by linarith [hy0 q])
      simpa [hPk] using this
    obtain ⟨hs0, hsc, hsb⟩ := hy s
    rw [Iio_eq, ← hPk] at hsb
    have hPpos : 0 < Pk := by linarith
    have h1 : Pk * y s ≤ (c * ((r : ℝ) + (((s : ℕ) : ℝ) + 1))) ^ r := by
      rw [le_div_iff₀ hPpos] at hsb
      linarith
    have h2 : (c * ((r : ℝ) + (((s : ℕ) : ℝ) + 1))) ^ r ≤ (c0 * ((r : ℝ) + t)) ^ r := by
      apply pow_le_pow_left₀ (by positivity)
      have : (((s : ℕ) : ℝ) + 1) ≤ t := by
        have : (s : ℕ) + 1 ≤ t := hkt
        exact_mod_cast this
      apply mul_le_mul hc0 (by linarith) (by positivity) (le_trans hc hc0)
    calc (1 + y s) * Pk = Pk + Pk * y s := by ring
      _ ≤ (1 + k * (c0 * ((r : ℝ) + t)) ^ r) + (c0 * ((r : ℝ) + t)) ^ r := by linarith
      _ = 1 + ((k + 1 : ℕ) : ℝ) * (c0 * ((r : ℝ) + t)) ^ r := by push_cast; ring

end LPUhelp

theorem solution {r : ℕ} (hr : 2 ≤ r) (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (ht : 1 ≤ t) :
    Vstar r c t ≤
      2 * max 1 c * ((r : ℝ) * Real.log (max 1 c) + ((r : ℝ) + 1) * Real.log ((r : ℝ) + t + 1)) := by
  set c0 := max 1 c with hc0def
  have hc0 : 1 ≤ c0 := le_max_left _ _
  have hcc : c ≤ c0 := le_max_right _ _
  unfold Vstar
  apply csSup_le
  · refine ⟨_, ⟨fun _ => (0 : ℝ), ?_, rfl⟩⟩
    intro s
    refine ⟨le_refl _, hc, ?_⟩
    simp only [add_zero, Finset.prod_const_one, div_one]
    positivity
  · rintro _ ⟨y, hy, rfl⟩
    have hy0 : ∀ q, 0 ≤ y q := fun q => (hy q).1
    have hfull := LPUhelp.prod_bound hc y hy c0 hcc t le_rfl
    have huniv : Finset.univ.filter (fun q : Fin t => (q : ℕ) < t) = Finset.univ := by
      ext q; simp
    rw [huniv] at hfull
    set PP := ∏ q : Fin t, (1 + y q) with hPPdef
    have hPPpos : 0 < PP := Finset.prod_pos fun q _ => by linarith [hy0 q]
    have hrt : (1 : ℝ) ≤ (r : ℝ) + t := by
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    have hX1 : (1 : ℝ) ≤ (c0 * ((r : ℝ) + t)) ^ r :=
      one_le_pow₀ (by nlinarith)
    have hbound : PP ≤ c0 ^ r * ((r : ℝ) + t + 1) ^ (r + 1) := by
      have h1 : 1 + (t : ℝ) * (c0 * ((r : ℝ) + t)) ^ r ≤
          ((r : ℝ) + t + 1) * (c0 * ((r : ℝ) + t)) ^ r := by
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        nlinarith
      have h2 : ((r : ℝ) + t + 1) * (c0 * ((r : ℝ) + t)) ^ r ≤
          c0 ^ r * ((r : ℝ) + t + 1) ^ (r + 1) := by
        rw [mul_pow, pow_succ]
        have : ((r : ℝ) + t) ^ r ≤ ((r : ℝ) + t + 1) ^ r :=
          pow_le_pow_left₀ (by linarith) (by linarith) r
        have hc0r : 0 ≤ c0 ^ r := by positivity
        have : c0 ^ r * ((r : ℝ) + t) ^ r ≤ c0 ^ r * ((r : ℝ) + t + 1) ^ r :=
          mul_le_mul_of_nonneg_left this hc0r
        nlinarith
      linarith
    have hlog : ∑ q : Fin t, Real.log (1 + y q) = Real.log PP := by
      rw [hPPdef, Real.log_prod]
      intro q _
      linarith [hy0 q]
    have hlog2 : Real.log PP ≤ (r : ℝ) * Real.log c0 + ((r : ℝ) + 1) * Real.log ((r : ℝ) + t + 1) := by
      calc Real.log PP ≤ Real.log (c0 ^ r * ((r : ℝ) + t + 1) ^ (r + 1)) :=
            Real.log_le_log hPPpos hbound
        _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; ring
    calc ∑ q : Fin t, y q ≤ ∑ q : Fin t, 2 * c0 * Real.log (1 + y q) :=
          Finset.sum_le_sum fun q _ => LPUhelp.sub_le_log hc0 (hy0 q) (le_trans (hy q).2.1 hcc)
      _ = 2 * c0 * Real.log PP := by rw [← Finset.mul_sum, hlog]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog2 (by linarith)
