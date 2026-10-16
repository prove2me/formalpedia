-- Prove2me | solution 1 for OAI.ShortEgyptian.interval_van_der_corput
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:20:45.938364+00:00
-- url     : https://prove2.me/submissions/1c0d8e5b-561a-4fd6-bee4-f5c6ae4f6231

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/IntervalDifferencing.lean:L120-L176
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.interval_van_der_corput. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing

-- ---- from OAI.NumberTheory.ShortEgyptian.FiniteFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uG

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem complex_sum_sq_le {ι : Type uι} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hn := norm_sum_le s f
  have hs0 : 0 ≤ ∑ i ∈ s, ‖f i‖ := Finset.sum_nonneg (by intros; positivity)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  exact ((sq_le_sq₀ (norm_nonneg _) hs0).mpr hn).trans hc

theorem complex_sum_norm_sq {ι : Type uι} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (f i * (starRingEnd ℂ) (f j)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_comm

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.IntervalDifferencing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι uκ uM

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem matrix_van_der_corput {ι : Type uι} {κ : Type uκ} (S : Finset ι) (H : Finset κ)
    (hH : H.Nonempty) (a : ι → κ → ℂ) (W : ℂ) (E C : ℝ) (hC : 0 ≤ C)
    (hsum : ∀ h ∈ H, (∑ x ∈ S, a x h) = W)
    (henergy : ∀ h ∈ H, (∑ x ∈ S, ‖a x h‖ ^ 2) ≤ E)
    (hcorr : ∀ h ∈ H, ∀ k ∈ H, h ≠ k →
      ‖∑ x ∈ S, a x h * (starRingEnd ℂ) (a x k)‖ ≤ C) :
    ‖W‖ ^ 2 ≤ (S.card : ℝ) / H.card * E + S.card * C := by
  classical
  let F (x : ι) := ∑ h ∈ H, a x h
  have hsum' : (∑ x ∈ S, F x) = (H.card : ℂ) * W := by
    rw [show (∑ x ∈ S, F x) = ∑ h ∈ H, ∑ x ∈ S, a x h from Finset.sum_comm]
    rw [Finset.sum_congr rfl hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hterm (h : κ) (hh : h ∈ H) (k : κ) (hk : k ∈ H) :
      (∑ x ∈ S, (a x h * (starRingEnd ℂ) (a x k)).re) ≤
        (if h = k then E else 0) + C := by
    by_cases heq : h = k
    · subst k
      simp only [ite_true, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      linarith [henergy h hh]
    · rw [ite_eq_right heq, zero_add, ← Complex.re_sum]
      exact (Complex.re_le_norm _).trans (hcorr h hh k hk heq)
  have hE : (∑ x ∈ S, ‖F x‖ ^ 2) ≤ H.card * E + (H.card : ℝ) ^ 2 * C := by
    simp only [F, complex_sum_norm_sq]
    rw [Finset.sum_comm]
    have hex : (∑ h ∈ H, ∑ x ∈ S, ∑ k ∈ H,
        (a x h * (starRingEnd ℂ) (a x k)).re) =
        ∑ h ∈ H, ∑ k ∈ H, ∑ x ∈ S,
        (a x h * (starRingEnd ℂ) (a x k)).re := by
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
    rw [hex]
    calc
      _ ≤ ∑ h ∈ H, ∑ k ∈ H, ((if h = k then E else 0) + C) :=
        sum_le_sum (fun h hh => sum_le_sum (fun k hk => hterm h hh k hk))
      _ = H.card * E + (H.card : ℝ) ^ 2 * C := by
        simp [Finset.sum_add_distrib, Finset.sum_ite_eq, pow_two, mul_assoc]
  have hcs := complex_sum_sq_le S F
  rw [hsum', norm_mul, Complex.norm_natCast, mul_pow] at hcs
  have hcard : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg S.card))
  have heq : (H.card : ℝ) ^ 2 * ((S.card : ℝ) / H.card * E + S.card * C) =
      S.card * (H.card * E + (H.card : ℝ) ^ 2 * C) := by field_simp
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hcard)).mp
  rw [heq]
  exact hbound

theorem supported_interval_sum_shift {M : Type uM} [AddCommMonoid M]
    (a : ℤ → M) (p q L h : ℤ) (hh0 : 0 ≤ h) (hhL : h ≤ L)
    (hsupp : ∀ n, n ∉ Icc p q → a n = 0) :
    (∑ n ∈ Icc (p - L) q, a (n + h)) = ∑ n ∈ Icc p q, a n := by
  classical
  apply Finset.sum_bij_ne_zero (fun n _ _ => n + h)
  · intro n _ hn
    by_contra hn'
    exact hn (hsupp _ hn')
  · intro n _ _ m _ _ heq
    omega
  · intro m hm hm0
    have hm' := mem_Icc.mp hm
    have hn : m - h ∈ Icc (p - L) q := mem_Icc.mpr ⟨by omega, by omega⟩
    refine ⟨m - h, hn, ?_, by omega⟩
    simpa only [sub_add_cancel] using hm0
  · intros
    rfl

theorem correlation_norm_symm {ι : Type uι} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ x ∈ S, a x * (starRingEnd ℂ) (b x)‖ =
      ‖∑ x ∈ S, b x * (starRingEnd ℂ) (a x)‖ := by
  rw [← Complex.norm_conj (∑ x ∈ S, a x * (starRingEnd ℂ) (b x)), map_sum]
  simp only [map_mul, starRingEnd_self_apply]
  congr 1
  apply sum_congr rfl
  intro x _
  ring

theorem interval_van_der_corput (a : ℤ → ℂ) (p q : ℤ) (hpq : p ≤ q)
    (L : ℕ) (hL : 1 ≤ L) (C : ℝ) (hC : 0 ≤ C)
    (hsupp : ∀ n, n ∉ Icc p q → a n = 0)
    (hnorm : ∀ n ∈ Icc p q, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 1 ≤ h → h < L →
      ‖∑ n ∈ Icc p q, a (n + h) * (starRingEnd ℂ) (a n)‖ ≤ C) :
    ‖∑ n ∈ Icc p q, a n‖ ^ 2 ≤
      (((Icc p q).card : ℝ) + L) / L * (Icc p q).card +
      (((Icc p q).card : ℝ) + L) * C := by
  classical
  let S := Icc (p - (L : ℤ)) q
  let H := Icc (1 : ℤ) L
  have hH : H.Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hL⟩⟩
  have hsum (h : ℤ) (hh : h ∈ H) : (∑ x ∈ S, a (x + h)) = ∑ x ∈ Icc p q, a x :=
    supported_interval_sum_shift a p q L h (le_trans (by norm_num) (mem_Icc.mp hh).1) (mem_Icc.mp hh).2 hsupp
  have henergy (h : ℤ) (hh : h ∈ H) :
      (∑ x ∈ S, ‖a (x + h)‖ ^ 2) ≤ ((Icc p q).card : ℝ) := by
    rw [supported_interval_sum_shift (fun n => ‖a n‖ ^ 2) p q L h
      (le_trans (by norm_num) (mem_Icc.mp hh).1) (mem_Icc.mp hh).2
      (fun n hn => by rw [hsupp n hn]; simp)]
    calc
      _ ≤ ∑ _n ∈ Icc p q, (1 : ℝ) := sum_le_sum (fun n hn => by
        have hh := hnorm n hn
        nlinarith [norm_nonneg (a n)])
      _ = _ := by simp
  have hcorr' (h k : ℤ) (hh : h ∈ H) (hk : k ∈ H) (hkh : k < h) :
      ‖∑ x ∈ S, a (x + h) * (starRingEnd ℂ) (a (x + k))‖ ≤ C := by
    have heq := supported_interval_sum_shift
      (fun n => a (n + (h - k)) * (starRingEnd ℂ) (a n)) p q L k
      (le_trans (by norm_num) (mem_Icc.mp hk).1) (mem_Icc.mp hk).2
      (fun n hn => by rw [hsupp n hn]; simp)
    have heq' : (∑ x ∈ S, a (x + h) * (starRingEnd ℂ) (a (x + k))) =
        ∑ n ∈ Icc p q, a (n + (h - k)) * (starRingEnd ℂ) (a n) := by
      convert heq using 1
      apply sum_congr rfl
      intro x _
      congr 2
      ring
    rw [heq']
    apply hcorr (h - k) (by omega)
    have hh' := mem_Icc.mp hh
    have hk' := mem_Icc.mp hk
    omega
  have hh := matrix_van_der_corput S H hH (fun x h => a (x + h))
    (∑ x ∈ Icc p q, a x) ((Icc p q).card : ℝ) C hC hsum henergy (by
      intro h hh k hk hne
      rcases lt_or_gt_of_ne hne with hhk | hkh
      · rw [correlation_norm_symm]
        exact hcorr' k h hk hh hhk
      · exact hcorr' h k hh hk hkh)
  have hcH : H.card = L := by simp [H, Int.card_Icc]
  have hcS : S.card = (Icc p q).card + L := by
    simp only [S, Int.card_Icc]
    have h1 : 0 ≤ q + 1 - p := by omega
    have h2 : 0 ≤ q + 1 - (p - (L : ℤ)) := by omega
    exact_mod_cast (show (q + 1 - (p - (L : ℤ))).toNat = (q + 1 - p).toNat + L by omega)
  simpa only [hcH, hcS, Nat.cast_add] using hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.interval_van_der_corput := @_root_.OAI.ShortEgyptian.interval_van_der_corput
