-- Prove2me | solution 1 for Kawahira.indifferent_in_strip_implies_rh_and_simplicity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:33:41.633972+00:00
-- url     : https://prove2.me/submissions/e238c0a5-0146-4fac-b55e-6de98153ad72

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
import Theorems.Thm_Kawahira_nu_indifferent_zero_order_re
import Theorems.Thm_Kawahira_riemannZeta_analyticOrderAt_ne_top

open Complex Topology
open Kawahira

theorem solution
    (h : ∀ a : ℂ, 0 < a.re → a.re < 1 → (riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) →
      nuZeta a = a → IsIndifferentFixedPoint nuZeta a) :
    ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0 := by
  intro s hs
  have hsstrip := Kawahira.nontrivial_zero_mem_strip s hs.1 hs.2
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hsstrip
  have hs1 : s ≠ 1 := by
    intro hone
    subst s
    norm_num at hsstrip
  let t : ℂ := 1 - s
  have htzero : riemannZeta t = 0 := by
    have hnat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      norm_num at hre
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith [hsstrip.1]
    dsimp [t]
    rw [riemannZeta_one_sub hnat hs1, hs.1, mul_zero]
  have htstrip : 0 < t.re ∧ t.re < 1 := by
    dsimp [t]
    constructor <;> linarith [hsstrip.1, hsstrip.2]
  have ht0 : t ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [t] at hre
    linarith [hsstrip.2]
  have ht1 : t ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    norm_num [t] at hre
    linarith [hsstrip.1]
  have hsfix : nuZeta s = s := by simp [nuZeta, nu, hs.1]
  have htfix : nuZeta t = t := by simp [nuZeta, nu, htzero]
  have hsind := h s hsstrip.1 hsstrip.2 (.inl hs.1) hsfix
  have htind := h t htstrip.1 htstrip.2 (.inl htzero) htfix
  have hsan : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hs1)
  have htan : AnalyticAt ℂ riemannZeta t :=
    analyticOn_riemannZeta t (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht1)
  let m := analyticOrderNatAt riemannZeta s
  let n := analyticOrderNatAt riemannZeta t
  have hsfinite := Kawahira.riemannZeta_analyticOrderAt_ne_top s hs1
  have htfinite := Kawahira.riemannZeta_analyticOrderAt_ne_top t ht1
  have hsorder : analyticOrderAt riemannZeta s = (m : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hsfinite).symm
  have htorder : analyticOrderAt riemannZeta t = (n : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt htfinite).symm
  have hm0 : m ≠ 0 := by
    intro hm
    have hne : analyticOrderAt riemannZeta s ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hsan, hs.1⟩
    apply hne
    simpa [hm] using hsorder
  have hn0 : n ≠ 0 := by
    intro hn
    have hne : analyticOrderAt riemannZeta t ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨htan, htzero⟩
    apply hne
    simpa [hn] using htorder
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hsmult : (m : ℝ) * s.re = 1 / 2 :=
    Kawahira.nu_indifferent_zero_order_re riemannZeta s m hs0 hm hsan hsorder
      (by simpa [nuZeta] using hsind)
  have htmult : (n : ℝ) * t.re = 1 / 2 :=
    Kawahira.nu_indifferent_zero_order_re riemannZeta t n ht0 hn htan htorder
      (by simpa [nuZeta] using htind)
  have htmult' : (n : ℝ) * (1 - s.re) = 1 / 2 := by
    simpa [t] using htmult
  have hm_eq : m = 1 := by
    by_contra hmne
    have hm2 : 2 ≤ m := by omega
    have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmx : 2 * s.re ≤ (m : ℝ) * s.re :=
      mul_le_mul_of_nonneg_right hm2R (le_of_lt hsstrip.1)
    have hnx : 1 - s.re ≤ (n : ℝ) * (1 - s.re) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hnR (by linarith [hsstrip.2] : 0 ≤ 1 - s.re)
    linarith
  have hsre : s.re = 1 / 2 := by
    simpa [hm_eq] using hsmult
  have hsderiv : deriv riemannZeta s ≠ 0 := by
    have horder1 : analyticOrderAt riemannZeta s = (↑(1 : ℕ) : ℕ∞) := by
      simpa [hm_eq] using hsorder
    have hchar := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hsan).1 horder1
    simpa [iteratedDeriv_one] using hchar.2
  exact ⟨hsre, hsderiv⟩
