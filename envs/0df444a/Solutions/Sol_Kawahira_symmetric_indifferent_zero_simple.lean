-- Prove2me | solution 1 for Kawahira.symmetric_indifferent_zero_simple
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:48:14.958494+00:00
-- url     : https://prove2.me/submissions/ff973922-beab-4616-b3cf-bffc8a88d629

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nu_indifferent_zero_order_re

open Complex Topology
open Kawahira

theorem solution (g : ℂ → ℂ)
    (hg : ∀ a : ℂ, AnalyticAt ℂ g a)
    (hfinite : ∀ a : ℂ, analyticOrderAt g a ≠ ⊤)
    (hsymm : ∀ z : ℂ, g (1 - z) = g z)
    (hind : ∀ a : ℂ, a ≠ 0 → g a = 0 → IsIndifferentFixedPoint (nu g) a)
    (s : ℂ) (hszero : g s = 0) (hstrip : 0 < s.re ∧ s.re < 1) :
    s.re = 1 / 2 ∧ deriv g s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hstrip
  let t : ℂ := 1 - s
  have htzero : g t = 0 := by
    dsimp [t]
    rw [hsymm, hszero]
  have htstrip : 0 < t.re ∧ t.re < 1 := by
    dsimp [t]
    constructor <;> linarith [hstrip.1, hstrip.2]
  have ht0 : t ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [t] at hre
    linarith [hstrip.2]
  have hsind := hind s hs0 hszero
  have htind := hind t ht0 htzero
  let m := analyticOrderNatAt g s
  let n := analyticOrderNatAt g t
  have hsorder : analyticOrderAt g s = (m : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt (hfinite s)).symm
  have htorder : analyticOrderAt g t = (n : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt (hfinite t)).symm
  have hm0 : m ≠ 0 := by
    intro hm
    have hne : analyticOrderAt g s ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hg s, hszero⟩
    apply hne
    simpa [hm] using hsorder
  have hn0 : n ≠ 0 := by
    intro hn
    have hne : analyticOrderAt g t ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hg t, htzero⟩
    apply hne
    simpa [hn] using htorder
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hsmult : (m : ℝ) * s.re = 1 / 2 :=
    nu_indifferent_zero_order_re g s m hs0 hm (hg s) hsorder hsind
  have htmult : (n : ℝ) * t.re = 1 / 2 :=
    nu_indifferent_zero_order_re g t n ht0 hn (hg t) htorder htind
  have htmult' : (n : ℝ) * (1 - s.re) = 1 / 2 := by
    simpa [t] using htmult
  have hm_eq : m = 1 := by
    by_contra hmne
    have hm2 : 2 ≤ m := by omega
    have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmx : 2 * s.re ≤ (m : ℝ) * s.re :=
      mul_le_mul_of_nonneg_right hm2R (le_of_lt hstrip.1)
    have hnx : 1 - s.re ≤ (n : ℝ) * (1 - s.re) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hnR (by linarith [hstrip.2] : 0 ≤ 1 - s.re)
    linarith
  have hsre : s.re = 1 / 2 := by
    simpa [hm_eq] using hsmult
  have hsderiv : deriv g s ≠ 0 := by
    have horder1 : analyticOrderAt g s = (↑(1 : ℕ) : ℕ∞) := by
      simpa [hm_eq] using hsorder
    have hchar := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hg s)).1 horder1
    simpa [iteratedDeriv_one] using hchar.2
  exact ⟨hsre, hsderiv⟩
