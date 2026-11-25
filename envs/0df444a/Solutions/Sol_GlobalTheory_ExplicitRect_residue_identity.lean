-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.residue_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:09.815061+00:00
-- url     : https://prove2.me/submissions/0fe4ed5c-5a5e-4f72-a4e1-9f78ee6e6011

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
import Theorems.Thm_GlobalTheory_ExplicitRect_logDeriv_pole
import Theorems.Thm_GlobalTheory_ExplicitRect_analyticAt_cpow
import Theorems.Thm_GlobalTheory_ExplicitRect_expand_simple
import Theorems.Thm_GlobalTheory_ExplicitRect_expand_zero
import Theorems.Thm_GlobalTheory_ExplicitRect_analyticOff
import Theorems.Thm_GlobalTheory_ExplicitRect_finite_zeros
import Theorems.Thm_GlobalTheory_ExplicitRect_order_ne_top
import Theorems.Thm_GlobalTheory_ExplicitRect_logDeriv_one
import Theorems.Thm_GlobalTheory_LFunction_zero_of_re_nonpos
import Theorems.Thm_GlobalTheory_ResRect_residue_rectangle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ (u c T : ℝ) (m : ℕ) (h : ℂ → ℂ), 1 < u → 1 < c → 0 < T → AnalyticAt ℂ h 0 → (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv (LFunction χ) s / LFunction χ s = (m : ℂ) / s + h s) → (∀ s : ℂ, -(1/2 : ℝ) ≤ s.re → s.re ≤ c → |s.im| = T → LFunction χ s ≠ 0) → (∀ s : ℂ, s.re = -(1/2 : ℝ) → LFunction χ s ≠ 0) → (∫ x : ℝ in (-(1/2 : ℝ))..c, (-(deriv (LFunction χ) ((x : ℂ) - T * I) / LFunction χ ((x : ℂ) - T * I)) * (u : ℂ) ^ ((x : ℂ) - T * I) / ((x : ℂ) - T * I))) - (∫ x : ℝ in (-(1/2 : ℝ))..c, (-(deriv (LFunction χ) ((x : ℂ) + T * I) / LFunction χ ((x : ℂ) + T * I)) * (u : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I))) + I * (∫ t : ℝ in (-T)..T, (-(deriv (LFunction χ) ((c : ℂ) + t * I) / LFunction χ ((c : ℂ) + t * I)) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) - I * (∫ t : ℝ in (-T)..T, (-(deriv (LFunction χ) (((-(1/2) : ℝ) : ℂ) + t * I) / LFunction χ (((-(1/2) : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((-(1/2) : ℝ) : ℂ) + t * I) / (((-(1/2) : ℝ) : ℂ) + t * I))) = 2 * Real.pi * I * ((if N = 1 then (u : ℂ) else 0) - (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)) - (m * (Real.log u : ℂ) + h 0)) := by
  intro N _ χ hχ u c T m h hu hc hT hh hφ0 hside hleft
  have hu0 : (0 : ℝ) < u := by linarith
  let f : ℂ → ℂ := fun s => -(deriv (LFunction χ) s / LFunction χ s) * (u : ℂ) ^ s / s
  have hZfin := finite_zeros χ T
  have h0Z : (0 : ℂ) ∉ hZfin.toFinset := by simp
  have h1Z : (1 : ℂ) ∉ hZfin.toFinset := by simp
  have h1S : (1 : ℂ) ∉ insert (0 : ℂ) hZfin.toFinset := by
    simp only [Finset.mem_insert, one_ne_zero, false_or]; exact h1Z
  let S : Finset ℂ := insert 1 (insert 0 hZfin.toFinset)
  let r : ℂ → ℂ := fun p => if p = 1 then -((if N = 1 then (-1 : ℂ) else 0) * ((u : ℂ) ^ p / p))
    else if p = 0 then -(m * (Real.log u : ℂ) + h 0)
    else -((analyticOrderNatAt (LFunction χ) p : ℕ) * ((u : ℂ) ^ p / p))
  have hins : ∀ p ∈ S, (⟨-(1/2), -T⟩ : ℂ).re < p.re ∧ p.re < (⟨c, T⟩ : ℂ).re ∧
      (⟨-(1/2), -T⟩ : ℂ).im < p.im ∧ p.im < (⟨c, T⟩ : ℂ).im := by
    intro p hp
    show -(1/2 : ℝ) < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T
    simp only [S, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    rcases hp with rfl | rfl | ⟨h0, h1, hT', -⟩
    · exact ⟨by simp only [Complex.one_re]; linarith, by simp only [Complex.one_re]; linarith,
        by simp only [Complex.one_im]; linarith, by simp only [Complex.one_im]; linarith⟩
    · exact ⟨by simp only [Complex.zero_re]; linarith, by simp only [Complex.zero_re]; linarith,
        by simp only [Complex.zero_im]; linarith, by simp only [Complex.zero_im]; linarith⟩
    · rw [abs_lt] at hT'
      exact ⟨by linarith, by linarith, hT'.1, hT'.2⟩
  have hdiff : DifferentiableOn ℂ f ((Set.Icc (⟨-(1/2), -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ
      Set.Icc (⟨-(1/2), -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im) \ ↑S) := by
    intro s hs
    obtain ⟨hsR, hsS⟩ := hs
    rw [Complex.mem_reProdIm] at hsR
    obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩⟩ := hsR
    change -(1/2 : ℝ) ≤ s.re at hre1
    change s.re ≤ c at hre2
    change -T ≤ s.im at him1
    change s.im ≤ T at him2
    have hs1 : s ≠ 1 := fun h' => hsS (by simp [S, h'])
    have hs0 : s ≠ 0 := fun h' => hsS (by simp [S, h'])
    have hLs : LFunction χ s ≠ 0 := by
      intro hL
      by_cases hI : |s.im| = T
      · exact hside s hre1 hre2 hI hL
      by_cases hRe : s.re = -(1/2 : ℝ)
      · exact hleft s hRe hL
      by_cases h1 : 1 ≤ s.re
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr hs1) h1 hL
      by_cases h0 : s.re ≤ 0
      · obtain ⟨⟨n, hn⟩, -⟩ := GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ s h0 hL
        have hre : s.re = -(n : ℝ) := by rw [hn]; simp
        have hn0 : n = 0 := by
          by_contra hne
          have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
        exact hs0 (by rw [hn, hn0]; simp)
      · have hI' : |s.im| < T := lt_of_le_of_ne (abs_le.mpr ⟨him1, him2⟩) hI
        apply hsS
        simp only [S, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Set.Finite.mem_toFinset,
          Set.mem_ofPred_eq]
        exact Or.inr (Or.inr ⟨by linarith, by linarith, hI', hL⟩)
    have hLa : AnalyticAt ℂ (LFunction χ) s := analyticOff χ s hs1
    have hd1 : DifferentiableAt ℂ (deriv (LFunction χ)) s := hLa.deriv.differentiableAt
    have hd2 : DifferentiableAt ℂ (fun s : ℂ => (u : ℂ) ^ s) s := (analyticAt_cpow hu0 s).differentiableAt
    exact (((hd1.div hLa.differentiableAt hLs).neg.mul hd2).div differentiableAt_id hs0).differentiableWithinAt
  have hexp : ∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧
      ∀ᶠ s in nhdsWithin p {p}ᶜ, f s = a / (s - p) ^ 2 + r p / (s - p) + g s := by
    intro p hp
    simp only [S, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    rcases hp with rfl | rfl | hpZ
    · obtain ⟨g1, hg1, hφ1⟩ := logDeriv_one hχ
      obtain ⟨a, G, hG, hfe⟩ := expand_simple
        (φ := fun s => deriv (LFunction χ) s / LFunction χ s) hu0 one_ne_zero hg1 hφ1
      have hr : r 1 = -((if N = 1 then (-1 : ℂ) else 0) * ((u : ℂ) ^ (1 : ℂ) / 1)) := by simp [r]
      exact ⟨a, G, hG, by rw [hr]; exact hfe⟩
    · obtain ⟨a, G, hG, hfe⟩ := expand_zero
        (φ := fun s => deriv (LFunction χ) s / LFunction χ s) hu0 hh hφ0
      have hr : r 0 = -(m * (Real.log u : ℂ) + h 0) := by simp [r]
      exact ⟨a, G, hG, by rw [hr]; exact hfe⟩
    · have hp1 : p ≠ 1 := by rintro rfl; simp at hpZ
      have hp0 : p ≠ 0 := by rintro rfl; simp at hpZ
      obtain ⟨g, hg, hφp⟩ := logDeriv_pole (analyticOff χ p hp1) (order_ne_top χ hp1)
      obtain ⟨a, G, hG, hfe⟩ := expand_simple
        (φ := fun s => deriv (LFunction χ) s / LFunction χ s) hu0 hp0 hg hφp
      have hr : r p = -((analyticOrderNatAt (LFunction χ) p : ℕ) * ((u : ℂ) ^ p / p)) := by
        simp [r, hp1, hp0]
      exact ⟨a, G, hG, by rw [hr]; exact hfe⟩
  have key : (∫ x : ℝ in (-(1/2) : ℝ)..c, f (x + ((-T : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in (-(1/2) : ℝ)..c, f (x + (T : ℂ) * I)) +
      I * (∫ y : ℝ in (-T)..T, f ((c : ℂ) + y * I)) -
      I * (∫ y : ℝ in (-T)..T, f (((-(1/2) : ℝ) : ℂ) + y * I)) = 2 * Real.pi * I * ∑ p ∈ S, r p :=
    GlobalTheory.ResRect.residue_rectangle f ⟨-(1/2), -T⟩ ⟨c, T⟩ S r
      (show (-(1/2) : ℝ) < c by linarith) (show -T < T by linarith) hins hdiff hexp
  have e : ∀ x : ℝ, (x : ℂ) - (T : ℂ) * I = (x : ℂ) + ((-T : ℝ) : ℂ) * I := by
    intro x; push_cast; ring
  simp only [e]
  refine key.trans ?_
  have hr1 : r 1 = if N = 1 then (u : ℂ) else 0 := by
    simp only [r, if_pos]
    split_ifs <;> simp
  have hr0 : r 0 = -(m * (Real.log u : ℂ) + h 0) := by simp [r]
  have hrZ : ∑ p ∈ hZfin.toFinset, r p =
      -∑ p ∈ hZfin.toFinset, ((analyticOrderNatAt (LFunction χ) p : ℕ) : ℂ) * ((u : ℂ) ^ p / p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := fun h' => h0Z (h' ▸ hp)
    have hp1 : p ≠ 1 := fun h' => h1Z (h' ▸ hp)
    simp [r, hp1, hp0]
  rw [Finset.sum_insert h1S, Finset.sum_insert h0Z, hr1, hr0, hrZ,
    finsum_mem_eq_finite_toFinset_sum _ hZfin]
  ring
end GlobalTheory.ExplicitRect
