-- Prove2me | solution 1 for GlobalTheory.ResRect.residue_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:37.213232+00:00
-- url     : https://prove2.me/submissions/f3317328-1a8d-47d4-9474-7957a0b2a243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_bdInt_add
import Theorems.Thm_GlobalTheory_ResRect_bdInt_sum
import Theorems.Thm_GlobalTheory_ResRect_bdInt_congr
import Theorems.Thm_GlobalTheory_ResRect_sidesIn_compl
import Theorems.Thm_GlobalTheory_ResRect_bdInt_sq
import Theorems.Thm_GlobalTheory_ResRect_bdInt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect
namespace GlobalTheory.ResRect
theorem _root_.solution :
    ∀ (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ) (r : ℂ → ℂ), z.re < w.re → z.im < w.im → (∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im) → DifferentiableOn ℂ f ((Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im) \ S) → (∀ p ∈ S, ∃ (a : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g p ∧ ∀ᶠ s in nhdsWithin p {p}ᶜ, f s = a / (s - p) ^ 2 + r p / (s - p) + g s) → (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) + I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) = 2 * Real.pi * I * ∑ p ∈ S, r p := by
  classical
  intro f z w S r hre him hS hf hp
  choose! a g hg hfg using hp
  set R : Set ℂ := Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im with hR
  let P : ℂ → ℂ → ℂ := fun p s => a p / (s - p) ^ 2 + r p / (s - p)
  have hP : ∀ p s, s ≠ p → DifferentiableAt ℂ (P p) s := fun p s hs => by
    have hs' : s - p ≠ 0 := sub_ne_zero.2 hs
    have hs2 : (s - p) ^ 2 ≠ 0 := pow_ne_zero _ hs'
    simp only [P]
    fun_prop (disch := assumption)
  let h : ℂ → ℂ := fun s =>
    if s ∈ S then g s s - ∑ q ∈ S.erase s, P q s else f s - ∑ q ∈ S, P q s
  have hopen : ∀ T : Finset ℂ, ∀ s ∉ T, ∀ᶠ t in nhds s, t ∉ T := fun T s hs =>
    T.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
  have hh : DifferentiableOn ℂ h R := by
    intro s hs
    by_cases hsS : s ∈ S
    · have hd : DifferentiableAt ℂ (fun t => g s t - ∑ q ∈ S.erase s, P q t) s :=
        (hg s hsS).differentiableAt.sub
          (DifferentiableAt.fun_sum fun q hq => hP q s (Finset.ne_of_mem_erase hq).symm)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      have e1 := eventually_nhdsWithin_iff.1 (hfg s hsS)
      filter_upwards [e1, hopen (S.erase s) s (Finset.notMem_erase s S)] with t ht1 ht2
      by_cases hts : t = s
      · subst hts
        simp only [h, if_pos hsS]
      · have htS : t ∉ S := fun ht => ht2 (Finset.mem_erase.2 ⟨hts, ht⟩)
        simp only [h, if_neg htS]
        rw [ht1 hts, ← Finset.add_sum_erase S _ hsS]
        simp only [P]
        ring
    · have hd : DifferentiableWithinAt ℂ (fun t => f t - ∑ q ∈ S, P q t) R s := by
        refine DifferentiableWithinAt.sub ?_
          (DifferentiableAt.fun_sum fun q hq => hP q s fun e => hsS (e ▸ hq)).differentiableWithinAt
        refine (hf s ⟨hs, hsS⟩).mono_of_mem_nhdsWithin ?_
        exact inter_mem_nhdsWithin R (hopen S s hsS)
      refine hd.congr_of_eventuallyEq ?_ (by simp only [h, if_neg hsS])
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen S s hsS)] with t ht
      have ht' : t ∉ S := ht
      simp only [h, if_neg ht']
  have hB : SidesIn z.re w.re z.im w.im (R \ S) := by
    rw [SidesIn, Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le]
    refine ⟨fun x hx => ⟨?_, fun hm => ?_⟩, fun x hx => ⟨?_, fun hm => ?_⟩,
      fun x hx => ⟨?_, fun hm => ?_⟩, fun x hx => ⟨?_, fun hm => ?_⟩⟩
    · simp [hR, mem_reProdIm, hx.1, hx.2, him.le]
    · simpa using (hS _ hm).2.2.1
    · simp [hR, mem_reProdIm, hx.1, hx.2, him.le]
    · simpa using (hS _ hm).2.2.2
    · simp [hR, mem_reProdIm, hx.1, hx.2, hre.le]
    · simpa using (hS _ hm).2.1
    · simp [hR, mem_reProdIm, hx.1, hx.2, hre.le]
    · simpa using (hS _ hm).1
  have hPc : ∀ p ∈ S, ContinuousOn (P p) (R \ S) := fun p hp s hs =>
    (hP p s fun e => hs.2 (e ▸ hp)).continuousAt.continuousWithinAt
  have h0 : bdInt z.re w.re z.im w.im h = 0 := by
    have := integral_boundary_rect_eq_zero_of_differentiableOn h z w
      (by rwa [Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le])
    simpa only [smul_eq_mul, bdInt] using this
  change bdInt z.re w.re z.im w.im f = _
  rw [bdInt_congr hB (g := fun s => h s + ∑ q ∈ S, P q s) (fun s hs => by
      have ht' : s ∉ S := hs.2
      simp only [h, if_neg ht']; ring),
    bdInt_add hB (hh.continuousOn.mono Set.diff_subset) (continuousOn_finset_sum _ hPc), h0,
    zero_add, bdInt_sum hB S hPc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hS p hp
  simp only [P]
  rw [bdInt_add (sidesIn_compl h1 h2 h3 h4) (f := fun s => a p / (s - p) ^ 2)
    (g := fun s => r p / (s - p))
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => pow_ne_zero _ (sub_ne_zero.2 hs))
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => sub_ne_zero.2 hs),
    bdInt_sq h1 h2 h3 h4, bdInt_inv h1 h2 h3 h4, zero_add]
end GlobalTheory.ResRect
