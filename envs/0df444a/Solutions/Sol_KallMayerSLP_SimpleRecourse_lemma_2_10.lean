-- Prove2me | solution 1 for KallMayerSLP.SimpleRecourse.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:51:16.460017+00:00
-- url     : https://prove2.me/submissions/d85d3044-c8b8-4c37-a8b8-f38439e1b285

import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory KallMayerSLP.SimpleRecourse

private lemma core_convex (α β γ : ℝ) (hαβ : 0 ≤ α + β) :
    ConvexOn ℝ Set.univ (fun w : ℝ => α * w⁺ + β * w⁻ - γ) := by
  have heq (w : ℝ) : α * w⁺ + β * w⁻ - γ = max (α * w) (-β * w) - γ := by
    by_cases hw : 0 ≤ w
    · rw [posPart_def, negPart_def, max_eq_left hw, max_eq_right (by linarith)]
      rw [max_eq_left (by nlinarith [mul_nonneg hαβ hw])]
      ring
    · have hw' : w ≤ 0 := le_of_not_ge hw
      rw [posPart_def, negPart_def, max_eq_right hw', max_eq_left (by linarith)]
      rw [max_eq_right (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hαβ hw'])]
      ring
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, heq]
  have hlx := mul_le_mul_of_nonneg_left (le_max_left (α*x) (-β*x)) ha
  have hly := mul_le_mul_of_nonneg_left (le_max_left (α*y) (-β*y)) hb
  have hrx := mul_le_mul_of_nonneg_left (le_max_right (α*x) (-β*x)) ha
  have hry := mul_le_mul_of_nonneg_left (le_max_right (α*y) (-β*y)) hb
  have hγ : a * γ + b * γ = γ := by rw [← add_mul, hab, one_mul]
  apply sub_le_iff_le_add.mpr
  apply max_le
  · nlinarith only [hlx, hly, hγ]
  · nlinarith only [hrx, hry, hγ]

private lemma srt_z_convex (α β γ ξ : ℝ) (hαβ : 0 ≤ α + β) :
    ConvexOn ℝ Set.univ (fun z => srt α β γ z ξ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (core_convex α β γ hαβ).2 (Set.mem_univ (ξ-x)) (Set.mem_univ (ξ-y)) ha hb hab
  have heq : a * (ξ-x) + b * (ξ-y) = ξ - (a*x+b*y) := calc
    _ = (a + b) * ξ - (a*x+b*y) := by ring
    _ = _ := by rw [hab, one_mul]
  simpa only [srt, smul_eq_mul, heq] using h

theorem solution (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : Integrable (fun ξ => ξ) P) :
    (∀ z : ℝ, ConvexOn ℝ Set.univ (fun ξ => srt α β γ z ξ)) ∧
    (∀ ξ : ℝ, ConvexOn ℝ Set.univ (fun z => srt α β γ z ξ)) ∧
    ConvexOn ℝ Set.univ (expectedSRT α β γ P) := by
  refine ⟨?_, fun ξ => srt_z_convex α β γ ξ hαβ, ?_⟩
  · intro z
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := (core_convex α β γ hαβ).2 (Set.mem_univ (x-z)) (Set.mem_univ (y-z)) ha hb hab
    have heq : a*(x-z)+b*(y-z) = a*x+b*y-z := calc
      _ = a*x+b*y-(a+b)*z := by ring
      _ = _ := by rw [hab, one_mul]
    simpa only [srt, smul_eq_mul, heq] using h
  · let F (z ξ : ℝ) := α * (ξ-z)⁺ + β * (ξ-z)⁻
    have hint (z : ℝ) : Integrable (F z) P := by
      have hz : Integrable (fun ξ : ℝ => ξ - z) P := hP.sub' (integrable_const z)
      have hp : Integrable (fun ξ : ℝ => (ξ-z)⁺) P := by
        simpa only [posPart_def] using hz.pos_part
      have hn : Integrable (fun ξ : ℝ => (ξ-z)⁻) P := by
        simpa only [negPart_def] using hz.neg_part
      exact (hp.const_mul α).add (hn.const_mul β)
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    change (∫ ξ, F (a*x+b*y) ξ ∂P) - γ ≤
      a * ((∫ ξ, F x ξ ∂P) - γ) + b * ((∫ ξ, F y ξ ∂P) - γ)
    have hc (ξ : ℝ) : F (a*x+b*y) ξ ≤ a * F x ξ + b * F y ξ := by
      simpa only [F, srt, sub_zero, smul_eq_mul] using
        (srt_z_convex α β 0 ξ hαβ).2 hx hy ha hb hab
    have hi : (∫ ξ, F (a*x+b*y) ξ ∂P) ≤ ∫ ξ, a * F x ξ + b * F y ξ ∂P :=
      integral_mono (hint (a*x+b*y)) (((hint x).const_mul a).add ((hint y).const_mul b)) hc
    rw [integral_add ((hint x).const_mul a) ((hint y).const_mul b), integral_const_mul,
      integral_const_mul] at hi
    have hγ : a * γ + b * γ = γ := by rw [← add_mul, hab, one_mul]
    nlinarith only [hi, hγ]

#print axioms solution
