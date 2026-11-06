-- Prove2me | solution 1 for LeiBR.Async.eq_C2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:08:19.216902+00:00
-- url     : https://prove2.me/submissions/bd4517ee-fc77-4896-b39c-1605f961856c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm
import Theorems.Thm_LeiBR_Async_eq_40
import Theorems.Thm_LeiBR_Async_eq_5

open MeasureTheory

namespace LeiBRC2Aux

theorem integral_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg0 : ∀ ω, 0 ≤ g ω) (hgm : Measurable g) (B : ℝ) (hB : ∀ ω, g ω ≤ B)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∫ ω, g ω ^ 2 ∂P ≤ C ^ 2) : ∫ ω, g ω ∂P ≤ C := by
  have hL : MemLp g 2 P := by
    refine MemLp.of_bound hgm.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]; exact hB ω
  have hv := ProbabilityTheory.variance_nonneg g P
  rw [ProbabilityTheory.variance_eq_sub hL] at hv
  have e : ∫ x, (g ^ 2) x ∂P = ∫ ω, g ω ^ 2 ∂P := rfl
  rw [e] at hv
  nlinarith

end LeiBRC2Aux

open LeiBR.Async LeiBRC2Aux in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (xs : LeiBR.Sync.Profile n)
    (hNE : LeiBR.Sync.IsNashEq X f xs) (I : ℕ → Finset (Fin N)) (τ : Fin N → Fin N → ℕ → ℕ)
    (α : Fin N → ℕ → ℝ) (hα : ∀ i k, 0 ≤ α i k) (x : ℕ → Ω → LeiBR.Sync.Profile n)
    (halg : IsAlgorithm3 P F X xhat I τ α x) :
    ∀ k, ∀ i ∈ I k,
      ∫ ω, ‖x (k + 1) ω i - xs i‖ ∂P ≤
        α i k + normInf (LeiBR.Sync.Gamma X f μ) * ⨆ j, ∫ ω, ‖x (k - τ i j k) ω j - xs j‖ ∂P := by
  classical
  intro k i hi
  set y := delayed x τ i k with hydef
  have hxk : ∀ l, Measurable (x l) := fun l => (halg.adapted l).mono (F.le l) le_rfl
  have hy : Measurable y := by
    refine measurable_pi_lambda _ fun j => ?_
    exact (measurable_pi_apply j).comp (hxk _)
  have hyX : ∀ ω, y ω ∈ profileSet X := by
    intro ω
    simp only [profileSet, Set.mem_univ_pi]
    intro j
    have := halg.mem (k - τ i j k) ω
    simp only [profileSet, Set.mem_univ_pi] at this
    exact this j
  -- `x̂_i` is Lipschitz on `X`, hence `ω ↦ x̂_i(y ω)` is measurable
  have hlip : LipschitzOnWith (∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖₊) (fun z => xhat z i)
      (profileSet X) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [dist_eq_norm, dist_eq_norm]
    refine (eq_5 X f hA1 μ hμ xhat hxhat b hb a ha i).trans ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : ‖a j - b j‖ ≤ ‖a - b‖ := norm_le_pi_norm (a - b) j
    calc LeiBR.Sync.Gamma X f μ i j * ‖a j - b j‖ ≤ ‖LeiBR.Sync.Gamma X f μ i j‖ * ‖a j - b j‖ :=
          mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _)
      _ ≤ ‖LeiBR.Sync.Gamma X f μ i j‖ * ‖a - b‖ :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hg : Measurable (fun ω => xhat (y ω) i) := by
    have hc : Continuous (fun z : profileSet X => xhat (z : LeiBR.Sync.Profile n) i) :=
      hlip.continuousOn.domRestrict
    have hys : Measurable (fun ω => (⟨y ω, hyX ω⟩ : profileSet X)) := hy.subtype_mk
    exact hc.measurable.comp hys
  have hgX : ∀ ω, xhat (y ω) i ∈ X i := fun ω => (hxhat (y ω) (hyX ω) i).1
  have hx1 : Measurable (fun ω => x (k + 1) ω i) := (measurable_pi_apply i).comp (hxk _)
  have hx1X : ∀ ω, x (k + 1) ω i ∈ X i := by
    intro ω
    have := halg.mem (k + 1) ω
    simp only [profileSet, Set.mem_univ_pi] at this
    exact this i
  have hxs : xs i ∈ X i := hNE.1 i (Set.mem_univ i)
  have hbd := (hA1.compact i).isBounded
  have hint : ∀ a b : Ω → LeiBR.Sync.Strat n i, Measurable a → Measurable b →
      (∀ ω, a ω ∈ X i) → (∀ ω, b ω ∈ X i) → Integrable (fun ω => ‖a ω - b ω‖) P := by
    intro a b ha hb haX hbX
    refine Integrable.of_bound (C := Metric.diam (X i)) (ha.sub hb).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_norm, ← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hbd (haX ω) (hbX ω)
  -- first term: conditional Jensen
  have hfirst : ∫ ω, ‖x (k + 1) ω i - xhat (y ω) i‖ ∂P ≤ α i k := by
    have hsq : ∫ ω, ‖x (k + 1) ω i - xhat (y ω) i‖ ^ 2 ∂P ≤ α i k ^ 2 := by
      rw [← integral_condExp (F.le k)]
      calc ∫ ω, (P[fun ω => ‖x (k + 1) ω i - xhat (y ω) i‖ ^ 2 | F k]) ω ∂P
          ≤ ∫ ω, α i k ^ 2 ∂P := integral_mono_ae integrable_condExp (integrable_const _)
            (halg.inexact k i hi)
        _ = α i k ^ 2 := by simp
    refine integral_le_of_sq P (fun ω => ‖x (k + 1) ω i - xhat (y ω) i‖) (fun ω => norm_nonneg _)
      (hx1.sub hg).norm (Metric.diam (X i))
      (fun ω => ?_) (α i k) (hα i k) hsq
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hbd (hx1X ω) (hgX ω)
  have h40 := eq_40 P X f hA1 μ hμ xhat hxhat xs hNE y hy hyX i
  calc ∫ ω, ‖x (k + 1) ω i - xs i‖ ∂P
      ≤ ∫ ω, (‖x (k + 1) ω i - xhat (y ω) i‖ + ‖xhat (y ω) i - xs i‖) ∂P := by
        refine integral_mono (hint _ _ hx1 measurable_const hx1X fun _ => hxs)
          ((hint _ _ hx1 hg hx1X hgX).add (hint _ _ hg measurable_const hgX fun _ => hxs))
          fun ω => ?_
        have := norm_sub_le_norm_sub_add_norm_sub (x (k + 1) ω i) (xhat (y ω) i) (xs i)
        exact this
    _ = ∫ ω, ‖x (k + 1) ω i - xhat (y ω) i‖ ∂P + ∫ ω, ‖xhat (y ω) i - xs i‖ ∂P :=
        integral_add (hint _ _ hx1 hg hx1X hgX) (hint _ _ hg measurable_const hgX fun _ => hxs)
    _ ≤ α i k + normInf (LeiBR.Sync.Gamma X f μ) * ⨆ j, ∫ ω, ‖y ω j - xs j‖ ∂P := by
        rw [h40.1]; exact add_le_add hfirst h40.2
    _ = α i k + normInf (LeiBR.Sync.Gamma X f μ) *
          ⨆ j, ∫ ω, ‖x (k - τ i j k) ω j - xs j‖ ∂P := rfl
