-- Prove2me | solution 1 for McLeishCLT.MDA.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:30:14.527011+00:00
-- url     : https://prove2.me/submissions/5aec0590-3e87-4fb7-acae-7a4d553a68db

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting
import Theorems.Thm_McLeishCLT_MDA_theorem_2_1
import Theorems.Thm_McLeishCLT_MDA_trunc_integral_prodT_eq_one
import Theorems.Thm_McLeishCLT_MDA_trunc_prodT_uniformIntegrable
import Theorems.Thm_McLeishCLT_MDA_eq_2_5
import Theorems.Thm_McLeishCLT_MDA_trunc_isMDA

set_option autoImplicit false

namespace McLeishCLT.MDA.Thm23Proof

open MeasureTheory Filter Topology Set

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Convergence in probability is unchanged by modifications on events of vanishing
probability. -/
theorem tendstoInMeasure_of_eq_off (P : Measure Ω) {f f' : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (B : ℕ → Set Ω) (hB : Tendsto (fun n => P (B n)) atTop (𝓝 0))
    (heq : ∀ n ω, ω ∉ B n → f' n ω = f n ω) (hf : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P f' atTop g := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (hf ε hε).add hB) (fun n => zero_le) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_cases hωB : ω ∈ B n
  · exact Or.inr hωB
  · left
    simp only [mem_ofPred_eq] at hω ⊢
    rwa [heq n ω hωB] at hω

end McLeishCLT.MDA.Thm23Proof

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
  McLeishCLT.MDA McLeishCLT.MDA.Thm23Proof
open scoped ENNReal NNReal

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X)
    (ha : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, eLpNorm (maxAbs k X n) 2 P ≤ C)
    (hb : TendstoInMeasure P (fun n => maxAbs k X n) atTop (fun _ => 0))
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1)) :
    TendstoInDistribution (fun n => S k X n) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  -- The bad event where truncation changes some entry; its probability tends to `0` by (2.5).
  set B : ℕ → Set Ω := fun n => {ω | ∃ j < k n, trunc X n j ω ≠ X n j ω} with hBdef
  have h25 := eq_2_5 P k X hc
  have hB : Tendsto (fun n => P (B n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h25.2 (fun _ => zero_le) h25.1
  have hoff : ∀ n ω, ω ∉ B n → ∀ j < k n, trunc X n j ω = X n j ω := by
    intro n ω hω j hj
    by_contra hne
    exact hω ⟨j, hj, hne⟩
  -- Hypotheses of Theorem (2.1) for the truncated array.
  have hZmda := trunc_isMDA P ℱ k X hmda
  have hZm : ∀ n, ∀ j < k n, Measurable (trunc X n j) := fun n j hj =>
    ((hZmda n j hj).1.mono ((ℱ n).le (j + 1))).measurable
  have hZa : ∀ t : ℝ, Tendsto (fun n => ∫ ω, prodT k (trunc X) t n ω ∂P) atTop (𝓝 1) := by
    intro t
    have : (fun n => ∫ ω, prodT k (trunc X) t n ω ∂P) = fun _ => (1 : ℂ) := by
      funext n
      exact trunc_integral_prodT_eq_one P ℱ k X hmda t n
    rw [this]
    exact tendsto_const_nhds
  have hZb := trunc_prodT_uniformIntegrable P ℱ k X hmda ha
  have hZc : TendstoInMeasure P (fun n => sumSq k (trunc X) n) atTop (fun _ => 1) := by
    refine tendstoInMeasure_of_eq_off P B hB (fun n ω hω => ?_) hc
    unfold sumSq
    exact Finset.sum_congr rfl fun j hj => by rw [hoff n ω hω j (Finset.mem_range.mp hj)]
  have hZd : TendstoInMeasure P (fun n => maxAbs k (trunc X) n) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_eq_off P B hB (fun n ω hω => ?_) hb
    unfold maxAbs
    exact iSup_congr fun j => by rw [hoff n ω hω j j.2]
  have hZ := theorem_2_1 P k (trunc X) hZm hZa hZb hZc hZd
  -- `S_n(X) - S_n(Z) → 0` in probability.
  have hXm : ∀ n, ∀ j < k n, Measurable (X n j) := fun n j hj =>
    ((hmda n j hj).1.mono ((ℱ n).le (j + 1))).measurable
  have hSm : ∀ n, AEMeasurable (S k X n) P := fun n => by
    unfold S
    exact (Finset.measurable_sum _ fun j hj => hXm n j (Finset.mem_range.mp hj)).aemeasurable
  have hdiff : TendstoInMeasure P ((fun n => S k X n) - fun n => S k (trunc X) n) atTop 0 := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun n => zero_le)
      (fun n => measure_mono fun ω hω => ?_)
    by_contra hωB
    have hS : S k X n ω = S k (trunc X) n ω := by
      unfold S
      exact Finset.sum_congr rfl fun j hj => by rw [hoff n ω hωB j (Finset.mem_range.mp hj)]
    simp only [mem_ofPred_eq, Pi.sub_apply, hS, sub_self, Pi.zero_apply, dist_self] at hω
    linarith
  exact tendstoInDistribution_of_tendstoInMeasure_sub (fun n => S k X n) id hZ hdiff hSm
