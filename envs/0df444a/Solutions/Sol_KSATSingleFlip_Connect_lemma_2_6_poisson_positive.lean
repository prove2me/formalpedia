-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_6_poisson_positive
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:00:10.281787+00:00
-- url     : https://prove2.me/submissions/5293f224-eb20-42f4-8d42-52be0358ba7f

import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_poisson_from_fibers
import Theorems.Thm_KSATSingleFlip_Connect_independent_poisson_mixture_mean
import Theorems.Thm_KSATSingleFlip_Connect_fixed_count_independent_fiber
import Theorems.Thm_KSATSingleFlip_Connect_expected_count_step_bound
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure A) [IsProbabilityMeasure D]
    (N : Ω → ℕ) (hN : Measurable N) (r : ℝ≥0) (hr : 0 < r) (hNlaw : Measure.map N P = poissonMeasure r)
    (X : ℕ → Ω → A) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ j, Measure.map (fun ω (i : Fin j) => X i.val ω) P = Measure.pi (fun _ : Fin j => D))
    (hind : ∀ j, IndepFun N (fun ω (i : Fin j) => X i.val ω) P)
    (F : List A → ℝ) (hF : ∀ j, Measurable (fun x : Fin j → A => F (List.ofFn x)))
    (ν a L n : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (ha1 : a ≤ 1)
    (hL : 1 ≤ L) (hn : 0 < n) (hrν : (r:ℝ) = ν*n)
    (hsqrt : Real.sqrt (ν*n) ≤ a*n/(4*L))
    (hbound : ∀ xs, 0 ≤ F xs ∧ F xs ≤ n)
    (hins : ∀ (xs : List A) (i : ℕ) (z : A), |F (xs.insertIdx i z)-F xs| ≤ L) :
    P.real {ω | F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ≤
      (∫ ω, F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ∂P)-a*n} ≤
      3*Real.exp (-(a^2*n)/(128*(ν+1)*L^2)) := by
  classical
  let Q : ∀ j, Ω → (Fin j → A) := fun j ω i => X i.val ω
  let W : ℕ → Ω → ℝ := fun j ω => F (List.ofFn (Q j ω))
  let g : ℕ → ℝ := fun j => ∫ ω, W j ω ∂P
  let Y : Ω → ℝ := fun ω => W (N ω) ω
  have hQ (j : ℕ) : Measurable (Q j) := measurable_pi_iff.mpr (fun i => hX i.val)
  have hW (j : ℕ) : Measurable (W j) := (hF j).comp (hQ j)
  have hWint (j : ℕ) : Integrable (W j) P := by
    apply Integrable.of_bound (hW j).aestronglyMeasurable n
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]; exact (hbound _).2)
  have hY : Measurable Y := by
    have hprod : Measurable (fun z : ℕ × Ω => W z.1 z.2) := measurable_from_prod_countable_right hW
    exact hprod.comp (hN.prodMk measurable_id)
  have hYint : Integrable Y P := by
    apply Integrable.of_bound hY.aestronglyMeasurable n
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]; exact (hbound _).2)
  have hgint : Integrable g (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable g).aestronglyMeasurable n
    apply Filter.Eventually.of_forall
    intro j
    have hh := norm_integral_le_of_norm_le_const (μ := P) (f := W j)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]; exact (hbound _).2)
    simpa [g, measureReal_def] using hh
  have hindW (j : ℕ) : IndepFun N (W j) P := by
    simpa [W, Q, Function.comp_def] using (hind j).comp measurable_id (hF j)
  have hmean : (∫ ω, Y ω ∂P) = ∫ j, g j ∂(poissonMeasure r) := by
    exact KSATSingleFlip.Connect.independent_poisson_mixture_mean P N hN r hNlaw W hW hindW hYint hgint
  have hstep (j : ℕ) : |g (j+1)-g j| ≤ L := by
    exact KSATSingleFlip.Connect.expected_count_step_bound P X F L hins hWint j
  have hzero : ∀ ω, N ω = 0 → Y ω = g 0 := by
    intro ω hω
    have hQ0 (u : Ω) : W 0 u = F [] := by simp [W,Q]
    have hg0 : g 0 = F [] := by simp [g,hQ0, measureReal_def]
    simpa [Y,hω,hg0] using hQ0 ω
  have hfib : ∀ j : ℕ, 1 ≤ j →
      P ({ω | N ω = j} ∩ {ω | Y ω ≤ g j-a*n/2}) ≤
        P {ω | N ω = j} * ENNReal.ofReal (Real.exp (-(a*n)^2/(8*(j:ℝ)*L^2))) := by
    intro j hj
    have h := KSATSingleFlip.Connect.fixed_count_independent_fiber P D N j hj (Q j) (hQ j) (hlaw j) (hind j) F (hF j) L (a*n/2) hL (by positivity) hins
    have hgj : g j = ∫ x, F (List.ofFn x) ∂(Measure.pi (fun _ : Fin j => D)) := by
      rw [← hlaw j]
      exact (integral_map (hQ j).aemeasurable (hF j).aestronglyMeasurable).symm
    have hevent : {ω | N ω = j} ∩ {ω | Y ω ≤ g j-a*n/2} =
        {ω | N ω = j} ∩ {ω | F (List.ofFn (Q j ω)) ≤ g j-a*n/2} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor <;> rintro ⟨hj',hh⟩ <;> refine ⟨hj', ?_⟩ <;> simpa [Y,hj'] using hh
    rw [hevent, hgj]
    convert h using 1 <;> congr 2 <;> ring
  have hh := KSATSingleFlip.Connect.lemma_2_6_poisson_from_fibers P N hN Y hY r hr hNlaw
    ν a L n hν ha ha1 hL hn hrν hsqrt g hgint hstep hzero hfib
  simpa only [← hmean, Y, W, Q] using hh
