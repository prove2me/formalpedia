-- Prove2me | solution 1 for KSATSingleFlip.Connect.independent_poisson_mixture_mean
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:56:29.338224+00:00
-- url     : https://prove2.me/submissions/e7f51484-c537-4caa-b659-cb7519accc67

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (r : ℝ≥0) (hNlaw : Measure.map N P = poissonMeasure r)
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : ∀ j, IndepFun N (X j) P)
    (hYint : Integrable (fun ω => X (N ω) ω) P)
    (hgint : Integrable (fun j => ∫ ω, X j ω ∂P) (poissonMeasure r)) :
    (∫ ω, X (N ω) ω ∂P) = ∫ j, (∫ ω, X j ω ∂P) ∂(poissonMeasure r) := by
  classical
  let Y : Ω → ℝ := fun ω => X (N ω) ω
  let C : ℕ → Set Ω := fun j => N ⁻¹' {j}
  let g : ℕ → ℝ := fun j => ∫ ω, X j ω ∂P
  have hm (j : ℕ) : MeasurableSet (C j) := (measurableSet_singleton j).preimage hN
  have hd : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have hi' : N ω = i := hi
    have hj' : N ω = j := hj
    exact hij (hi'.symm.trans hj')
  have hu : (⋃ j, C j) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, C, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨N ω, rfl⟩
  have hpart : (∫ ω, Y ω ∂P) = ∑' j, ∫ ω in C j, Y ω ∂P := by
    have h := integral_iUnion hm hd (show IntegrableOn Y (⋃ j, C j) P by simpa [hu, Y] using hYint)
    simpa [hu] using h
  have hcell (j : ℕ) : (∫ ω in C j, Y ω ∂P) = (poissonMeasure r).real {j} * g j := by
    have heq : (∫ ω in C j, Y ω ∂P) = ∫ ω in C j, X j ω ∂P := by
      apply setIntegral_congr_fun (hm j)
      intro ω hω
      have hNj : N ω = j := hω
      simp [Y,hNj]
    rw [heq, ← integral_indicator (hm j)]
    let ind : ℕ → ℝ := ({j} : Set ℕ).indicator 1
    have hi : Measurable ind := measurable_const.indicator (measurableSet_singleton j)
    have hi' : AEStronglyMeasurable ind (Measure.map N P) := hi.aestronglyMeasurable
    have hprod := (hind j).integral_fun_comp_mul_comp hN.aemeasurable (hX j).aemeasurable hi'
      (measurable_id.aestronglyMeasurable : AEStronglyMeasurable (fun z : ℝ => z) (Measure.map (X j) P))
    have heqfun : (fun ω => (C j).indicator (X j) ω) = fun ω => ind (N ω)*X j ω := by
      funext ω
      by_cases h : N ω = j <;> simp [C, ind, Set.indicator_apply, h]
    simp only [id_eq] at hprod
    rw [heqfun, hprod]
    have hindreal : (∫ ω, ind (N ω) ∂P) = (poissonMeasure r).real {j} := by
      have hh : (fun ω => ind (N ω)) = (C j).indicator 1 := by
        funext ω
        by_cases h : N ω = j <;> simp [C, ind, Set.indicator_apply, h]
      rw [hh, integral_indicator_one (hm j)]
      simp only [measureReal_def, ← hNlaw, Measure.map_apply hN (measurableSet_singleton j)]
      rfl
    rw [hindreal]
  rw [hpart]
  simp_rw [hcell]
  rw [integral_countable hgint]
  simp [g, smul_eq_mul]
