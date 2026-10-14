-- Prove2me | solution 1 for NagaevLD.FukNagaev.cond_1_4_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:47:03.229119+00:00
-- url     : https://prove2.me/submissions/bcf211e0-fe9e-4613-b28f-d410e2d340d6

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting



namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem fn_eq_1_8_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (x : ℝ) (yv : Fin n → ℝ) :
    P.real {ω | x ≤ S n X ω} ≤
      P.real {ω | x ≤ St X yv ω} + ∑ i, P.real {ω | yv i < X i ω} := by
  have hsub : {ω | x ≤ S n X ω} ⊆ {ω | x ≤ St X yv ω} ∪ ⋃ i, {ω | yv i < X i ω} := by
    intro ω hω
    by_cases hall : ∀ i, X i ω ≤ yv i
    · left
      have : St X yv ω = S n X ω := by
        unfold St S Xt
        exact Finset.sum_congr rfl (fun i _ => if_pos (hall i))
      simp only [Set.mem_setOf_eq] at hω ⊢; rw [this]; exact hω
    · right
      push_neg at hall
      obtain ⟨i, hi⟩ := hall
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  calc P.real {ω | x ≤ S n X ω}
      ≤ P.real ({ω | x ≤ St X yv ω} ∪ ⋃ i, {ω | yv i < X i ω}) := measureReal_mono hsub
    _ ≤ P.real {ω | x ≤ St X yv ω} + P.real (⋃ i, {ω | yv i < X i ω}) :=
        measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (measureReal_iUnion_fintype_le _)

lemma Xt_le {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (i : Fin n) (ω : Ω) : Xt X yv i ω ≤ yv i := by
  unfold Xt; split_ifs with h
  · exact h
  · exact (hyv i).le

lemma Xt_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (yv : Fin n → ℝ) (i : Fin n) : Measurable (Xt X yv i) := by
  unfold Xt
  exact Measurable.ite (measurableSet_le (hmeas i) measurable_const) (hmeas i) measurable_const

lemma Xt_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (X : Fin n → Ω → ℝ) (hindep : iIndepFun X P) (yv : Fin n → ℝ) :
    iIndepFun (fun i => Xt X yv i) P := by
  have := hindep.comp (fun i (u : ℝ) => if u ≤ yv i then u else 0)
    (fun i => Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_id
      measurable_const)
  exact this

lemma exp_Xt_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (yv : Fin n → ℝ)
    (hyv : ∀ i, 0 < yv i) (h : ℝ) (hh : 0 ≤ h) (i : Fin n) :
    Integrable (fun ω => Real.exp (h * Xt X yv i ω)) P := by
  refine Integrable.of_bound (C := Real.exp (h * yv i))
    (((Xt_measurable X hmeas yv i).const_mul h).exp.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_left (Xt_le X yv hyv i ω) hh

theorem fn_eq_1_9_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (h : ℝ) (hh : 0 < h) :
    P.real {ω | x ≤ St X yv ω} ≤ Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P ∧
      Real.exp (-h * x) * ∫ ω, Real.exp (h * St X yv ω) ∂P =
        Real.exp (-h * x) * ∏ i, ∫ ω, Real.exp (h * Xt X yv i ω) ∂P := by
  have hS : (fun ω => St X yv ω) = ∑ i, Xt X yv i := by
    funext ω; simp [St, Finset.sum_apply]
  have hXm := Xt_measurable X hmeas yv
  have hind := Xt_indep P X hindep yv
  have hI := hind.integrable_exp_mul_sum (t := h) hXm (s := Finset.univ)
    (fun i _ => exp_Xt_integrable P X hmeas yv hyv h hh.le i)
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ i, Xt X yv i) x hh.le hI
  have h2 := hind.mgf_sum hXm (t := h) Finset.univ
  have e : {ω | x ≤ St X yv ω} = {ω | x ≤ (∑ i, Xt X yv i) ω} := by rw [← hS]
  have e2 : ∫ ω, Real.exp (h * St X yv ω) ∂P = mgf (∑ i, Xt X yv i) P h := by
    rw [mgf]; congr 1; funext ω; rw [← hS]
  refine ⟨?_, ?_⟩
  · rw [e, e2]; exact h1
  · rw [e2, h2]; rfl

theorem fn_cond_1_4_iff_core (t : ℝ) (ht : 2 ≤ t) (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : β = 1 - α) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy0 : 0 < y) (B A : ℝ) (hB : 0 < B)
    (hA : 0 < A) :
    cond_1_4 t α β x y B A ↔
      α * x / (Real.exp t * B) ≤
        max (t / y) (1 / y * Real.log (β * x * y ^ (t - 1) / A + 1)) := by
  unfold cond_1_4
  have hA' : A ≠ 0 := hA.ne'
  have e : max (t / y) (1 / y * Real.log (β * x * y ^ (t - 1) / A + 1)) =
      max t (Real.log (β * x * y ^ (t - 1) / A + 1)) / y := by
    rw [show 1 / y * Real.log (β * x * y ^ (t - 1) / A + 1) = Real.log (β * x * y ^ (t - 1) / A + 1) / y by ring]
    exact max_div_div_right hy0.le _ _
  rw [e, le_div_iff₀ hy0]
  have e2 : α * x * y / (Real.exp t * B) = α * x / (Real.exp t * B) * y := by ring
  rw [e2]
  constructor
  · rintro (h | h)
    · exact absurd h hA'
    · exact h
  · intro h; exact Or.inr h

end NagaevLD.FukNagaev

open NagaevLD.FukNagaev


theorem solution (t : ℝ) (ht : 2 ≤ t) (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : β = 1 - α) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy0 : 0 < y) (B A : ℝ) (hB : 0 < B)
    (hA : 0 < A) :
    cond_1_4 t α β x y B A ↔
      α * x / (Real.exp t * B) ≤
        max (t / y) (1 / y * Real.log (β * x * y ^ (t - 1) / A + 1)) := by
  exact fn_cond_1_4_iff_core t ht α β hα0 hα1 hβ x hx y hy0 B A hB hA
