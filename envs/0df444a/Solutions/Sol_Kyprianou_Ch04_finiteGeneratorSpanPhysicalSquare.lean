-- Prove2me | solution 1 for Kyprianou.Ch04.finiteGeneratorSpanPhysicalSquare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:26:52.960497+00:00
-- url     : https://prove2.me/submissions/3f6c0d92-4a16-4dd1-97af-4c060d4d6154

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_physicalL1BoundCongrAE
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false

/-- Physical square identities pass from pointwise generator sums to their L2 classes. -/
theorem solution
    {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) [IsFiniteMeasure mu] (P : Measure Omega)
    (G : Set (Set A)) (T : (A → ℝ) → Omega → ℝ)
    (hT : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu →
      Integrable (T f) P ∧ Integrable (T g) P ∧
        (∫ w, |T f w - T g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu)
    (hSimple : ∀ (k : ℕ) (D : Fin k → Set A) (c : Fin k → ℝ),
      (∀ i, D i ∈ G) →
      let f : A → ℝ := fun a => ∑ i, c i * (D i).indicator (fun _ => (1 : ℝ)) a
      Measurable f → MemLp f 2 mu →
      Integrable (fun w => (T f w)^2) P ∧
        (∫ w, (T f w)^2 ∂P) = ∫ a, (f a)^2 ∂mu)
    (v : Lp ℝ 2 mu)
    (hv : v ∈ Submodule.span ℝ
      {w : Lp ℝ 2 mu | ∃ (B : Set A), B ∈ G ∧
        ∃ (hB : MeasurableSet B) (hfin : mu B ≠ ⊤),
          indicatorConstLp 2 hB hfin (1 : ℝ) = w}) :
    Integrable (fun w => (T (v : A → ℝ) w)^2) P ∧
      (∫ w, (T (v : A → ℝ) w)^2 ∂P) = ∫ a, (v a)^2 ∂mu := by
  classical
  let S : Set (Lp ℝ 2 mu) :=
    {w | ∃ (B : Set A), B ∈ G ∧
      ∃ (hB : MeasurableSet B) (hfin : mu B ≠ ⊤),
        indicatorConstLp 2 hB hfin (1 : ℝ) = w}
  change v ∈ Submodule.span ℝ S at hv
  obtain ⟨k, c, g, heq⟩ := Submodule.mem_span_set'.mp hv
  have hg (i : Fin k) : ∃ B : Set A, B ∈ G ∧
      ∃ (hB : MeasurableSet B) (hfin : mu B ≠ ⊤),
        indicatorConstLp 2 hB hfin (1 : ℝ) = (g i : Lp ℝ 2 mu) := (g i).property
  choose D hDG hDm hDfin hgi using hg
  let f : A → ℝ := fun a => ∑ i, c i * (D i).indicator (fun _ => (1 : ℝ)) a
  have hco (i : Fin k) : ((g i : Lp ℝ 2 mu) : A → ℝ) =ᵐ[mu]
      (D i).indicator (fun _ => (1 : ℝ)) := by
    rw [← hgi i]
    exact indicatorConstLp_coeFn
  have hs (i : Fin k) :
      ((c i • (g i : Lp ℝ 2 mu) : Lp ℝ 2 mu) : A → ℝ) =ᵐ[mu]
        fun a => c i * (D i).indicator (fun _ => (1 : ℝ)) a := by
    filter_upwards [Lp.coeFn_smul (c i) (g i : Lp ℝ 2 mu), hco i] with a ha hb
    simpa [Pi.smul_apply, smul_eq_mul, hb] using ha
  have he : (v : A → ℝ) =ᵐ[mu] f := by
    rw [← heq]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => c i • (g i : Lp ℝ 2 mu)),
      ae_all_iff.mpr hs] with a ha hb
    rw [ha, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hb i
  have hfm : Measurable f := by
    apply Finset.measurable_sum
    intro i hi
    exact measurable_const.mul (measurable_const.indicator (hDm i))
  have hflp := (memLp_congr_ae he).1 (Lp.memLp v)
  have h := hSimple k D c hDG hfm hflp
  have hT' := hT (v : A → ℝ) f (Lp.stronglyMeasurable v).measurable hfm
    ((Lp.memLp v).integrable (by norm_num)) (hflp.integrable (by norm_num))
  have hEq := Kyprianou.Ch04.physicalL1BoundCongrAE mu P _ _ _ _ he hT'.1 hT'.2.1 hT'.2.2
  have hsq1 : (fun w => (T (v : A → ℝ) w)^2) =ᵐ[P] fun w => (T f w)^2 :=
    hEq.fun_comp (fun x : ℝ => x^2)
  have hsq2 : (fun a => (v a)^2) =ᵐ[mu] fun a => (f a)^2 :=
    he.fun_comp (fun x : ℝ => x^2)
  exact ⟨h.1.congr hsq1.symm, (integral_congr_ae hsq1).trans
    (h.2.trans (integral_congr_ae hsq2).symm)⟩
