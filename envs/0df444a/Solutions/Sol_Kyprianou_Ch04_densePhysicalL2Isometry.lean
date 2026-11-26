-- Prove2me | solution 1 for Kyprianou.Ch04.densePhysicalL2Isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:26:57.17593+00:00
-- url     : https://prove2.me/submissions/40e2f40d-409d-4cfa-acc3-ffd71f7058da

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_physicalL1BoundCongrAE
import Theorems.Thm_Kyprianou_Ch04_kernelL2ConvergenceAbsoluteL1
import Theorems.Thm_Kyprianou_Ch04_physicalL2LimitTransfer
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Extend a physical square-integral identity from a dense L2 submodule. -/
theorem solution
    {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) [IsFiniteMeasure mu] (P : Measure Omega)
    (T : (A → ℝ) → Omega → ℝ)
    (hT : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu →
      Integrable (T f) P ∧ Integrable (T g) P ∧
        (∫ w, |T f w - T g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu)
    (hSub : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu → T (f - g) =ᵐ[P] T f - T g)
    (R : Submodule ℝ (Lp ℝ 2 mu))
    (hDense : ∀ v : Lp ℝ 2 mu, v ∈ R.topologicalClosure)
    (hSq : ∀ v : Lp ℝ 2 mu, v ∈ R →
      Integrable (fun w => (T (v : A → ℝ) w)^2) P ∧
      (∫ w, (T (v : A → ℝ) w)^2 ∂P) = ∫ a, (v a)^2 ∂mu)
    (g : A → ℝ) (hgm : Measurable g) (hg : MemLp g 2 mu) :
    MemLp (T g) 2 P ∧ (∫ w, (T g w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  have hgi := hg.integrable (by norm_num)
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp (hDense (hg.toLp g))
  let f : ℕ → A → ℝ := fun n => v n
  have hf (n : ℕ) : MemLp (f n) 2 mu := Lp.memLp (v n)
  have hm (n : ℕ) : Measurable (f n) := (Lp.stronglyMeasurable (v n)).measurable
  have hfi (n : ℕ) : Integrable (f n) mu := (hf n).integrable (by norm_num)
  have hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
    change Tendsto (fun n => (hf n).toLp (v n : A → ℝ)) atTop (𝓝 (hg.toLp g))
    simpa only [Lp.toLp_coeFn] using hlim
  have hTi (n : ℕ) := hT (f n) g (hm n) hgm (hfi n) hgi
  have hX (n : ℕ) : MemLp (T (f n)) 2 P :=
    (memLp_two_iff_integrable_sq (hTi n).1.aestronglyMeasurable).2 (hSq (v n) (hv n)).1
  have hL1 : Tendsto (fun n => ∫ w, |T (f n) w - T g w| ∂P) atTop (𝓝 0) := by
    have h1 := Kyprianou.Ch04.kernelL2ConvergenceAbsoluteL1 mu f g hf hg hfg
    have h2 := h1.const_mul (2 : ℝ)
    rw [mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => (hTi n).2.2)
  have hDiff (n m : ℕ) : (∫ w, (T (f n) w - T (f m) w)^2 ∂P) =
      ∫ a, (f n a - f m a)^2 ∂mu := by
    let u := v n - v m
    have hu : u ∈ R := R.sub_mem (hv n) (hv m)
    have he : (u : A → ℝ) =ᵐ[mu] f n - f m := Lp.coeFn_sub (v n) (v m)
    have hU := hT (u : A → ℝ) (f n - f m) (Lp.stronglyMeasurable u).measurable
      ((hm n).sub (hm m)) ((Lp.memLp u).integrable (by norm_num)) ((hfi n).sub (hfi m))
    have hcon := Kyprianou.Ch04.physicalL1BoundCongrAE mu P _ _ _ _ he hU.1 hU.2.1 hU.2.2
    have hsub := hcon.trans (hSub (f n) (f m) (hm n) (hm m) (hfi n) (hfi m))
    have hsq1 : (fun w => (T (u : A → ℝ) w)^2) =ᵐ[P]
        fun w => (T (f n) w - T (f m) w)^2 := hsub.fun_comp (fun x : ℝ => x^2)
    have hsq2 : (fun a => (u a)^2) =ᵐ[mu] fun a => (f n a - f m a)^2 :=
      he.fun_comp (fun x : ℝ => x^2)
    rw [← integral_congr_ae hsq1, (hSq u hu).2, integral_congr_ae hsq2]
  exact Kyprianou.Ch04.physicalL2LimitTransfer mu P f g (fun n => T (f n)) (T g)
    hf hg hX (fun n => (hTi n).1) (hTi 0).2.1 hfg hL1
    (fun n => (hSq (v n) (hv n)).2) hDiff
