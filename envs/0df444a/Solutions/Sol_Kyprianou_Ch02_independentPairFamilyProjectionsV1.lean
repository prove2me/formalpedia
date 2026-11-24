-- Prove2me | solution 1 for Kyprianou.Ch02.independentPairFamilyProjectionsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:29:22.264674+00:00
-- url     : https://prove2.me/submissions/b193fdf6-7002-4ba1-939e-1a83c117a12a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (a b : Fin n → Ω → ℝ)
    (ha : ∀ i, AEMeasurable (a i) P) (hb : ∀ i, AEMeasurable (b i) P)
    (hi : iIndepFun (fun i ω => (a i ω,b i ω)) P)
    (hc : ∀ i, IndepFun (a i) (b i) P) :
    IndepFun (fun ω i => a i ω) (fun ω i => b i ω) P := by
  apply pi_indepFun_pi_of_prod_bcf ha hb
  intro f g
  let H (i : Fin n) (p : ℝ × ℝ) := f i p.1 * g i p.2
  have hH (i : Fin n) : Measurable (H i) :=
    ((f i).continuous.measurable.comp measurable_fst).mul
      ((g i).continuous.measurable.comp measurable_snd)
  have hpair := hi.integral_fun_prod_comp
    (fun i => (ha i).prodMk (hb i)) (fun i => (hH i).aestronglyMeasurable)
  have h1 := (hi.comp (fun _ : Fin n => Prod.fst : Fin n → ℝ × ℝ → ℝ) (fun _ => measurable_fst)).integral_fun_prod_comp
    ha (fun i => (f i).continuous.measurable.aestronglyMeasurable)
  have h2 := (hi.comp (fun _ : Fin n => Prod.snd : Fin n → ℝ × ℝ → ℝ) (fun _ => measurable_snd)).integral_fun_prod_comp
    hb (fun i => (g i).continuous.measurable.aestronglyMeasurable)
  simp only [Pi.mul_apply, Finset.prod_apply, Function.comp_apply]
  simp only [← Finset.prod_mul_distrib]
  change (∫ ω, ∏ i, H i (a i ω, b i ω) ∂P) = _
  rw [hpair]
  change _ = (∫ ω, ∏ i, f i (a i ω) ∂P) * (∫ ω, ∏ i, g i (b i ω) ∂P)
  simp only [Function.comp_apply] at h1 h2
  rw [h1, h2, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (hc i).integral_fun_comp_mul_comp (ha i) (hb i)
    (f i).continuous.measurable.aestronglyMeasurable
    (g i).continuous.measurable.aestronglyMeasurable
