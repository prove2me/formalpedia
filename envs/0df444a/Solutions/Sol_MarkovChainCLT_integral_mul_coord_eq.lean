-- Prove2me | solution 1 for MarkovChainCLT.integral_mul_coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:26:24.595118+00:00
-- url     : https://prove2.me/submissions/197d4fb5-f53a-47d4-82e9-9baf4d6d66e4

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_condExp_coord_add
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br) (j d : ℕ) :
    ∫ ω, r (ω (j + 1)) * r (ω (j + 1 + d)) ∂(chainMeasure P π)
      = ∫ x, r x * (∫ y, r y ∂(iterKernel P d x)) ∂π := by
  classical
  set ν : Measure (ℕ → X) := chainMeasure P π with hν
  set Q : X → ℝ := fun x => ∫ y, r y ∂(iterKernel P d x) with hQ
  have hQm : Measurable Q :=
    (hr.stronglyMeasurable.integral_kernel (κ := iterKernel P d)).measurable
  have hQB : ∀ x, |Q x| ≤ Br := by
    intro x
    rw [hQ]
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun z => |r z|) (iterKernel P d x) :=
      ⟨(continuous_abs.measurable.comp hr).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := Br) (ae_of_all _ (fun z => by simpa using hBr z))⟩
    have h2 := integral_mono h1 (integrable_const Br) (fun z => hBr z)
    simpa using h2
  have hmle : MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance
      ≤ (inferInstance : MeasurableSpace (ℕ → X)) := (measurable_frestrictLe (j + 1)).comap_le
  haveI : IsFiniteMeasure (ν.trim hmle) := isFiniteMeasure_trim hmle
  have hcoordm : Measurable[MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]
      (fun ω : ℕ → X => ω (j + 1)) := by
    have h1 : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) (j + 1)) := Measurable.of_comap_le le_rfl
    have h2 := (measurable_pi_apply
      (⟨j + 1, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic (j + 1))).comp h1
    exact h2
  have hsmr : StronglyMeasurable[MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]
      (fun ω : ℕ → X => r (ω (j + 1))) := by
    have hx := hr.comp hcoordm
    exact hx.stronglyMeasurable
  have hint2 : Integrable (fun ω : ℕ → X => r (ω (j + 1 + d))) ν :=
    ⟨(hr.comp (measurable_pi_apply (j + 1 + d))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := Br) (ae_of_all _ (fun ω => by simpa using hBr _))⟩
  have hintprod : Integrable
      (fun ω : ℕ → X => r (ω (j + 1)) * r (ω (j + 1 + d))) ν := by
    refine ⟨((hr.comp (measurable_pi_apply (j + 1))).mul
      (hr.comp (measurable_pi_apply (j + 1 + d)))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun ω => ?_))⟩
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hBr (ω (j + 1)), hBr (ω (j + 1 + d)),
      abs_nonneg (r (ω (j + 1))), abs_nonneg (r (ω (j + 1 + d)))]
  -- the Markov property at lag `d`
  have hce := condExp_coord_add P π r hr Br hBr (j + 1) d
  have hpull : ν[fun ω : ℕ → X => r (ω (j + 1)) * r (ω (j + 1 + d)) | MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]
      =ᵐ[ν] (fun ω : ℕ → X => r (ω (j + 1))) *
        ν[fun ω : ℕ → X => r (ω (j + 1 + d)) | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance] :=
    condExp_mul_of_stronglyMeasurable_left hsmr hintprod hint2
  have hfin : (fun ω : ℕ → X => r (ω (j + 1)) *
      (ν[fun ω : ℕ → X => r (ω (j + 1 + d)) | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]) ω)
      =ᵐ[ν] fun ω : ℕ → X => r (ω (j + 1)) * Q (ω (j + 1)) := by
    filter_upwards [hce] with ω e
    rw [← e]
  -- integrate and pass to the coordinate law
  have hstep : ∫ ω, r (ω (j + 1)) * r (ω (j + 1 + d)) ∂ν
      = ∫ ω, r (ω (j + 1)) * Q (ω (j + 1)) ∂ν := by
    calc ∫ ω, r (ω (j + 1)) * r (ω (j + 1 + d)) ∂ν
        = ∫ ω, (ν[fun ω : ℕ → X => r (ω (j + 1)) * r (ω (j + 1 + d)) | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]) ω ∂ν :=
          (integral_condExp hmle).symm
      _ = ∫ ω, r (ω (j + 1)) *
            (ν[fun ω : ℕ → X => r (ω (j + 1 + d)) | MeasurableSpace.comap
              (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]) ω ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hpull] with ω e
          rw [e]
          rfl
      _ = ∫ ω, r (ω (j + 1)) * Q (ω (j + 1)) ∂ν := integral_congr_ae hfin
  rw [hstep]
  have hmap := map_coord_chainMeasure P π hinv (j + 1)
  have hfm : StronglyMeasurable (fun x : X => r x * Q x) := (hr.mul hQm).stronglyMeasurable
  have := integral_map (μ := ν) (φ := fun ω : ℕ → X => ω (j + 1))
    (f := fun x : X => r x * Q x) (measurable_pi_apply (j + 1)).aemeasurable
    hfm.aestronglyMeasurable
  rw [hmap] at this
  rw [← this]
