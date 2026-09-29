-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_iterKernel_geom_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:22:42.700533+00:00
-- url     : https://prove2.me/submissions/4545a1b2-e070-4008-9b25-005cd2a86bda

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_condExp_coord_add
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_pow_le
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 4000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br)
    (hmean : ∫ x, r x ∂π = 0) (d : ℕ) :
    ∫ x, (∫ y, r y ∂(iterKernel P d x)) ^ 2 ∂π
      ≤ (1 / 4 : ℝ) ^ (d / N) * ∫ x, (r x) ^ 2 ∂π := by
  classical
  set ν : Measure (ℕ → X) := chainMeasure P π with hν
  set S : ℝ := ∫ x, (r x) ^ 2 ∂π with hS
  have hS0 : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  set Q : ℕ → X → ℝ := fun d x => ∫ y, r y ∂(iterKernel P d x) with hQ
  have hQm : ∀ d, Measurable (Q d) :=
    fun d => (hr.stronglyMeasurable.integral_kernel (κ := iterKernel P d)).measurable
  have hQB : ∀ d x, |Q d x| ≤ Br := by
    intro d x
    rw [hQ]
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun z => |r z|) (iterKernel P d x) :=
      ⟨(continuous_abs.measurable.comp hr).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := Br) (ae_of_all _ (fun z => by simpa using hBr z))⟩
    have h2 := integral_mono h1 (integrable_const Br) (fun z => hBr z)
    simpa using h2
  have hrint : Integrable r π :=
    ⟨hr.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := Br) (ae_of_all _ (fun z => by simpa using hBr z))⟩
  have hr2int : Integrable (fun x => (r x) ^ 2) π :=
    ⟨(hr.pow_const 2).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hBr z, abs_nonneg (r z), sq_abs (r z)]))⟩
  have hQint : ∀ d, Integrable (Q d) π :=
    fun d => ⟨(hQm d).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := Br) (ae_of_all _ (fun z => by simpa using hQB d z))⟩
  have hQ2int : ∀ d, Integrable (fun x => (Q d x) ^ 2) π :=
    fun d => ⟨((hQm d).pow_const 2).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hQB d z, abs_nonneg (Q d z), sq_abs (Q d z)]))⟩
  -- invariance for all powers, and the semigroup identity
  have hinvN : ∀ m : ℕ, (iterKernel P m) ∘ₘ π = π := by
    intro m
    induction m with
    | zero => rw [iterKernel_zero]; simp
    | succ k ih => rw [iterKernel_succ, ← Measure.comp_assoc, ih, hinv]
  have hadd : ∀ a b : ℕ, iterKernel P (a + b) = iterKernel P a ∘ₖ iterKernel P b := by
    intro a b
    induction a with
    | zero => rw [Nat.zero_add, iterKernel_zero, Kernel.id_comp]
    | succ c ih =>
        have h1 : c + 1 + b = (c + b) + 1 := by omega
        rw [h1, iterKernel_succ, ih, ← Kernel.comp_assoc, ← iterKernel_succ]
  have hQmean : ∀ d, ∫ x, Q d x ∂π = 0 := by
    intro d
    have hcomp : (iterKernel P d) ∘ₘ π = ((iterKernel P d) ∘ₖ Kernel.const Unit π) () :=
      Measure.comp_eq_comp_const_apply
    have hint : Integrable r (((iterKernel P d) ∘ₖ Kernel.const Unit π) ()) := by
      rw [← hcomp, hinvN d]; exact hrint
    have h1 : ∫ y, r y ∂((iterKernel P d) ∘ₘ π) = ∫ x, Q d x ∂π := by
      rw [hcomp, Kernel.integral_comp hint]
      simp [hQ]
    rw [← h1, hinvN d, hmean]
  -- Jensen: applying the kernel does not increase the `L²` norm
  have hjen : ∀ (u : X → ℝ), Measurable u → (∀ x, |u x| ≤ Br) → ∀ b : ℕ,
      ∫ x, (∫ y, u y ∂(iterKernel P b x)) ^ 2 ∂π ≤ ∫ x, (u x) ^ 2 ∂π := by
    intro u hu huB b
    have hu2 : Integrable (fun x => (u x) ^ 2) π :=
      ⟨(hu.pow_const 2).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [huB z, abs_nonneg (u z), sq_abs (u z)]))⟩
    have hu1 : Integrable u π :=
      ⟨hu.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := Br) (ae_of_all _ (fun z => by simpa using huB z))⟩
    have hsqm : Integrable (fun y => (u y) ^ 2) ((iterKernel P b) ∘ₘ π) := by
      rw [hinvN b]; exact hu2
    have h1m : Integrable u ((iterKernel P b) ∘ₘ π) := by
      rw [hinvN b]; exact hu1
    have hA : Integrable (fun x => ∫ y, (u y) ^ 2 ∂(iterKernel P b x)) π := by
      have := Measure.integrable_integral_norm_of_integrable_comp
        (κ := iterKernel P b) (μ := π) (f := fun y => (u y) ^ 2) hsqm
      refine this.congr ?_
      filter_upwards with x
      refine integral_congr_ae (ae_of_all _ (fun y => ?_))
      simp only
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u y))]
    have hae : ∀ᵐ x ∂π, Integrable (fun y => (u y) ^ 2) ((iterKernel P b) x) :=
      Measure.ae_integrable_of_integrable_comp hsqm
    have haeu : ∀ᵐ x ∂π, Integrable u ((iterKernel P b) x) :=
      Measure.ae_integrable_of_integrable_comp h1m
    have hpt : ∀ᵐ x ∂π, (∫ y, u y ∂(iterKernel P b x)) ^ 2
        ≤ ∫ y, (u y) ^ 2 ∂(iterKernel P b x) := by
      filter_upwards [hae, haeu] with x hx hxu
      set c : ℝ := ∫ y, u y ∂(iterKernel P b x) with hc
      have hexp : ∫ y, (u y - c) ^ 2 ∂(iterKernel P b x)
          = (∫ y, (u y) ^ 2 ∂(iterKernel P b x)) - 2 * c * c + c ^ 2 := by
        have hev : ∀ y, (u y - c) ^ 2 = (u y) ^ 2 - 2 * c * u y + c ^ 2 := by intro y; ring
        rw [integral_congr_ae (ae_of_all _ hev)]
        have i2 : Integrable (fun y => 2 * c * u y) (iterKernel P b x) := hxu.const_mul (2 * c)
        have i1 : Integrable (fun y => (u y) ^ 2 - 2 * c * u y) (iterKernel P b x) := hx.sub i2
        rw [integral_add i1 (integrable_const (c ^ 2)), integral_sub hx i2,
          integral_const_mul, integral_const]
        simp [Measure.real, ← hc]
      have hnn : 0 ≤ ∫ y, (u y - c) ^ 2 ∂(iterKernel P b x) :=
        integral_nonneg (fun y => sq_nonneg _)
      rw [hexp] at hnn
      nlinarith [hnn]
    have hlhs : Integrable (fun x => (∫ y, u y ∂(iterKernel P b x)) ^ 2) π := by
      refine Integrable.mono' (g := fun x => ∫ y, (u y) ^ 2 ∂(iterKernel P b x)) hA ?_ ?_
      · exact ((hu.stronglyMeasurable.integral_kernel
          (κ := iterKernel P b)).measurable.pow_const 2).aestronglyMeasurable
      · filter_upwards [hpt] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hx
    have hmono := integral_mono_ae hlhs hA hpt
    have hAeq : ∫ x, (∫ y, (u y) ^ 2 ∂(iterKernel P b x)) ∂π = ∫ x, (u x) ^ 2 ∂π := by
      have hcomp : (iterKernel P b) ∘ₘ π = ((iterKernel P b) ∘ₖ Kernel.const Unit π) () :=
        Measure.comp_eq_comp_const_apply
      have hint : Integrable (fun y => (u y) ^ 2)
          (((iterKernel P b) ∘ₖ Kernel.const Unit π) ()) := by
        rw [← hcomp]; exact hsqm
      have h1 : ∫ y, (u y) ^ 2 ∂((iterKernel P b) ∘ₘ π)
          = ∫ x, (∫ y, (u y) ^ 2 ∂(iterKernel P b x)) ∂π := by
        rw [hcomp, Kernel.integral_comp hint]
        simp
      rw [← h1, hinvN b]
    rw [hAeq] at hmono
    exact hmono
  -- the geometric bound on `‖Q d‖₂²`
  show ∫ x, (Q d x) ^ 2 ∂π ≤ (1 / 4 : ℝ) ^ (d / N) * S
  · set q : ℕ := d / N with hq
    set sm : ℕ := d % N with hsm
    have hdq : q * N + sm = d := by
      rw [hq, hsm]
      exact Nat.div_add_mod' d N
    have hsplit : ∀ x : X, Q d x = ∫ y, Q (q * N) y ∂(iterKernel P sm x) := by
      intro x
      have hker : iterKernel P d = iterKernel P (q * N) ∘ₖ iterKernel P sm := by
        rw [← hdq, hadd]
      haveI : IsMarkovKernel (iterKernel P (q * N) ∘ₖ iterKernel P sm) :=
        Kernel.IsMarkovKernel.comp _ _
      have hint : Integrable r ((iterKernel P (q * N) ∘ₖ iterKernel P sm) x) :=
        ⟨hr.aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := Br)
            (ae_of_all _ (fun z => by simpa using hBr z))⟩
      show ∫ y, r y ∂(iterKernel P d x) = _
      rw [hker, Kernel.integral_comp hint]
    have h1 : ∫ x, (Q d x) ^ 2 ∂π
        = ∫ x, (∫ y, Q (q * N) y ∂(iterKernel P sm x)) ^ 2 ∂π := by
      refine integral_congr_ae (ae_of_all _ (fun x => ?_))
      simp only
      rw [hsplit x]
    rw [h1]
    refine le_trans (hjen (Q (q * N)) (hQm _) (hQB _) sm) ?_
    exact integral_sq_iterKernel_pow_le P π hinv N ρ hρ0 hρ hrate r hr hr2int hmean q
