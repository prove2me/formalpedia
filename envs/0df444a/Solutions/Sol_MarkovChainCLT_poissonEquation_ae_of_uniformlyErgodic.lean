-- Prove2me | solution 1 for MarkovChainCLT.poissonEquation_ae_of_uniformlyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:13:17.232053+00:00
-- url     : https://prove2.me/submissions/81ad17e1-9084-46cf-9f15-32cb2b9cc349

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MarkovIterKernel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section KernelL2

variable {X : Type*} [MeasurableSpace X]

theorem KernelL2.integral_sq_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h1 : Integrable f μ := hf.integrable (by norm_num)
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  let m := ∫ x, f x ∂μ
  have hnonneg : 0 ≤ ∫ x, (f x - m) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq : (fun x => (f x - m) ^ 2) =
      (fun x => f x ^ 2 - (2 * m) * f x + m ^ 2) := by
    funext x
    ring
  rw [heq] at hnonneg
  rw [integral_add (f := fun x => f x ^ 2 - (2 * m) * f x)
      (g := fun _ => m ^ 2) (h2.sub (h1.const_mul (2 * m))) (integrable_const _),
    integral_sub (f := fun x => f x ^ 2) (g := fun x => (2 * m) * f x)
      h2 (h1.const_mul (2 * m)), integral_const_mul, integral_const] at hnonneg
  simp only [probReal_univ, smul_eq_mul, one_mul] at hnonneg
  dsimp [m] at hnonneg
  nlinarith

theorem KernelL2.ae_integrable (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f : X → ℝ} (hf : Integrable f π) : ∀ᵐ x ∂π, Integrable f (P x) := by
  change P ∘ₘ π = π at hinv
  apply Measure.ae_integrable_of_integrable_comp
  simpa only [hinv] using hf

theorem KernelL2.integral_invariant (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f : X → ℝ} (hf : Integrable f π) :
    (∫ x, ∫ y, f y ∂P x ∂π) = ∫ x, f x ∂π := by
  change P ∘ₘ π = π at hinv
  have hcomp : Integrable f ((P ∘ₖ Kernel.const Unit π) ()) := by
    simpa only [← Measure.comp_eq_comp_const_apply, hinv] using hf
  simpa only [← Measure.comp_eq_comp_const_apply, hinv, Kernel.const_apply] using
    (Kernel.integral_comp hcomp).symm

theorem KernelL2.kernel_memLp_and_sq_bound (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : X → ℝ) (hf : Measurable f) (h2 : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f y ∂P x) 2 π ∧
      (∫ x, (∫ y, f y ∂P x) ^ 2 ∂π) ≤ ∫ x, f x ^ 2 ∂π := by
  have hmeas : Measurable (fun x => ∫ y, f y ∂P x) :=
    hf.stronglyMeasurable.integral_kernel.measurable
  have hsq : Integrable (fun x => f x ^ 2) π := h2.integrable_sq
  have hcomp : Integrable (fun x => f x ^ 2) (P ∘ₘ π) := by
    change P ∘ₘ π = π at hinv
    simpa only [hinv] using hsq
  have hi : Integrable (fun x => ∫ y, f y ^ 2 ∂P x) π := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      Measure.integrable_integral_norm_of_integrable_comp hcomp
  have hj : ∀ᵐ x ∂π, (∫ y, f y ∂P x) ^ 2 ≤ ∫ y, f y ^ 2 ∂P x := by
    filter_upwards [ae_integrable P π hinv hsq] with x hx
    exact integral_sq_bound (P x) f
      ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hx)
  have hi2 : Integrable (fun x => (∫ y, f y ∂P x) ^ 2) π := by
    apply hi.mono' (hmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [hj] with x hx
    simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hi2, ?_⟩
  calc
    (∫ x, (∫ y, f y ∂P x) ^ 2 ∂π) ≤ ∫ x, ∫ y, f y ^ 2 ∂P x ∂π :=
      integral_mono_ae hi2 hi hj
    _ = ∫ x, f x ^ 2 ∂π := integral_invariant P π hinv hsq

theorem KernelL2.kernel_memLp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : X → ℝ) (hf : Measurable f) (h2 : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f y ∂P x) 2 π :=
  (kernel_memLp_and_sq_bound P π hinv f hf h2).1

theorem KernelL2.norm_sq {π : Measure X} (f : Lp ℝ 2 π) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [Real.norm_eq_abs, sq_abs]

noncomputable def KernelL2.action (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : Lp ℝ 2 π :=
  (kernel_memLp P π hinv f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).toLp _

theorem KernelL2.action_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) :
    ⇑(action P π hinv f) =ᵐ[π] (fun x => ∫ y, f y ∂P x) :=
  MemLp.coeFn_toLp _

theorem KernelL2.action_norm_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : ‖action P π hinv f‖ ≤ ‖f‖ := by
  have hsq : ‖action P π hinv f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq, norm_sq]
    calc
      (∫ x, action P π hinv f x ^ 2 ∂π) = ∫ x, (∫ y, f y ∂P x) ^ 2 ∂π := by
        apply integral_congr_ae
        filter_upwards [action_ae P π hinv f] with x hx
        rw [hx]
      _ ≤ ∫ x, f x ^ 2 ∂π :=
        (kernel_memLp_and_sq_bound P π hinv f (Lp.stronglyMeasurable f).measurable
          (Lp.memLp f)).2
  nlinarith [norm_nonneg (action P π hinv f), norm_nonneg f]

theorem KernelL2.kernel_congr_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f g : X → ℝ} (hfg : f =ᵐ[π] g) :
    (fun x => ∫ y, f y ∂P x) =ᵐ[π] (fun x => ∫ y, g y ∂P x) := by
  change P ∘ₘ π = π at hinv
  have hfg' : f =ᵐ[P ∘ₘ π] g := by simpa only [hinv] using hfg
  filter_upwards [Measure.ae_ae_of_ae_comp hfg'] with x hx
  exact integral_congr_ae hx

theorem KernelL2.action_add (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f g : Lp ℝ 2 π) :
    action P π hinv (f + g) = action P π hinv f + action P π hinv g := by
  apply Lp.ext
  filter_upwards [action_ae P π hinv (f + g), action_ae P π hinv f,
    action_ae P π hinv g, Lp.coeFn_add (action P π hinv f) (action P π hinv g),
    kernel_congr_ae P π hinv (Lp.coeFn_add f g),
    ae_integrable P π hinv ((Lp.memLp f).integrable (by norm_num)),
    ae_integrable P π hinv ((Lp.memLp g).integrable (by norm_num))]
      with x hsum hf hg ha hk hif hig
  rw [hsum, ha, Pi.add_apply, hf, hg, hk]
  exact integral_add hif hig

theorem KernelL2.action_smul (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (c : ℝ) (f : Lp ℝ 2 π) :
    action P π hinv (c • f) = c • action P π hinv f := by
  apply Lp.ext
  filter_upwards [action_ae P π hinv (c • f), action_ae P π hinv f,
    Lp.coeFn_smul c (action P π hinv f),
    kernel_congr_ae P π hinv (Lp.coeFn_smul c f)] with x hcf hf ha hk
  rw [hcf, ha, Pi.smul_apply, hf, hk]
  exact integral_smul c f

noncomputable def KernelL2.markovOp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  LinearMap.mkContinuous
    { toFun := action P π hinv
      map_add' := action_add P π hinv
      map_smul' := action_smul P π hinv }
    1 (fun f => by rw [one_mul]; exact action_norm_le P π hinv f)

theorem KernelL2.markovOp_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) :
    ⇑(markovOp P π hinv f) =ᵐ[π] (fun x => ∫ y, f y ∂P x) :=
  action_ae P π hinv f

theorem KernelL2.markovOp_norm_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : ‖markovOp P π hinv f‖ ≤ ‖f‖ :=
  action_norm_le P π hinv f

theorem KernelL2.norm_markovOp_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    ‖markovOp P π hinv‖ ≤ 1 :=
  (markovOp P π hinv).opNorm_le_bound zero_le_one
    (fun f => by simpa only [one_mul] using markovOp_norm_le P π hinv f)

end KernelL2

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal

section KernelPowers

variable {X : Type*} [MeasurableSpace X]

theorem KernelPowers.invariant_iterKernel (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) (hinv : Kernel.Invariant P π) (n : ℕ) :
    Kernel.Invariant (iterKernel P n) π := by
  induction n with
  | zero =>
      change π.bind (fun x => Measure.dirac x) = π
      exact Measure.bind_dirac
  | succ n ih =>
      exact hinv.comp ih

theorem KernelPowers.markovOp_pow_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (n : ℕ) (f : Lp ℝ 2 π) :
    ⇑((KernelL2.markovOp P π hinv ^ n) f) =ᵐ[π]
      (fun x => ∫ y, f y ∂iterKernel P n x) := by
  induction n generalizing f with
  | zero =>
      apply Filter.Eventually.of_forall
      intro x
      simp only [pow_zero, ContinuousLinearMap.one_apply, iterKernel_zero,
        Kernel.id_apply, integral_dirac' f x (Lp.stronglyMeasurable f)]
  | succ n ih =>
      have hn := invariant_iterKernel P π hinv n
      have hsucc := invariant_iterKernel P π hinv (n + 1)
      filter_upwards [ih (KernelL2.markovOp P π hinv f),
        KernelL2.kernel_congr_ae (iterKernel P n) π hn (KernelL2.markovOp_ae P π hinv f),
        KernelL2.ae_integrable (iterKernel P (n + 1)) π hsucc
          ((Lp.memLp f).integrable (by norm_num))] with x hx hrep hInt
      rw [pow_succ, ContinuousLinearMap.mul_apply, hx, hrep, iterKernel_succ]
      exact (Kernel.integral_comp hInt).symm

end KernelPowers

section BlockResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BlockResolvent.finite_telescope (A : E →L[ℝ] E) (s : E) (N : ℕ) :
    (∑ i ∈ Finset.range N, (A ^ i) s) - A (∑ i ∈ Finset.range N, (A ^ i) s) =
      s - (A ^ N) s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, map_add]
    calc
      _ = ((∑ i ∈ Finset.range N, (A ^ i) s) -
          A (∑ i ∈ Finset.range N, (A ^ i) s)) +
          ((A ^ N) s - A ((A ^ N) s)) := by abel
      _ = s - (A ^ (N + 1)) s := by
        rw [ih, pow_succ']
        simp only [ContinuousLinearMap.mul_apply]
        abel

theorem BlockResolvent.exists_sub_apply_of_summable_blocks (A : E →L[ℝ] E) (h : E) (N : ℕ)
    (hs : Summable (fun j : ℕ => (A ^ (j * N)) h)) :
    ∃ g : E, g - A g = h := by
  let s : E := ∑' j : ℕ, (A ^ (j * N)) h
  have hshift : (A ^ N) s = ∑' j : ℕ, (A ^ ((j + 1) * N)) h := by
    rw [show s = ∑' j : ℕ, (A ^ (j * N)) h from rfl, (A ^ N).map_tsum hs]
    congr 1
    funext j
    rw [← ContinuousLinearMap.mul_apply, ← pow_add]
    congr 2
    ring
  have hhead : s = h + (A ^ N) s := by
    rw [hshift]
    simpa only [Nat.zero_mul, pow_zero, ContinuousLinearMap.one_apply] using
      hs.tsum_eq_zero_add
  refine ⟨∑ i ∈ Finset.range N, (A ^ i) s, ?_⟩
  rw [finite_telescope]
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hhead)

theorem BlockResolvent.exists_sub_apply_of_sq_decay [CompleteSpace E]
    (A : E →L[ℝ] E) (h : E) (N : ℕ)
    (hdecay : ∀ j : ℕ, ‖(A ^ (j * N)) h‖ ^ 2 ≤ (1 / 4 : ℝ) ^ j * ‖h‖ ^ 2) :
    ∃ g : E, g - A g = h := by
  have hnorm (j : ℕ) : ‖(A ^ (j * N)) h‖ ≤ (1 / 2 : ℝ) ^ j * ‖h‖ := by
    have hsq : ((1 / 2 : ℝ) ^ j * ‖h‖) ^ 2 = (1 / 4 : ℝ) ^ j * ‖h‖ ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    have hn : 0 ≤ (1 / 2 : ℝ) ^ j * ‖h‖ := mul_nonneg (by positivity) (norm_nonneg h)
    have hd := hdecay j
    nlinarith [norm_nonneg ((A ^ (j * N)) h)]
  apply exists_sub_apply_of_summable_blocks A h N
  apply Summable.of_norm_bounded (g := fun j : ℕ => (1 / 2 : ℝ) ^ j * ‖h‖)
  · exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right ‖h‖
  · exact hnorm

end BlockResolvent


section TVBound

open MeasureTheory ProbabilityTheory MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

/-- Cauchy–Schwarz for a finite measure: `(∫ h dα)² ≤ α(X) ∫ h² dα`. -/
theorem TVBound.sq_integral_le_mass_mul (α : Measure X) [IsFiniteMeasure α] (h : X → ℝ)
    (h1 : Integrable h α) (h2 : Integrable (fun x => h x ^ 2) α) :
    (∫ x, h x ∂α) ^ 2 ≤ (α Set.univ).toReal * ∫ x, h x ^ 2 ∂α := by
  set m : ℝ := (α Set.univ).toReal with hm_def
  set I : ℝ := ∫ x, h x ∂α with hI_def
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  rcases hm.lt_or_eq with hpos | hzero
  · have hnn : 0 ≤ ∫ x, (m * h x - I) ^ 2 ∂α := integral_nonneg (fun _ => sq_nonneg _)
    have heq : (fun x => (m * h x - I) ^ 2) =
        fun x => (m ^ 2 * h x ^ 2 - (2 * m * I) * h x) + I ^ 2 := by
      funext x; ring
    have e1 : Integrable (fun x => m ^ 2 * h x ^ 2) α := h2.const_mul _
    have e2 : Integrable (fun x => (2 * m * I) * h x) α := h1.const_mul _
    have e12 : Integrable (fun x => m ^ 2 * h x ^ 2 - (2 * m * I) * h x) α := e1.sub e2
    have hexp : ∫ x, (m * h x - I) ^ 2 ∂α =
        m ^ 2 * ∫ x, h x ^ 2 ∂α - (2 * m * I) * I + I ^ 2 * m := by
      rw [heq, integral_add e12 (integrable_const _), integral_sub e1 e2, integral_const_mul,
        integral_const_mul, integral_const]
      simp only [smul_eq_mul, Measure.real, ← hm_def, ← hI_def]
      ring
    have hsq : 0 ≤ ∫ x, h x ^ 2 ∂α := integral_nonneg (fun _ => sq_nonneg _)
    rw [hexp] at hnn
    nlinarith
  · have hα : α = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      rcases (ENNReal.toReal_eq_zero_iff _).mp hzero.symm with h0 | htop
      · exact h0
      · exact absurd htop (measure_ne_top _ _)
    have hI0 : I = 0 := by
      rw [hI_def, hα, integral_zero_measure]
    rw [hI0]
    have hsq : 0 ≤ ∫ x, h x ^ 2 ∂α := integral_nonneg (fun _ => sq_nonneg _)
    nlinarith

/-- The `tvDist` (sup over measurable sets of `|μ A - ν A|`) dominates each individual
difference, for probability measures. -/
theorem TVBound.abs_sub_le_tvDist (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {A : Set X} (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ tvDist μ ν := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro r ⟨B, hB, rfl⟩
    have h1 : (μ B).toReal ≤ 1 := by
      have := prob_le_one (μ := μ) (s := B)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h2 : (ν B).toReal ≤ 1 := by
      have := prob_le_one (μ := ν) (s := B)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h3 : 0 ≤ (μ B).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (ν B).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  · exact ⟨A, hA, rfl⟩

/-- The key one-measure estimate: if `tvDist μ ν ≤ ρ` and `h` has `ν`-mean zero, then
`(∫ h dμ)² ≤ 2ρ (∫ h² dμ + ∫ h² dν)`.  Proof by the Hahn decomposition of `μ - ν`. -/
theorem TVBound.sq_integral_le_of_tvDist (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ρ : ℝ) (htv : tvDist μ ν ≤ ρ) (h : X → ℝ) (hh : Measurable h)
    (hμ2 : Integrable (fun x => h x ^ 2) μ) (hν2 : Integrable (fun x => h x ^ 2) ν)
    (hmean : ∫ x, h x ∂ν = 0) :
    (∫ x, h x ∂μ) ^ 2 ≤ 2 * ρ * (∫ x, h x ^ 2 ∂μ + ∫ x, h x ^ 2 ∂ν) := by
  have hμ1 : Integrable h μ :=
    ((memLp_two_iff_integrable_sq hh.aestronglyMeasurable).mpr hμ2).integrable (by norm_num)
  have hν1 : Integrable h ν :=
    ((memLp_two_iff_integrable_sq hh.aestronglyMeasurable).mpr hν2).integrable (by norm_num)
  obtain ⟨s, hs, hsν, hsμ⟩ := hahn_decomposition μ ν
  -- the two pieces of the Hahn decomposition of `μ - ν`
  set α : Measure X := μ.restrict s - ν.restrict s with hα_def
  set β : Measure X := ν.restrict sᶜ - μ.restrict sᶜ with hβ_def
  have hle1 : ν.restrict s ≤ μ.restrict s := by
    refine Measure.le_iff.mpr fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hsν _ (ht.inter hs) Set.inter_subset_right
  have hle2 : μ.restrict sᶜ ≤ ν.restrict sᶜ := by
    refine Measure.le_iff.mpr fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hsμ _ (ht.inter hs.compl) Set.inter_subset_right
  have hαμ : α ≤ μ := Measure.sub_le.trans Measure.restrict_le_self
  have hβν : β ≤ ν := Measure.sub_le.trans Measure.restrict_le_self
  have hαadd : α + ν.restrict s = μ.restrict s := Measure.sub_add_cancel_of_le hle1
  have hβadd : β + μ.restrict sᶜ = ν.restrict sᶜ := Measure.sub_add_cancel_of_le hle2
  -- integrability transfers
  have hα1 : Integrable h α := hμ1.mono_measure hαμ
  have hα2 : Integrable (fun x => h x ^ 2) α := hμ2.mono_measure hαμ
  have hβ1 : Integrable h β := hν1.mono_measure hβν
  have hβ2 : Integrable (fun x => h x ^ 2) β := hν2.mono_measure hβν
  -- decomposition of the integrals
  have hμsplit : ∫ x, h x ∂μ = ∫ x in s, h x ∂μ + ∫ x in sᶜ, h x ∂μ :=
    (integral_add_compl hs hμ1).symm
  have hνsplit : ∫ x, h x ∂ν = ∫ x in s, h x ∂ν + ∫ x in sᶜ, h x ∂ν :=
    (integral_add_compl hs hν1).symm
  have hαint : ∫ x in s, h x ∂μ = ∫ x, h x ∂α + ∫ x in s, h x ∂ν := by
    rw [← hαadd, integral_add_measure hα1 (hν1.mono_measure Measure.restrict_le_self)]
  have hβint : ∫ x in sᶜ, h x ∂ν = ∫ x, h x ∂β + ∫ x in sᶜ, h x ∂μ := by
    rw [← hβadd, integral_add_measure hβ1 (hμ1.mono_measure Measure.restrict_le_self)]
  have hdiff : ∫ x, h x ∂μ = ∫ x, h x ∂α - ∫ x, h x ∂β := by
    rw [hmean] at hνsplit
    linarith
  -- masses of the pieces are at most `ρ`
  have hmassα : (α Set.univ).toReal ≤ ρ := by
    have h1 : α Set.univ = μ s - ν s := by
      rw [hα_def, Measure.sub_apply MeasurableSet.univ hle1, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ]
    have hle : ν s ≤ μ s := hsν s hs subset_rfl
    rw [h1, ENNReal.toReal_sub_of_le hle (measure_ne_top _ _)]
    exact (le_abs_self _).trans ((abs_sub_le_tvDist μ ν hs).trans htv)
  have hmassβ : (β Set.univ).toReal ≤ ρ := by
    have h1 : β Set.univ = ν sᶜ - μ sᶜ := by
      rw [hβ_def, Measure.sub_apply MeasurableSet.univ hle2, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ]
    have hle : μ sᶜ ≤ ν sᶜ := hsμ sᶜ hs.compl subset_rfl
    rw [h1, ENNReal.toReal_sub_of_le hle (measure_ne_top _ _)]
    have := abs_sub_le_tvDist μ ν hs.compl
    rw [abs_sub_comm] at this
    exact (le_abs_self _).trans (this.trans htv)
  have hmassα0 : 0 ≤ (α Set.univ).toReal := ENNReal.toReal_nonneg
  have hmassβ0 : 0 ≤ (β Set.univ).toReal := ENNReal.toReal_nonneg
  -- Cauchy–Schwarz on each piece
  have hcsα := sq_integral_le_mass_mul α h hα1 hα2
  have hcsβ := sq_integral_le_mass_mul β h hβ1 hβ2
  have hsqα : ∫ x, h x ^ 2 ∂α ≤ ∫ x, h x ^ 2 ∂μ :=
    integral_mono_measure hαμ (Filter.Eventually.of_forall fun _ => sq_nonneg _) hμ2
  have hsqβ : ∫ x, h x ^ 2 ∂β ≤ ∫ x, h x ^ 2 ∂ν :=
    integral_mono_measure hβν (Filter.Eventually.of_forall fun _ => sq_nonneg _) hν2
  have hsqα0 : 0 ≤ ∫ x, h x ^ 2 ∂α := integral_nonneg fun _ => sq_nonneg _
  have hsqβ0 : 0 ≤ ∫ x, h x ^ 2 ∂β := integral_nonneg fun _ => sq_nonneg _
  have hA : (∫ x, h x ∂α) ^ 2 ≤ ρ * ∫ x, h x ^ 2 ∂μ := by
    calc (∫ x, h x ∂α) ^ 2 ≤ (α Set.univ).toReal * ∫ x, h x ^ 2 ∂α := hcsα
      _ ≤ ρ * ∫ x, h x ^ 2 ∂μ := by
        apply mul_le_mul hmassα hsqα hsqα0 (hmassα0.trans hmassα)
  have hB : (∫ x, h x ∂β) ^ 2 ≤ ρ * ∫ x, h x ^ 2 ∂ν := by
    calc (∫ x, h x ∂β) ^ 2 ≤ (β Set.univ).toReal * ∫ x, h x ^ 2 ∂β := hcsβ
      _ ≤ ρ * ∫ x, h x ^ 2 ∂ν := by
        apply mul_le_mul hmassβ hsqβ hsqβ0 (hmassβ0.trans hmassβ)
  rw [hdiff]
  nlinarith [sq_nonneg (∫ x, h x ∂α + ∫ x, h x ∂β)]

/-- Kernel form: if `tvDist (Q x) π ≤ ρ` for every `x` and `π` is `Q`-invariant, then the
`L²(π)`-norm of `Qh` is at most `4ρ` times that of `h`, for `h` of `π`-mean zero. -/
theorem TVBound.integral_sq_kernel_le (Q : Kernel X X) [IsMarkovKernel Q] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant Q π) (ρ : ℝ)
    (hrate : ∀ x, tvDist (Q x) π ≤ ρ) (h : X → ℝ) (hh : Measurable h)
    (hL2 : Integrable (fun x => h x ^ 2) π) (hmean : ∫ x, h x ∂π = 0) :
    ∫ x, (∫ y, h y ∂Q x) ^ 2 ∂π ≤ 4 * ρ * ∫ x, h x ^ 2 ∂π := by
  have hmemLp : MemLp h 2 π := (memLp_two_iff_integrable_sq hh.aestronglyMeasurable).mpr hL2
  have hmeas : Measurable (fun x => ∫ y, h y ∂Q x) :=
    hh.stronglyMeasurable.integral_kernel.measurable
  have hi2 : Integrable (fun x => (∫ y, h y ∂Q x) ^ 2) π :=
    (KernelL2.kernel_memLp Q π hinv h hh hmemLp).integrable_sq
  have hcomp : Integrable (fun x => h x ^ 2) (Q ∘ₘ π) := by
    change Q ∘ₘ π = π at hinv
    simpa only [hinv] using hL2
  have hi : Integrable (fun x => ∫ y, h y ^ 2 ∂Q x) π := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      Measure.integrable_integral_norm_of_integrable_comp hcomp
  have hpt : ∀ᵐ x ∂π, (∫ y, h y ∂Q x) ^ 2 ≤
      2 * ρ * (∫ y, h y ^ 2 ∂Q x + ∫ x, h x ^ 2 ∂π) := by
    filter_upwards [KernelL2.ae_integrable Q π hinv hL2] with x hx
    exact sq_integral_le_of_tvDist (Q x) π ρ (hrate x) h hh hx hL2 hmean
  calc ∫ x, (∫ y, h y ∂Q x) ^ 2 ∂π
      ≤ ∫ x, 2 * ρ * (∫ y, h y ^ 2 ∂Q x + ∫ x, h x ^ 2 ∂π) ∂π :=
        integral_mono_ae hi2 ((hi.add (integrable_const _)).const_mul _) hpt
    _ = 2 * ρ * (∫ x, h x ^ 2 ∂π + ∫ x, h x ^ 2 ∂π) := by
        rw [integral_const_mul, integral_add hi (integrable_const _), integral_const,
          KernelL2.integral_invariant Q π hinv hL2]
        simp only [smul_eq_mul, probReal_univ, one_mul]
    _ = 4 * ρ * ∫ x, h x ^ 2 ∂π := by ring

end TVBound

section Lag

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X]

/-- Uniform ergodicity gives a lag `N ≥ 1` with `tvDist (Pᴺ x, π) ≤ 1/16` for every `x`. -/
theorem Lag.exists_lag_tvDist_le (P : Kernel X X) (π : Measure X)
    (huni : UniformlyErgodic P π) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16 := by
  obtain ⟨R, t, _hR, ht0, ht1, hrate⟩ := huni
  have hlim : Tendsto (fun n : ℕ => R * t ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul R
  obtain ⟨N, hlt, hN⟩ :=
    ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))).and
      (eventually_ge_atTop 1)).exists
  exact ⟨N, hN, fun x => (hrate x N hN).trans hlt.le⟩

end Lag

section Decay

open MeasureTheory ProbabilityTheory MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

/-- One block step: for `f ∈ L²(π)` of mean zero, `‖Aᴺ f‖² ≤ (1/4)‖f‖²` and `Aᴺ f` again has
mean zero, where `A` is the Markov operator and the lag `N` satisfies the `1/16` bound. -/
theorem Decay.block_step (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16) (f : Lp ℝ 2 π)
    (hmean : ∫ x, f x ∂π = 0) :
    (∫ x, ((KernelL2.markovOp P π hinv ^ N) f) x ∂π = 0) ∧
      ‖(KernelL2.markovOp P π hinv ^ N) f‖ ^ 2 ≤ (1 / 4 : ℝ) * ‖f‖ ^ 2 := by
  have hQinv := KernelPowers.invariant_iterKernel P π hinv N
  have hrep := KernelPowers.markovOp_pow_ae P π hinv N f
  have hfm : Measurable (f : X → ℝ) := (Lp.stronglyMeasurable f).measurable
  have hf1 : Integrable (f : X → ℝ) π := (Lp.memLp f).integrable (by norm_num)
  constructor
  · rw [integral_congr_ae hrep, KernelL2.integral_invariant (iterKernel P N) π hQinv hf1, hmean]
  · rw [KernelL2.norm_sq, KernelL2.norm_sq]
    calc (∫ x, ((KernelL2.markovOp P π hinv ^ N) f) x ^ 2 ∂π)
        = ∫ x, (∫ y, f y ∂iterKernel P N x) ^ 2 ∂π := by
          apply integral_congr_ae
          filter_upwards [hrep] with x hx
          rw [hx]
      _ ≤ 4 * (1 / 16) * ∫ x, f x ^ 2 ∂π :=
          TVBound.integral_sq_kernel_le (iterKernel P N) π hQinv (1 / 16) hrate f hfm
            (Lp.memLp f).integrable_sq hmean
      _ = (1 / 4 : ℝ) * ∫ x, f x ^ 2 ∂π := by ring

/-- Iterating the block step: `‖A^{jN} f‖² ≤ (1/4)^j ‖f‖²` for mean-zero `f`. -/
theorem Decay.pow_decay (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16) (f : Lp ℝ 2 π)
    (hmean : ∫ x, f x ∂π = 0) (j : ℕ) :
    ‖(KernelL2.markovOp P π hinv ^ (j * N)) f‖ ^ 2 ≤ (1 / 4 : ℝ) ^ j * ‖f‖ ^ 2 := by
  set A := KernelL2.markovOp P π hinv with hA
  have key : ∀ j : ℕ, (∫ x, ((A ^ N) ^ j) f x ∂π = 0) ∧
      ‖((A ^ N) ^ j) f‖ ^ 2 ≤ (1 / 4 : ℝ) ^ j * ‖f‖ ^ 2 := by
    intro j
    induction j with
    | zero => simpa using hmean
    | succ j ih =>
      have hstep := block_step P π hinv N hrate (((A ^ N) ^ j) f) ih.1
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      refine ⟨hstep.1, ?_⟩
      calc ‖(A ^ N) (((A ^ N) ^ j) f)‖ ^ 2 ≤ (1 / 4 : ℝ) * ‖((A ^ N) ^ j) f‖ ^ 2 := hstep.2
        _ ≤ (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ j * ‖f‖ ^ 2) := by gcongr; exact ih.2
        _ = (1 / 4 : ℝ) ^ (j + 1) * ‖f‖ ^ 2 := by ring
  have hpow : A ^ (j * N) = (A ^ N) ^ j := by rw [mul_comm, pow_mul]
  rw [hpow]
  exact (key j).2

end Decay

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) :
    ∃ g : X → ℝ, Measurable g ∧ MemLp g 2 π ∧
      Measurable (fun x => ∫ y, g y ∂(P x)) ∧
      MemLp (fun x => ∫ y, g y ∂(P x)) 2 π ∧
      ∀ᵐ x ∂π, g x - ∫ y, g y ∂(P x) = f x - ∫ x, f x ∂π := by
  have hinv : Kernel.Invariant P π := hP.1
  let μf : ℝ := ∫ x, f x ∂π
  have hc : MemLp (fun x => f x - μf) 2 π := hL2.sub (memLp_const μf)
  let h : Lp ℝ 2 π := hc.toLp (fun x => f x - μf)
  have hae : ⇑h =ᵐ[π] (fun x => f x - μf) := MemLp.coeFn_toLp hc
  have hmean : ∫ x, h x ∂π = 0 := by
    rw [integral_congr_ae hae,
      integral_sub (hL2.integrable (by norm_num)) (integrable_const μf)]
    simp [μf]
  obtain ⟨N, _hN, hrate⟩ := Lag.exists_lag_tvDist_le P π huni
  let A : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π := KernelL2.markovOp P π hinv
  have hdecay : ∀ j : ℕ, ‖(A ^ (j * N)) h‖ ^ 2 ≤ (1 / 4 : ℝ) ^ j * ‖h‖ ^ 2 :=
    fun j => Decay.pow_decay P π hinv N hrate h hmean j
  obtain ⟨g, hgeq⟩ := BlockResolvent.exists_sub_apply_of_sq_decay A h N hdecay
  have hgm : Measurable (g : X → ℝ) := (Lp.stronglyMeasurable g).measurable
  refine ⟨g, hgm, Lp.memLp g, hgm.stronglyMeasurable.integral_kernel.measurable,
    KernelL2.kernel_memLp P π hinv g hgm (Lp.memLp g), ?_⟩
  have hgeq_ae : ⇑(g - A g) =ᵐ[π] ⇑h := Filter.Eventually.of_forall (fun x => by rw [hgeq])
  filter_upwards [Lp.coeFn_sub g (A g), KernelL2.markovOp_ae P π hinv g,
    hgeq_ae, hae] with x hsub hAg heq hh
  change (g - A g) x = g x - (A g) x at hsub
  change (A g) x = ∫ y, g y ∂P x at hAg
  calc
    g x - ∫ y, g y ∂P x = (g - A g) x := by rw [hsub, hAg]
    _ = h x := heq
    _ = f x - ∫ x, f x ∂π := hh

#print axioms solution
