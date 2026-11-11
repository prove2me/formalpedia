-- Prove2me | solution 1 for OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:50.058953+00:00
-- url     : https://prove2.me/submissions/36dd058d-0f65-4440-afed-a969916a2385

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_DensityTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.DensityTransport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {F : X → Y} {G : Y → X}

theorem map_inverse_eq (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x) : ν.map G = μ := by
  rw [← hmap, Measure.map_map hG hF]
  calc
    μ.map (G ∘ F) = μ.map id := Measure.map_congr hinv
    _ = μ := Measure.map_id

theorem map_withDensity_eq (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ≥0∞} (hh : Measurable h) :
    (μ.withDensity h).map F = ν.withDensity (h ∘ G) := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs,
    ← hmap, Measure.restrict_map hF hs,
    lintegral_map' (hh.comp hG).aemeasurable hF.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hinv] with x hx
  simp only [Function.comp_apply, hx]

theorem eLpNorm_comp_inverse {E : Type*} [NormedAddCommGroup E]
    (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → E} (hh : AEStronglyMeasurable h μ) (p : ℝ≥0∞) :
    eLpNorm (h ∘ G) p ν = eLpNorm h p μ := by
  exact eLpNorm_comp_measurePreserving hh
    ⟨hG, map_inverse_eq hF hG hmap hinv⟩

theorem real_density_transport (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ} (hh : Measurable h) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map F =
      ν.withDensity (fun y => ENNReal.ofReal (h (G y))) ∧
    eLpNorm (h ∘ G) 2 ν = eLpNorm h 2 μ := by
  constructor
  · exact map_withDensity_eq hF hG hmap hinv hh.ennreal_ofReal
  · exact eLpNorm_comp_inverse hF hG hmap hinv hh.aestronglyMeasurable 2

theorem real_density_transport_ae (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ} (hh : AEMeasurable h μ) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map F =
      ν.withDensity (fun y => ENNReal.ofReal (h (G y))) ∧
    eLpNorm (h ∘ G) 2 ν = eLpNorm h 2 μ := by
  have hback : ν.map G = μ := map_inverse_eq hF hG hmap hinv
  have ht : Filter.Tendsto G (ae ν) (ae μ) := by
    rw [← hback]
    exact Measure.tendsto_ae_map hG.aemeasurable
  have heq : h =ᵐ[μ] hh.mk h := hh.ae_eq_mk
  have heqG : h ∘ G =ᵐ[ν] hh.mk h ∘ G := heq.comp_tendsto ht
  obtain ⟨hweighted, hnorm⟩ := real_density_transport hF hG hmap hinv hh.measurable_mk
  constructor
  · have hx : μ.withDensity (fun x => ENNReal.ofReal (h x)) =
        μ.withDensity (fun x => ENNReal.ofReal (hh.mk h x)) := by
      apply withDensity_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    have hy : ν.withDensity (fun y => ENNReal.ofReal (h (G y))) =
        ν.withDensity (fun y => ENNReal.ofReal (hh.mk h (G y))) := by
      apply withDensity_congr_ae
      filter_upwards [heqG] with y hy
      exact congrArg ENNReal.ofReal hy
    rw [hx, hy]
    exact hweighted
  · calc
      eLpNorm (h ∘ G) 2 ν = eLpNorm (hh.mk h ∘ G) 2 ν := eLpNorm_congr_ae heqG
      _ = eLpNorm (hh.mk h) 2 μ := hnorm
      _ = eLpNorm h 2 μ := (eLpNorm_congr_ae heq).symm

end Invariant233.DensityTransport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointLoss
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace Invariant233.EndpointLoss

variable {X : Type*} [MeasurableSpace X]

theorem sqrt_integral_sq_eq_norm {μ : Measure X} (f : Lp ℝ 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖f‖ := by
  have hs : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hs, Real.sqrt_sq (norm_nonneg f)]

theorem setIntegral_density_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (∫ x in s, h x ∂μ) ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two h_nonneg
    (show 0 ≤ᵐ[μ] s.indicator (fun _ : X => (1 : ℝ)) from
      Filter.Eventually.of_forall (fun x => by
        change 0 ≤ s.indicator (fun _ : X => (1 : ℝ)) x
        by_cases hx : x ∈ s <;> simp [hx]))
    (by simpa using hh) (by simpa using (MemLp.indicator hs (memLp_const (1 : ℝ))))
  have hmul : (fun x => h x * s.indicator (fun _ : X => (1 : ℝ)) x) =
      s.indicator h := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hpow : (fun x => (s.indicator (fun _ : X => (1 : ℝ)) x) ^ (2 : ℝ)) =
      s.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hmul, integral_indicator hs, hpow] at hCS
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hmass : (∫ x, s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = μ.real s := by
    rw [integral_indicator hs]
    simp
  simpa only [hmass] using hCS

theorem withDensity_measureReal_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).real s ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  rw [measureReal_def, withDensity_apply _ hs]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_ae h_nonneg) hh.aestronglyMeasurable.restrict]
  exact setIntegral_density_le_sqrt μ hh h_nonneg hs

end Invariant233.EndpointLoss

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteUniformLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace Invariant233.FiniteUniformLaw

theorem map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).toMeasure.map e = (PMF.uniformOfFintype β).toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton b)]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext a
    exact e.eq_symm_apply.symm
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem infinitePi_restrict_uniform {ι : Type*} (α : ι → Type*)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] (s : Finset ι) :
    (Measure.infinitePi (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).map s.restrict =
      (PMF.uniformOfFintype ((i : s) → α i)).toMeasure := by
  rw [Measure.infinitePi_map_restrict]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  symm
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  exact Or.inr (ENNReal.natCast_ne_top _)

end Invariant233.FiniteUniformLaw

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.FiniteSupportWeights

variable {X ι κ : Type*} [MeasurableSpace X]

theorem ae_mem_integerCore (μ : Measure X) (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ) (hs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ, x ∈ integerCore σ s := by
  exact ae_all_iff.mpr fun n => (hσ n).quasiMeasurePreserving.ae hs

theorem measurableSet_integerCore (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, Measurable (σ n)) (hs : MeasurableSet s) :
    MeasurableSet (integerCore σ s) := by
  have heq : integerCore σ s = ⋂ n : ℤ, σ n ⁻¹' s := by
    ext x
    simp [integerCore]
  rw [heq]
  exact MeasurableSet.iInter fun n => hs.preimage (hσ n)

omit [MeasurableSpace X] in

theorem integerCore_subset (σ : ℤ → X → X) (s : Set X)
    (hzero : ∀ x, σ 0 x = x) : integerCore σ s ⊆ s := by
  intro x hx
  simpa only [hzero] using hx 0

omit [MeasurableSpace X] in

theorem mem_integerCore_translate_iff (σ : ℤ → X → X) (s : Set X)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x)) (n : ℤ) (x : X) :
    σ n x ∈ integerCore σ s ↔ x ∈ integerCore σ s := by
  constructor
  · intro hx m
    have hm := hx (m - n)
    simpa only [← hadd, sub_add_cancel] using hm
  · intro hx m
    simpa only [← hadd] using hx (m + n)

theorem uniform_nonzero_floor_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal t := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico (1 - t) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨?_, hu1⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, ?_, hu1⟩
      · intro h
        linarith [h.2]
      · linarith
  rw [hset, Real.volume_Ico]
  congr 1
  ring

theorem uniform_nonzero_floor_of_nonpos {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 0) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal (-t) := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico 0 (-t) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨hu0, ?_⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, hu0, ?_⟩
      · intro h
        linarith [h.1]
      · linarith
  rw [hset, Real.volume_Ico, sub_zero]

theorem uniform_nonzero_floor_le (t : ℝ) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} ≤
      ENNReal.ofReal |t| := by
  by_cases ht : |t| ≤ 1
  · have ht' := abs_le.mp ht
    rcases le_total 0 t with hpos | hneg
    · rw [uniform_nonzero_floor_of_nonneg hpos ht'.2, abs_of_nonneg hpos]
    · rw [uniform_nonzero_floor_of_nonpos ht'.1 hneg, abs_of_nonpos hneg]
  · calc
      _ ≤ (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal |t| := ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge ht))

theorem measure_nonzero_floor_le (μ : Measure X) (u : X → ℝ)
    (hu : MeasurePreserving u μ (volume.restrict (Set.Ico (0 : ℝ) 1))) (t : ℝ) :
    μ {x | Int.floor (u x + t) ≠ 0} ≤ ENNReal.ofReal |t| := by
  have hmeas : MeasurableSet {v : ℝ | Int.floor (v + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  change μ (u ⁻¹' {v : ℝ | Int.floor (v + t) ≠ 0}) ≤ _
  rw [hu.measure_preimage hmeas.nullMeasurableSet]
  exact uniform_nonzero_floor_le t

theorem measurableSet_finite_support {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Zero R] [Countable ι]
    (a : ι → X → R) (ha : ∀ i, Measurable (a i)) :
    MeasurableSet {x | (Function.support (fun i => a i x)).Finite} := by
  classical
  have heq : {x | (Function.support (fun i => a i x)).Finite} =
      ⋃ s : Finset ι, ⋂ i : ι, ⋂ (_ : i ∉ s), {x | a i x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hx
      refine ⟨hx.toFinset, ?_⟩
      intro i hi
      by_contra hne
      exact hi (hx.mem_toFinset.mpr hne)
    · rintro ⟨s, hs⟩
      apply s.finite_toSet.subset
      intro i hi
      by_contra his
      exact hi (hs i his)
  rw [heq]
  refine MeasurableSet.iUnion fun s => MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun _ => ?_
  exact (ha i) (measurableSet_singleton 0)

theorem ae_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) (k : ℤ) :
    ∀ᵐ x ∂μ, (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  have hs : Summable (fun i => |(k : ℝ)| * α i) := hα.mul_left _
  have hbound : (∑' i, μ {x | Int.floor (u i x + (k : ℝ) * α i) ≠ 0}) ≤
      ∑' i, ENNReal.ofReal (|(k : ℝ)| * α i) := by
    apply ENNReal.tsum_le_tsum
    intro i
    simpa only [abs_mul, abs_of_nonneg (hα0 i)] using
      measure_nonzero_floor_le μ (u i) (hu i) ((k : ℝ) * α i)
  exact ae_finite_setOfPred_mem (lt_of_le_of_lt hbound hs.tsum_ofReal_lt_top).ne

theorem ae_all_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  exact ae_all_iff.mpr fun k => ae_finite_floor_support μ u hu α hα0 hα k

theorem exists_invariant_conull_floor_support [Countable ι]
    (μ : Measure X) (σ : ℤ → X → X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x))
    (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set X, MeasurableSet s ∧ (∀ᵐ x ∂μ, x ∈ s) ∧
      (∀ n x, σ n x ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  let a : ℤ → ι → X → ℤ := fun k i x => Int.floor (u i x + (k : ℝ) * α i)
  let s₀ : Set X := {x | ∀ k : ℤ, (Function.support (fun i => a k i x)).Finite}
  have hs₀ : MeasurableSet s₀ := by
    have heq : s₀ = ⋂ k : ℤ, {x | (Function.support (fun i => a k i x)).Finite} := by
      ext x
      simp [s₀]
    rw [heq]
    exact MeasurableSet.iInter fun k => measurableSet_finite_support (a k)
      (fun i => ((hu i).measurable.add_const _).floor)
  refine ⟨integerCore σ s₀,
    measurableSet_integerCore σ s₀ (fun n => (hσ n).measurable) hs₀, ?_, ?_, ?_⟩
  · exact ae_mem_integerCore μ σ s₀ hσ (ae_all_finite_floor_support μ u hu α hα0 hα)
  · exact mem_integerCore_translate_iff σ s₀ hadd
  · intro x hx
    exact integerCore_subset σ s₀ hzero hx

end Invariant233.FiniteSupportWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleWeightSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.CircleWeightSupport

theorem exists_invariant_conull_floor_support {ι : Type*} [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (n : ℤ) x, x + n • (θ : UnitAddCircle) ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i =>
          Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) +
            (k : ℝ) * α i))).Finite := by
  apply FiniteSupportWeights.exists_invariant_conull_floor_support
    (volume : Measure UnitAddCircle) (fun n x => x + n • (θ : UnitAddCircle))
    (fun n => measurePreserving_add_right volume (n • (θ : UnitAddCircle)))
    (by intro x; simp)
    (by intro m n x; simp [add_zsmul, add_comm, add_left_comm])
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ))
    (fun i => measurePreserving_characterRepresentative (q i) (hq i)) α hα0 hα

end Invariant233.CircleWeightSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_fract_add (x y : ℝ) :
    ⌊Int.fract x + y⌋ + ⌊x⌋ = ⌊x + y⌋ := by
  rw [Int.fract, sub_add_eq_add_sub, Int.floor_sub_intCast]
  omega

theorem floor_cocycle (u α : ℝ) (v n : ℤ) :
    ⌊u + (v : ℝ) * α⌋ + ⌊Int.fract (u + (v : ℝ) * α) + (n : ℝ) * α⌋ =
      ⌊u + ((v + n : ℤ) : ℝ) * α⌋ := by
  rw [add_comm, floor_fract_add]
  congr 1
  push_cast
  ring

theorem floor_add_eq_indicator {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u < 1) (t : ℝ) :
    ⌊u + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ u then 1 else 0 := by
  have hsplit : ⌊u + t⌋ = ⌊u + Int.fract t⌋ + ⌊t⌋ := by
    rw [← Int.floor_add_intCast]
    congr 1
    rw [add_assoc, Int.fract_add_floor]
  rw [hsplit]
  split_ifs with h
  · have hf : ⌊u + Int.fract t⌋ = 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [Int.fract_lt_one t]
    rw [hf]
    omega
  · have hf : ⌊u + Int.fract t⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · exact add_nonneg hu₀ (Int.fract_nonneg t)
      · linarith
    rw [hf]
    omega

theorem floor_sub_eq_crossing {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (t : ℝ) :
    ⌊w + t⌋ - ⌊u + t⌋ =
      if u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w then 1 else 0 := by
  rw [floor_add_eq_indicator hw₀ hw₁, floor_add_eq_indicator hu₀ hu₁]
  by_cases huT : 1 - Int.fract t ≤ u
  · have hwT : 1 - Int.fract t ≤ w := huT.trans huw
    simp [huT, hwT, not_lt_of_ge huT]
  · have hut : u < 1 - Int.fract t := lt_of_not_ge huT
    by_cases hwT : 1 - Int.fract t ≤ w
    · simp [huT, hwT, hut]
    · simp [huT, hwT]

theorem floor_sub_eq_one_iff {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (t : ℝ) :
    ⌊w + t⌋ - ⌊u + t⌋ = 1 ↔
      u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w := by
  rw [floor_sub_eq_crossing hu₀ hu₁ hw₀ hw₁ huw]
  split_ifs <;> simp_all

theorem floor_sub_bounds {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1) (t : ℝ) :
    -1 ≤ ⌊w + t⌋ - ⌊u + t⌋ ∧ ⌊w + t⌋ - ⌊u + t⌋ ≤ 1 := by
  rw [floor_add_eq_indicator hw₀ hw₁, floor_add_eq_indicator hu₀ hu₁]
  split_ifs <;> omega

end FloorCocycle
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

theorem exp_tsum_floor_cocycle {I : Type*} (x θ c : I → ℝ) (k n : ℤ)
    (hk : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ))) =
      Real.exp (-(∑' i, c i *
        (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ))) *
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) := by
  have hcoord (i : I) :
      c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ) =
        c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ) +
        c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ) := by
    rw [← FloorCocycle.floor_cocycle]
    push_cast
    ring
  rw [tsum_congr hcoord,
    (summable_weighted_int c hk).tsum_add (summable_weighted_int c hn),
    neg_add, Real.exp_add, mul_comm]

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleCharacterDynamics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace CircleCharacterDynamics

local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem coe_representative (x : Circle) : ((rep x : ℝ) : Circle) = x :=
  AddCircle.coe_equivIco

theorem representative_add_real (x : Circle) (t : ℝ) :
    rep (x + (t : Circle)) = Int.fract (rep x + t) := by
  rw [← representative_coe]
  congr 1
  rw [AddCircle.coe_add, coe_representative]

theorem zsmul_real_phase (q : ℤ) (θ : ℝ) :
    q • (θ : Circle) = ((Int.fract ((q : ℝ) * θ) : ℝ) : Circle) := by
  rw [AddCircle.coe_fract]
  simpa only [zsmul_eq_mul] using
    (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := q) (x := θ)).symm

theorem character_orbit_representative (q v : ℤ) (θ : ℝ) (x : Circle) :
    rep (q • (x + v • (θ : Circle))) =
      Int.fract (rep (q • x) + (v : ℝ) * Int.fract ((q : ℝ) * θ)) := by
  rw [zsmul_add, smul_comm q v, zsmul_real_phase]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  exact representative_add_real _ _

end CircleCharacterDynamics
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.CircleWeights

variable {ι : Type*}

theorem coordinate_mem_Ico (q : ι → ℤ) (i : ι) (x : UnitAddCircle) :
    coordinate q i x ∈ Ico (0 : ℝ) 1 := by
  simpa only [coordinate, representative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 (q i • x)).property

theorem coordinate_rotate (θ : ℝ) (q : ι → ℤ) (i : ι)
    (k : ℤ) (x : UnitAddCircle) :
    coordinate q i (rotate θ k x) =
      Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) := by
  exact CircleCharacterDynamics.character_orbit_representative (q i) k θ x

theorem exists_cocycle_set [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) (c : ι → ℝ)
    (hphase : Summable (phase θ q)) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (k : ℤ) x, rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        cocycle θ q c (k + n) x =
          cocycle θ q c n (rotate θ k x) * cocycle θ q c k x) := by
  obtain ⟨s, hs, hfull, hinv, hfinite⟩ :=
    CircleWeightSupport.exists_invariant_conull_floor_support θ q hq
      (phase θ q) (phase_nonneg θ q) hphase
  refine ⟨s, hs, hfull, hinv, hfinite, ?_⟩
  intro x hx k n
  have hk : HasFiniteSupport
      (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)) := hfinite x hx k
  have hn : HasFiniteSupport (fun i =>
      Int.floor (Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) +
        (n : ℝ) * phase θ q i)) := by
    have h := hfinite (rotate θ k x) ((hinv k x).mpr hx) n
    change HasFiniteSupport (fun i =>
      Int.floor (coordinate q i (rotate θ k x) + (n : ℝ) * phase θ q i)) at h
    simpa only [coordinate_rotate] using h
  simpa only [cocycle, floorCost, coordinate_rotate] using
    FiniteSupportCocycle.exp_tsum_floor_cocycle
      (fun i => coordinate q i x) (phase θ q) c k n hk hn

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_InfiniteRatioCaps
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function
open scoped BigOperators

namespace Invariant233.InfiniteRatioCaps

private theorem summable_finset_mask {I : Type*} [DecidableEq I] (c : I → ℝ) (s : Finset I) :
    Summable (fun i => if i ∈ s then c i else 0) := by
  classical
  apply summable_of_hasFiniteSupport
  apply s.finite_toSet.subset
  intro i hi
  by_contra hn
  change i ∉ s at hn
  exact hi (by simp [hn])

private theorem tsum_finset_mask {I : Type*} [DecidableEq I] (c : I → ℝ) (s : Finset I) :
    (∑' i, if i ∈ s then c i else 0) = ∑ i ∈ s, c i := by
  classical
  rw [tsum_eq_sum (s := s) (by intro i hi; simp [hi])]
  exact Finset.sum_congr rfl (by intro i hi; simp [hi])

theorem ratio_le_exp_exception_sub_crossings {I : Type*}
    (x y t c : I → ℝ) (a s : Finset I)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy01 : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, i ∉ a → x i ≤ y i)
    (hx : HasFiniteSupport (fun i => Int.floor (x i + t i)))
    (hy : HasFiniteSupport (fun i => Int.floor (y i + t i)))
    (hcross : ∀ i ∈ s, x i < 1 - Int.fract (t i) ∧
      1 - Int.fract (t i) ≤ y i) :
    Real.exp (-(∑' i, c i * (Int.floor (y i + t i) : ℝ))) /
      Real.exp (-(∑' i, c i * (Int.floor (x i + t i) : ℝ))) ≤
      Real.exp ((∑ i ∈ a, c i) - ∑ i ∈ s, c i) := by
  classical
  have hsx := FiniteSupportCocycle.summable_weighted_int c hx
  have hsy := FiniteSupportCocycle.summable_weighted_int c hy
  have hbound (i : I) :
      c i * (Int.floor (x i + t i) : ℝ) - c i * (Int.floor (y i + t i) : ℝ) ≤
        (if i ∈ a then c i else 0) - (if i ∈ s then c i else 0) := by
    by_cases his : i ∈ s
    · have hci := hcross i his
      have horder : x i ≤ y i := hci.1.le.trans hci.2
      have hdiff : (Int.floor (y i + t i) : ℝ) -
          (Int.floor (x i + t i) : ℝ) = 1 := by
        exact_mod_cast (FloorCocycle.floor_sub_eq_one_iff
          (hx01 i).1 (hx01 i).2 (hy01 i).1 (hy01 i).2 horder (t i)).mpr hci
      simp only [ite_eq_left his]
      by_cases hia : i ∈ a
      · simp only [ite_eq_left hia]
        nlinarith [hc i]
      · simp only [ite_eq_right hia]
        nlinarith [hc i]
    · by_cases hia : i ∈ a
      · have hdiff : (Int.floor (x i + t i) : ℝ) -
            (Int.floor (y i + t i) : ℝ) ≤ 1 := by
          exact_mod_cast (FloorCocycle.floor_sub_bounds
            (hy01 i).1 (hy01 i).2 (hx01 i).1 (hx01 i).2 (t i)).2
        simp only [ite_eq_left hia, ite_eq_right his, sub_zero]
        have := mul_le_mul_of_nonneg_left hdiff (hc i)
        nlinarith
      · have hfloor : (Int.floor (x i + t i) : ℝ) ≤
            (Int.floor (y i + t i) : ℝ) := by
          apply Int.cast_le.mpr
          apply Int.floor_mono
          linarith [hxy i hia]
        simp only [ite_eq_right hia, ite_eq_right his, sub_self]
        exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hfloor (hc i))
  have hsum := (hsx.sub hsy).tsum_le_tsum hbound
    ((summable_finset_mask c a).sub (summable_finset_mask c s))
  rw [hsx.tsum_sub hsy, (summable_finset_mask c a).tsum_sub
    (summable_finset_mask c s), tsum_finset_mask, tsum_finset_mask] at hsum
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

end Invariant233.InfiniteRatioCaps

namespace Invariant233.CircleWeights

theorem cocycle_ratio_cap_with_crossings {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ)
    (x y : UnitAddCircle) (a s : Finset ι)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, i ∉ a → coordinate q i x ≤ coordinate q i y)
    (hx : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)))
    (hy : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i y + (k : ℝ) * phase θ q i)))
    (hcross : ∀ i ∈ s, coordinate q i x < 1 - Int.fract ((k : ℝ) * phase θ q i) ∧
      1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i y) :
    cocycle θ q c k y / cocycle θ q c k x ≤
      Real.exp ((∑ i ∈ a, c i) - ∑ i ∈ s, c i) := by
  exact InfiniteRatioCaps.ratio_le_exp_exception_sub_crossings
    (fun i => coordinate q i x) (fun i => coordinate q i y)
    (fun i => (k : ℝ) * phase θ q i) c a s
    (fun i => coordinate_mem_Ico q i x) (fun i => coordinate_mem_Ico q i y)
    hc hxy hx hy hcross

theorem cocycle_ratio_cap_finite_exceptions {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ)
    (x y : UnitAddCircle) (a : Finset ι)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, i ∉ a → coordinate q i x ≤ coordinate q i y)
    (hx : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)))
    (hy : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i y + (k : ℝ) * phase θ q i))) :
    cocycle θ q c k y / cocycle θ q c k x ≤ Real.exp (∑ i ∈ a, c i) := by
  simpa only [Finset.sum_empty, sub_zero] using
    cocycle_ratio_cap_with_crossings θ q c k x y a ∅ hc hxy hx hy
      (by intro i hi; simp at hi)

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_L2UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Invariant233.EndpointLoss

variable {X ι : Type*} [MeasurableSpace X]

theorem uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X)
    (hfinite : ∀ i, IsFiniteMeasure (ν i)) (H : ℝ)
    (hbound : ∀ i A, MeasurableSet A → (ν i).real A ≤ H * Real.sqrt (μ.real A)) :
    UniformlyAbsolutelyContinuous μ ν := by
  intro ε hε
  have he : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hB : 0 < |H| + 1 := by positivity
  have hd : 0 < (ε : ℝ) / (|H| + 1) := div_pos he hB
  refine ⟨⟨((ε : ℝ) / (|H| + 1)) ^ 2, sq_nonneg _⟩, ?_, ?_⟩
  · change 0 < ((ε : ℝ) / (|H| + 1)) ^ 2
    positivity
  · intro A hA hsmall i
    let := hfinite i
    have hreal : μ.real A < ((ε : ℝ) / (|H| + 1)) ^ 2 := by
      exact (ENNReal.toReal_lt_toReal (measure_ne_top μ A) ENNReal.coe_ne_top).2 hsmall
    have hsqrt : Real.sqrt (μ.real A) < (ε : ℝ) / (|H| + 1) := by
      have ht := Real.sqrt_lt_sqrt (measureReal_nonneg) hreal
      simpa only [Real.sqrt_sq hd.le] using ht
    have hH : H ≤ |H| + 1 := by linarith [le_abs_self H]
    have hν : (ν i).real A < (ε : ℝ) := calc
      (ν i).real A ≤ H * Real.sqrt (μ.real A) := hbound i A hA
      _ ≤ (|H| + 1) * Real.sqrt (μ.real A) :=
        mul_le_mul_of_nonneg_right hH (Real.sqrt_nonneg _)
      _ < (|H| + 1) * ((ε : ℝ) / (|H| + 1)) :=
        mul_lt_mul_of_pos_left hsqrt hB
      _ = (ε : ℝ) := mul_div_cancel₀ _ hB.ne'
    exact (ENNReal.toReal_lt_toReal (measure_ne_top (ν i) A) ENNReal.coe_ne_top).1 hν

theorem uniformlyAbsolutelyContinuous_withDensity
    (μ : Measure X) [IsFiniteMeasure μ] (h : ι → X → ℝ)
    (hh : ∀ i, MemLp (h i) 2 μ) (hn : ∀ i, 0 ≤ᵐ[μ] h i) (H : ℝ)
    (hb : ∀ i, Real.sqrt (∫ x, h i x ^ 2 ∂μ) ≤ H) :
    UniformlyAbsolutelyContinuous μ
      (fun i => μ.withDensity (fun x => ENNReal.ofReal (h i x))) := by
  have hfin : ∀ i, IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isFiniteMeasure_withDensity_ofReal ((hh i).integrable (by norm_num)).2
  apply uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound μ _ hfin H
  intro i A hA
  exact (withDensity_measureReal_le_sqrt μ (hh i) (hn i) hA).trans
    (mul_le_mul_of_nonneg_right (hb i) (Real.sqrt_nonneg _))

theorem uniformlyAbsolutelyContinuous_Lp_withDensity
    (μ : Measure X) [IsFiniteMeasure μ] (f : ι → Lp ℝ 2 μ)
    (hn : ∀ i, 0 ≤ᵐ[μ] (f i : X → ℝ)) (H : ℝ) (hb : ∀ i, ‖f i‖ ≤ H) :
    UniformlyAbsolutelyContinuous μ
      (fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x))) := by
  apply uniformlyAbsolutelyContinuous_withDensity μ (fun i => f i) (fun i => Lp.memLp (f i)) hn H
  intro i
  simpa only [sqrt_integral_sq_eq_norm] using hb i

theorem uniformlyAbsolutelyContinuous_of_Lp_densities
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X) (H : ℝ)
    (hν : ∀ i, ∃ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] (f : X → ℝ)) ∧
      ν i = μ.withDensity (fun x => ENNReal.ofReal (f x)) ∧ ‖f‖ ≤ H) :
    UniformlyAbsolutelyContinuous μ ν := by
  choose f hn heq hb using hν
  have hfun : ν = fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x)) :=
    funext heq
  rw [hfun]
  exact uniformlyAbsolutelyContinuous_Lp_withDensity μ f hn H hb

end Invariant233.EndpointLoss

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_LimitLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Invariant233

theorem map_eq_of_ae_limits_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {Z : Ω → ℝ} {W : Ω' → ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ) (hY : ∀ n, AEMeasurable (Y n) ν)
    (hZ : AEMeasurable Z μ) (hW : AEMeasurable W ν)
    (hXZ : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    (hYW : ∀ᵐ ω ∂ν, Tendsto (fun n => Y n ω) atTop (𝓝 (W ω)))
    (hXY : ∀ n, μ.map (X n) = ν.map (Y n)) : μ.map Z = ν.map W := by
  have h₁ := tendstoInDistribution_of_ae_tendsto hX hZ hXZ
  have h₂ := tendstoInDistribution_of_ae_tendsto hY hW hYW
  have h₃ : TendstoInDistribution X atTop W (fun _ => μ) ν :=
    { forall_aemeasurable := hX
      aemeasurable_limit := hW
      tendsto := by simpa only [hXY] using h₂.tendsto }
  exact tendstoInDistribution_unique X h₁ h₃

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformQuantization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformQuantization

theorem quantize_eq_iff {q : ℕ} [NeZero q] (a : Fin q) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) :
    quantize q x = a ↔ x ∈ Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hnonneg : 0 ≤ (q : ℝ) * x := mul_nonneg hq.le hx.1
  have hfloor : ⌊(q : ℝ) * x⌋₊ < q := (Nat.floor_lt hnonneg).mpr (by nlinarith [hx.2])
  change (⟨⌊(q : ℝ) * x⌋₊ % q, _⟩ : Fin q) = a ↔ _
  rw [Fin.ext_iff]
  change (⌊(q : ℝ) * x⌋₊ % q = a.val) ↔ _
  rw [Nat.mod_eq_of_lt hfloor, Nat.floor_eq_iff hnonneg]
  simp only [mem_Ico]
  constructor
  · intro h
    exact ⟨(div_le_iff₀ hq).mpr (by nlinarith [h.1]),
      (lt_div_iff₀ hq).mpr (by nlinarith [h.2])⟩
  · intro h
    constructor
    · have := (div_le_iff₀ hq).mp h.1
      nlinarith
    · have := (lt_div_iff₀ hq).mp h.2
      nlinarith

theorem preimage_singleton_inter_unit {q : ℕ} [NeZero q] (a : Fin q) :
    (quantize q ⁻¹' {a}) ∩ Ico (0 : ℝ) 1 =
      Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  ext x
  constructor
  · rintro ⟨hxa, hx⟩
    exact (quantize_eq_iff a hx).mp hxa
  · intro hx
    have hunit : x ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact (div_nonneg (by positivity) hq.le).trans hx.1
      · have ha : (a : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt a.isLt
        have hbound : ((a : ℝ) + 1) / q ≤ 1 := (div_le_iff₀ hq).mpr (by linarith)
        exact hx.2.trans_le hbound
    exact ⟨(quantize_eq_iff a hunit).mpr hx, hunit⟩

theorem map_quantize_singleton (q : ℕ) [NeZero q] (a : Fin q) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (quantize q) {a} = (q : ℝ≥0∞)⁻¹ := by
  rw [Measure.map_apply (measurable_quantize q) (measurableSet_singleton a),
    Measure.restrict_apply ((measurable_quantize q) (measurableSet_singleton a)),
    preimage_singleton_inter_unit, Real.volume_Ico]
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have heq : ((a : ℝ) + 1) / q - (a : ℝ) / q = 1 / q := by ring
  rw [heq, ENNReal.ofReal_div_of_pos hq]
  simp

theorem map_quantize_uniform (q : ℕ) [NeZero q] :
    (volume.restrict (Ico (0 : ℝ) 1)).map (quantize q) =
      (PMF.uniformOfFintype (Fin q)).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [map_quantize_singleton]
  simp

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_DigitAveraging
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.DigitAveraging

theorem sq_integral_le_mass_mul_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {u : Ω → ℝ} (hu : Integrable u μ)
    (hu2 : Integrable (fun x => u x ^ 2) μ) (hM : 0 < μ.real univ) :
    (∫ x, u x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, u x ^ 2 ∂μ := by
  let M := μ.real univ
  let A := ∫ x, u x ∂μ
  let a := A / M
  have ha : a * M = A := div_mul_cancel₀ A (ne_of_gt hM)
  have he : (∫ x, (u x - a) ^ 2 ∂μ) =
      (∫ x, u x ^ 2 ∂μ) - 2 * a * A + a ^ 2 * M := by
    have hlin : Integrable (fun x => 2 * a * u x) μ := hu.const_mul _
    have hconst : Integrable (fun _ : Ω => a ^ 2) μ := integrable_const _
    have hpoint : (fun x => (u x - a) ^ 2) =
        (fun x => u x ^ 2 - 2 * a * u x + a ^ 2) := by
      funext x
      ring
    rw [hpoint, integral_add (show Integrable (fun x => u x ^ 2 - 2 * a * u x) μ from hu2.sub hlin) hconst, integral_sub hu2 hlin,
      integral_const_mul, integral_const]
    simp only [smul_eq_mul, Measure.real, M, A]
    ring
  have hnonneg : 0 ≤ ∫ x, (u x - a) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [he, ← ha] at hnonneg
  have hb : a ^ 2 * M ≤ ∫ x, u x ^ 2 ∂μ := by nlinarith
  change A ^ 2 ≤ M * ∫ x, u x ^ 2 ∂μ
  calc
    A ^ 2 = (a * M) ^ 2 := congrArg (fun z : ℝ => z ^ 2) ha.symm
    _ = M * (a ^ 2 * M) := by ring
    _ ≤ M * ∫ x, u x ^ 2 ∂μ := mul_le_mul_of_nonneg_left hb hM.le

theorem sum_integral_fibers {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    {μ : Measure Ω} {f : Ω → α} (hf : Measurable f)
    {u : Ω → ℝ} (hu : Integrable u μ) :
    (∑ a : α, ∫ x in {x | f x = a}, u x ∂μ) = ∫ x, u x ∂μ := by
  have hm : ∀ a : α, MeasurableSet {x | f x = a} :=
    fun a => hf (measurableSet_singleton a)
  have hd : Pairwise (fun a b : α => Disjoint {x | f x = a} {x | f x = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  have hcover : (⋃ a : α, {x | f x = a}) = univ := by
    ext x
    simp
  rw [← integral_iUnion_fintype hm hd (fun _ => hu.integrableOn), hcover,
    Measure.restrict_univ]

theorem digit_averaging_energy_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : MemLp h 2 μ) :
    (1 / (q : ℝ)) * ∑ a : Fin q,
      ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ≤
      ∫ x, (h x - 1) ^ 2 ∂μ := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hhInt : Integrable h μ := hh.integrable (by norm_num)
  have hu : MemLp (fun x => h x - 1) 2 μ := hh.sub (memLp_const 1)
  have huInt : Integrable (fun x => h x - 1) μ := hu.integrable (by norm_num)
  have hu2Int := hu.integrable_sq
  have hlocal : ∀ a : Fin q,
      (1 / (q : ℝ)) * ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ≤
      ∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ := by
    intro a
    have hpos : 0 < (μ.restrict {x | f x = a}).real univ := by
      rw [measureReal_restrict_apply_univ, hmass]
      positivity
    have hcs := sq_integral_le_mass_mul_integral_sq
      huInt.restrict hu2Int.restrict hpos
    rw [measureReal_restrict_apply_univ, hmass] at hcs
    have he : (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1 =
        (q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ) := by
      rw [integral_sub hhInt.restrict (integrable_const 1), setIntegral_const]
      simp only [smul_eq_mul, mul_one, hmass]
      field_simp
    rw [he]
    calc
      (1 / (q : ℝ)) * ((q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ)) ^ 2 =
          (q : ℝ) * (∫ x in {x | f x = a}, h x - 1 ∂μ) ^ 2 := by field_simp
      _ ≤ (q : ℝ) * ((1 / (q : ℝ)) *
          (∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hcs hqR.le
      _ = ∫ x in {x | f x = a}, (h x - 1) ^ 2 ∂μ := by field_simp
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum (fun a _ => hlocal a)).trans_eq
    (sum_integral_fibers hf hu2Int)

theorem digit_average_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℕ} {f : Ω → Fin q} {h : Ω → ℝ}
    (hh : ∀ᵐ x ∂μ, 0 ≤ h x) (a : Fin q) :
    0 ≤ (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) :=
  mul_nonneg (Nat.cast_nonneg q) (integral_nonneg_of_ae (ae_restrict_of_ae hh))

theorem digit_average_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    {h : Ω → ℝ} (hh : Integrable h μ) :
    (1 / (q : ℝ)) * ∑ a : Fin q,
      (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) = ∫ x, h x ∂μ := by
  rw [← Finset.mul_sum, sum_integral_fibers hf hh]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

theorem digit_average_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q}
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : Integrable h μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, h x ≤ B) (a : Fin q) :
    (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) ≤ B := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  calc
    (q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) ≤
        (q : ℝ) * (∫ _x in {x | f x = a}, B ∂μ) :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hh.restrict (integrable_const B) (ae_restrict_of_ae hB)) hqR.le
    _ = B := by
      rw [setIntegral_const, smul_eq_mul, hmass]
      field_simp

theorem map_withDensity_eq_digit_density
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : Integrable h μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ h x) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map f =
      (μ.map f).withDensity (fun a => ENNReal.ofReal
        ((q : ℝ) * ∫ x in {x | f x = a}, h x ∂μ)) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  apply Measure.ext_of_singleton
  intro a
  have hfiber : f ⁻¹' {a} = {x | f x = a} := by ext x; simp
  have hmeas : MeasurableSet {x | f x = a} := hf (measurableSet_singleton a)
  have hmapa : (μ.map f) {a} = ENNReal.ofReal (1 / (q : ℝ)) := by
    rw [Measure.map_apply hf (measurableSet_singleton a), hfiber]
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | f x = a})]
    exact congrArg ENNReal.ofReal (hmass a)
  rw [Measure.map_apply hf (measurableSet_singleton a), hfiber,
    withDensity_apply _ hmeas,
    withDensity_apply _ (measurableSet_singleton a), lintegral_singleton, hmapa,
    ← ofReal_integral_eq_lintegral_ofReal hh.restrict (ae_restrict_of_ae hnonneg)]
  rw [← ENNReal.ofReal_mul (digit_average_nonneg hnonneg a)]
  congr 1
  field_simp

theorem integral_map_eq_uniform_sum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    (g : Fin q → ℝ) :
    (∫ a, g a ∂μ.map f) = (1 / (q : ℝ)) * ∑ a : Fin q, g a := by
  have hg : Integrable g (μ.map f) := by
    exact Integrable.of_finite
  rw [integral_fintype hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hmap : (μ.map f).real {a} = μ.real {x | f x = a} := by
    unfold Measure.real
    rw [Measure.map_apply hf (measurableSet_singleton a)]
    congr 1
  rw [smul_eq_mul, hmap, hmass]

theorem integral_digit_energy_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ} (hq : 0 < q) {f : Ω → Fin q} (hf : Measurable f)
    (hmass : ∀ a : Fin q, μ.real {x | f x = a} = 1 / (q : ℝ))
    {h : Ω → ℝ} (hh : MemLp h 2 μ) :
    (∫ a, ((q : ℝ) * (∫ x in {x | f x = a}, h x ∂μ) - 1) ^ 2 ∂μ.map f) ≤
      ∫ x, (h x - 1) ^ 2 ∂μ := by
  rw [integral_map_eq_uniform_sum hf hmass]
  exact digit_averaging_energy_le hq hf hmass hh

end Invariant233.DigitAveraging

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_QuantizedDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.UniformQuantization

local instance instIsProbabilityMeasureRealRestrictVolumeIcoOfNat_solutions : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) :=
  ⟨by simp⟩

theorem quantize_fiber_mass (q : ℕ) [NeZero q] (a : Fin q) :
    (volume.restrict (Ico (0 : ℝ) 1)).real {x | quantize q x = a} =
      1 / (q : ℝ) := by
  have hmass := map_quantize_singleton q a
  rw [Measure.map_apply (measurable_quantize q) (measurableSet_singleton a)] at hmass
  unfold Measure.real
  rw [show (volume.restrict (Ico (0 : ℝ) 1)) {x | quantize q x = a} =
      (q : ℝ≥0∞)⁻¹ from hmass]
  simp [one_div]

theorem map_withDensity_quantize (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1)))
    (hnonneg : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), 0 ≤ h x) :
    ((volume.restrict (Ico (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (h x))).map
      (quantize q) =
      (PMF.uniformOfFintype (Fin q)).toMeasure.withDensity
        (fun a => ENNReal.ofReal (binAverage q h a)) := by
  simpa only [map_quantize_uniform, binAverage] using
    DigitAveraging.map_withDensity_eq_digit_density (Nat.pos_of_ne_zero (NeZero.ne q))
      (measurable_quantize q) (quantize_fiber_mass q) hh hnonneg

theorem integral_binAverage_energy_le (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : MemLp h 2 (volume.restrict (Ico (0 : ℝ) 1))) :
    (∫ a, (binAverage q h a - 1) ^ 2 ∂(PMF.uniformOfFintype (Fin q)).toMeasure) ≤
      ∫ x, (h x - 1) ^ 2 ∂volume.restrict (Ico (0 : ℝ) 1) := by
  simpa only [map_quantize_uniform, binAverage] using
    DigitAveraging.integral_digit_energy_le (Nat.pos_of_ne_zero (NeZero.ne q))
      (measurable_quantize q) (quantize_fiber_mass q) hh

theorem binAverage_nonneg (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), 0 ≤ h x) (a : Fin q) :
    0 ≤ binAverage q h a := DigitAveraging.digit_average_nonneg hh a

theorem integral_binAverage (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1))) :
    (∫ a, binAverage q h a ∂(PMF.uniformOfFintype (Fin q)).toMeasure) =
      ∫ x, h x ∂volume.restrict (Ico (0 : ℝ) 1) := by
  rw [← map_quantize_uniform q,
    DigitAveraging.integral_map_eq_uniform_sum (measurable_quantize q) (quantize_fiber_mass q)]
  exact DigitAveraging.digit_average_mean (Nat.pos_of_ne_zero (NeZero.ne q))
    (measurable_quantize q) hh

theorem binAverage_le (q : ℕ) [NeZero q] {h : ℝ → ℝ} {B : ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1)))
    (hB : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), h x ≤ B) (a : Fin q) :
    binAverage q h a ≤ B :=
  DigitAveraging.digit_average_le (Nat.pos_of_ne_zero (NeZero.ne q))
    (quantize_fiber_mass q) hh hB a

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal NNReal

namespace Invariant233.UniformlyAbsolutelyContinuous

variable {X ι : Type*} [MeasurableSpace X]

theorem absolutelyContinuous {μ : Measure X} {ν : ι → Measure X}
    (h : UniformlyAbsolutelyContinuous μ ν) (i : ι) : ν i ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨δ, hδ, hbound⟩ := h ε hε
  have hsmall : μ s < (δ : ℝ≥0∞) := by
    rw [hzero]
    exact_mod_cast hδ
  simpa only [bot_eq_zero, zero_add] using (hbound s hs hsmall i).le

end Invariant233.UniformlyAbsolutelyContinuous

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterBlocks
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.CircleParameterData

theorem block_index_unique (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j k i : ℕ}
    (hij : i ∈ p.block j) (hik : i ∈ p.block k) : j = k := by
  have hj := (p.mem_block_iff j i).mp hij
  have hk := (p.mem_block_iff k i).mp hik
  have hmono := (p.blockEnd_strictMono hm).monotone
  apply le_antisymm
  · by_contra h
    have hjk : k ≤ j - 1 := by omega
    have hd := hmono hjk
    omega
  · by_contra h
    have hjk : j ≤ k - 1 := by omega
    have hd := hmono hjk
    omega

end Invariant233.CircleParameterData

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadix
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem sum_terms_le_reciprocal_gap {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j N : ℕ) :
    (∑ n ∈ Finset.range N, term d (j + n)) ≤
      1 / (denominator r j : ℝ) - 1 / (denominator r (j + N) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hterm := term_le_reciprocal_gap hr d (j + N)
      simp only [Nat.add_assoc] at hterm
      linarith

theorem summable_terms {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    Summable (term d) := by
  apply summable_of_sum_range_le (term_nonneg d) (c := 1)
  intro N
  have h := sum_terms_le_reciprocal_gap hr d 0 N
  simp only [Nat.zero_add, denominator_zero, Nat.cast_one, div_one] at h
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r N : ℝ) := by positivity
  linarith

theorem tsum_tail_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    (∑' n, term d (j + n)) ≤ 1 / (denominator r j : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun n => term_nonneg d (j + n))
  intro N
  have h := sum_terms_le_reciprocal_gap hr d j N
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r (j + N) : ℝ) := by positivity
  linarith

theorem ofDigits_nonneg {r : ℕ → ℕ} (d : Digits r) : 0 ≤ ofDigits d :=
  tsum_nonneg (term_nonneg d)

theorem tailValue_nonneg {r : ℕ → ℕ} (d : Digits r) (j : ℕ) :
    0 ≤ tailValue d j := by
  unfold tailValue
  exact mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun n => term_nonneg d (j + n)))

theorem tailValue_le_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j ≤ 1 := by
  have hq : (0 : ℝ) < denominator r j := by exact_mod_cast denominator_pos hr j
  calc
    tailValue d j ≤ (denominator r j : ℝ) * (1 / (denominator r j : ℝ)) :=
      mul_le_mul_of_nonneg_left (tsum_tail_le hr d j) hq.le
    _ = 1 := by field_simp

theorem tailValue_mono {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) {d e : Digits r}
    (hde : ∀ n, d n ≤ e n) (j : ℕ) : tailValue d j ≤ tailValue e j := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply ((summable_terms hr d).comp_injective (fun _ _ h => Nat.add_left_cancel h)).tsum_le_tsum
    _ ((summable_terms hr e).comp_injective (fun _ _ h => Nat.add_left_cancel h))
  intro n
  exact div_le_div_of_nonneg_right (by exact_mod_cast hde (j + n)) (Nat.cast_nonneg _)

theorem tailValue_rec {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j = ((d j : ℝ) + tailValue d (j + 1)) / (r j : ℝ) := by
  have hs : Summable (fun n => term d (j + (n + 1))) :=
    (summable_terms hr d).comp_injective (fun _ _ h => by omega)
  have hsplit : (∑' n, term d (j + n)) =
      term d j + ∑' n, term d (j + 1 + n) := by
    simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using tsum_eq_zero_add' (f := fun n => term d (j + n)) hs
  have hq : (denominator r j : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast denominator_pos hr j)
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  unfold tailValue
  rw [hsplit]
  simp only [term, denominator_succ, Nat.cast_mul]
  field_simp

theorem ofDigits_eq_prefix_add_tail {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    ofDigits d = (∑ n ∈ Finset.range N, term d n) + ∑' n, term d (N + n) := by
  simpa only [ofDigits, Nat.add_comm] using
    ((summable_terms hr d).sum_add_tsum_nat_add N).symm

theorem reciprocal_denominator_tendsto_zero {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Tendsto (fun n => 1 / (denominator r n : ℝ)) atTop (𝓝 0) :=
  (summable_reciprocal_denominator hr).tendsto_atTop_zero

theorem denominator_mul_prefix {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * (∑ n ∈ Finset.range N, term d n) = (prefixRank d N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hq : (denominator r N : ℝ) ≠ 0 :=
        ne_of_gt (by exact_mod_cast denominator_pos hr N)
      have hrr : (r N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr N)
      rw [Finset.sum_range_succ, prefixRank_succ, Nat.cast_add, Nat.cast_mul]
      simp only [term, denominator_succ, Nat.cast_mul] at *
      field_simp at *
      nlinarith

theorem denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * ofDigits d = (prefixRank d N : ℝ) + tailValue d N := by
  rw [ofDigits_eq_prefix_add_tail hr d N, mul_add, denominator_mul_prefix hr d N]
  rfl

theorem tailValue_eq_one_imp_next {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) (heq : tailValue d j = 1) :
    tailValue d (j + 1) = 1 := by
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d j)
  have hd : (d j : ℝ) + 1 ≤ (r j : ℝ) := by exact_mod_cast (d j).isLt
  rw [heq, one_mul] at hrec
  linarith [tailValue_le_one hr d (j + 1)]

theorem tailValue_lt_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) : tailValue d j < 1 := by
  by_contra hnot
  have heq : tailValue d j = 1 := le_antisymm (tailValue_le_one hr d j) (le_of_not_gt hnot)
  have hprop : ∀ k, tailValue d (j + k) = 1 := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ k ih =>
        simpa only [Nat.add_assoc] using tailValue_eq_one_imp_next hr d (j + k) ih
  obtain ⟨n, hjn, hn⟩ := hnt j
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjn
  have hrr : (r (j + k) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr (j + k))
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d (j + k))
  rw [hprop k, one_mul] at hrec
  have hd : (d (j + k) : ℝ) + 1 < (r (j + k) : ℝ) := by exact_mod_cast hn
  linarith [tailValue_le_one hr d (j + k + 1)]

theorem fract_denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) :
    Int.fract ((denominator r j : ℝ) * ofDigits d) = tailValue d j := by
  rw [denominator_mul_ofDigits hr d j, Int.fract_natCast_add]
  exact Int.fract_eq_self.mpr ⟨tailValue_nonneg d j, tailValue_lt_one hr d hnt j⟩

theorem canonical_prefix_error {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) (N : ℕ) :
    0 ≤ x - (∑ n ∈ Finset.range N, term (canonicalDigits r hr x) n) ∧
    x - (∑ n ∈ Finset.range N, term (canonicalDigits r hr x) n) <
      1 / (denominator r N : ℝ) := by
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hgrid := denominator_mul_prefix hr (canonicalDigits r hr x) N
  rw [prefixRank_canonicalDigits hr hx N] at hgrid
  have hlow := Nat.floor_le (mul_nonneg hq.le hx.1)
  have hhigh := Nat.lt_floor_add_one ((denominator r N : ℝ) * x)
  constructor
  · nlinarith
  · apply (lt_div_iff₀ hq).mpr
    nlinarith

theorem ofDigits_canonicalDigits {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    ofDigits (canonicalDigits r (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)) x) = x := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  let d := canonicalDigits r hp x
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, term d n) atTop (𝓝 x) := by
    have hzero : Tendsto (fun N => x - ∑ n ∈ Finset.range N, term d n) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (reciprocal_denominator_tendsto_zero hr)
      · intro N; exact (canonical_prefix_error hp hx N).1
      · intro N; exact (canonical_prefix_error hp hx N).2.le
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hzero
    simpa using h
  have hs := (summable_terms hp d).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hs hlim

theorem measurable_canonicalDigits (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    Measurable (canonicalDigits r hr) := by
  apply Measurable.of_eval
  intro n
  exact (measurable_of_countable (fun k : ℕ =>
    (⟨k % r n, Nat.mod_lt _ (hr n)⟩ : Fin (r n)))).comp
      ((measurable_const.mul measurable_id).nat_floor)

theorem ofDigits_mem_Ico {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) : ofDigits d ∈ Set.Ico 0 1 := by
  refine ⟨ofDigits_nonneg d, ?_⟩
  simpa [tailValue, ofDigits] using tailValue_lt_one hr d hnt 0

theorem floor_denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (N : ℕ) :
    ⌊(denominator r N : ℝ) * ofDigits d⌋₊ = prefixRank d N := by
  apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) (ofDigits_nonneg d))).mpr
  rw [denominator_mul_ofDigits hr d N]
  constructor
  · linarith [tailValue_nonneg d N]
  · linarith [tailValue_lt_one hr d hnt N]

theorem canonicalDigits_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) : canonicalDigits r hr (ofDigits d) = d := by
  funext n
  have hrank := prefixRank_canonicalDigits hr (ofDigits_mem_Ico hr d hnt) (n + 1)
  rw [floor_denominator_mul_ofDigits hr d hnt (n + 1)] at hrank
  exact (prefixRank_eq_iff hr _ _ (n + 1)).mp hrank n (Nat.lt_succ_self n)

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem denominator_radices {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hdiv : ∀ n, q n ∣ q (n + 1)) (N : ℕ) : denominator (radices q) N = q N := by
  induction N with
  | zero => simpa using hq0.symm
  | succ N ih =>
      rw [denominator_succ, ih, radices]
      exact Nat.mul_div_cancel' (hdiv N)

theorem radices_pos {q : ℕ → ℕ} (hq : ∀ n, 0 < q n)
    (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1)) (n : ℕ) :
    0 < radices q n := lt_of_lt_of_le (by decide) (radices_ge_two hq hstrict hdiv n)

theorem coordinate_eq_tailValue {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hq : ∀ n, 0 < q n) (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1))
    (d : Digits (radices q)) (hnt : Nonterminal d) (i : ℕ) :
    Int.fract ((q i : ℝ) * ofDigits d) = tailValue d i := by
  rw [← denominator_radices hq0 hdiv i]
  exact fract_denominator_mul_ofDigits (radices_pos hq hstrict hdiv) d hnt i

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingParameters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coupling_K_ge (j : ℕ) (hj : 1 ≤ j) : 100 ≤ p.K j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n with
  | zero => simpa using hp.initial_K.ge
  | succ n ih =>
    have h := hp.K_double (1 + n) (by omega)
    have he : 1 + (n + 1) = 1 + n + 1 := by omega
    rw [he]
    omega

lemma coupling_radix_ge_N {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    p.N s ≤ (MixedRadix.radices p.q i : ℝ) := by
  simpa only [MixedRadix.radices, Nat.cast_div (hp.frequency_divisible i)
    (by exact_mod_cast (Nat.ne_of_gt (hp.q_pos i)) : (p.q i : ℝ) ≠ 0)] using hp.frequency_ratios s hs i hi

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMarginalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.CouplingMarginalBounds

lemma rho_div_width_le {κ m w : ℝ} (hκ : 0 ≤ κ)
    (hm : 0 < m) (hw : 1 / m ≤ w) : rho κ m w / w ≤ κ := by
  exact (div_le_iff₀ (width_pos hm hw)).2 (rho_le_mul_width hκ hm hw)

lemma rho_sq_div_width {κ m w : ℝ} (hm : 0 < m) (hw : 0 < w) :
    (rho κ m w) ^ 2 / w = κ ^ 2 / m := by
  unfold rho
  rw [mul_pow, Real.sq_sqrt (div_nonneg hw.le hm.le)]
  field_simp

lemma integral_sq_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂μ := by
  classical
  have hsum : MemLp (fun ω => ∑ i, f i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hf i)
  have hsq : Integrable (fun ω => ∑ i, (f i ω) ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hf i).integrable_sq)
  calc
    _ ≤ ∫ ω, (Fintype.card I : ℝ) * ∑ i, (f i ω) ^ 2 ∂μ := by
      apply integral_mono hsum.integrable_sq (hsq.const_mul _)
      intro ω
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => f i ω))
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      intro i _
      exact (hf i).integrable_sq

lemma integral_sq_weighted_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    (p : I → ℝ) :
    (∫ ω, (∑ i, p i * f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, (p i) ^ 2 * ∫ ω, (f i ω) ^ 2 ∂μ := by
  have h := integral_sq_sum_le (fun i => (hf i).const_mul (p i))
  simpa only [mul_pow, integral_const_mul] using h

lemma uniformDensity_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (p : ℝ≥0∞) : MemLp (uniformDensity μ s) p μ := by
  exact memLp_indicator_const p hs _ (Or.inr (measure_ne_top μ s))

lemma uniformDensity_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, uniformDensity μ s ω ∂μ = 1 := by
  rw [uniformDensity, integral_indicator_const _ hs, smul_eq_mul]
  exact mul_inv_cancel₀ hpos.ne'

lemma uniformDensity_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω) ^ 2 ∂μ = (μ.real s)⁻¹ := by
  have hsq : (fun ω => (uniformDensity μ s ω) ^ 2) =
      s.indicator (fun _ => ((μ.real s)⁻¹) ^ 2) := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [uniformDensity, hω]
  rw [hsq, integral_indicator_const _ hs, smul_eq_mul]
  field_simp

lemma uniformDensity_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ = (μ.real s)⁻¹ - 1 := by
  have hu := uniformDensity_memLp (μ := μ) hs 2
  have hui : Integrable (uniformDensity μ s) μ := hu.integrable (by norm_num)
  have hfun : (fun ω => (uniformDensity μ s ω - 1) ^ 2) =
      fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω + 1 := by
    ext ω
    ring
  have hsub : Integrable (fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω) μ :=
    hu.integrable_sq.sub (hui.const_mul 2)
  rw [hfun, integral_add hsub (integrable_const 1),
    integral_sub hu.integrable_sq (hui.const_mul 2), integral_const_mul,
    uniformDensity_sq_integral hs hpos, uniformDensity_integral hs hpos]
  simp
  ring

lemma uniformDensity_variance_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) {w : ℝ} (hw : 0 < w) (hlen : w / 2 ≤ μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ ≤ 2 / w := by
  have hpos : 0 < μ.real s := lt_of_lt_of_le (by positivity) hlen
  rw [uniformDensity_variance hs hpos]
  have hinv : (μ.real s)⁻¹ ≤ 2 / w := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hpos hw).2
    linarith
  linarith

end Invariant233.CouplingMarginalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

lemma diagonal_fst (μ : Measure X) : (diagonal μ).fst = μ := by
  simpa [diagonal] using
    (Measure.fst_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma diagonal_snd (μ : Measure X) : (diagonal μ).snd = μ := by
  simpa [diagonal] using
    (Measure.snd_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma fst_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).fst = ∑ i ∈ s, (μ i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma snd_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).snd = ∑ i ∈ s, (μ i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma mixture_fst (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).fst = q • μ + ∑ i, p i • u i := by
  unfold mixture
  rw [Measure.fst_add, fst_finsetSum]
  simp only [Measure.fst, Measure.map_smul,
    Measure.map_fst_prod, measure_univ, one_smul]
  rw [← Measure.fst, diagonal_fst]

lemma mixture_snd (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).snd = q • μ + ∑ i, p i • v i := by
  unfold mixture
  rw [Measure.snd_add, snd_finsetSum]
  simp only [Measure.snd, Measure.map_smul,
    Measure.map_snd_prod, measure_univ, one_smul]
  rw [← Measure.snd, diagonal_snd]

lemma withDensity_finite_mixture (μ : Measure X) (q : ℝ≥0∞)
    (p : I → ℝ≥0∞) (g : I → X → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    μ.withDensity (fun x => q + ∑ i, p i * g i x) =
      q • μ + ∑ i, p i • μ.withDensity (g i) := by
  classical
  have hsum : μ.withDensity (fun x => ∑ i, p i * g i x) =
      ∑ i, p i • μ.withDensity (g i) := by
    have hfin : ∀ s : Finset I, μ.withDensity (fun x => ∑ i ∈ s, p i * g i x) =
        ∑ i ∈ s, p i • μ.withDensity (g i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [show (fun x => p a * g a x + ∑ i ∈ s, p i * g i x) =
          (fun x => p a * g a x) + (fun x => ∑ i ∈ s, p i * g i x) from rfl,
          withDensity_add_left (show Measurable (fun x => p a * g a x) from measurable_const.mul (hg a)), ih]
        congr 1
        exact withDensity_smul (p a) (hg a)
    exact hfin Finset.univ
  rw [show (fun x => q + ∑ i, p i * g i x) =
    (fun _ => q) + (fun x => ∑ i, p i * g i x) from rfl,
    withDensity_add_left measurable_const, withDensity_const, hsum]

lemma intervalLaw_ae_mem (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ico a b :=
  ae_cond_mem measurableSet_Ico

lemma intervalLaw_pair_ordered {a b c d : ℝ} (hbc : b ≤ c) :
    ∀ᵐ z ∂(intervalLaw a b).prod (intervalLaw c d), z.1 ≤ z.2 := by
  have : IsZeroOrProbabilityMeasure (intervalLaw a b) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico a b]))
  have : IsZeroOrProbabilityMeasure (intervalLaw c d) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico c d]))
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_fst measurable_snd)]
  filter_upwards [intervalLaw_ae_mem a b] with x hx
  filter_upwards [intervalLaw_ae_mem c d] with y hy
  exact hx.2.le.trans (hbc.trans hy.1)

lemma cond_eq_withDensity_uniformDensity {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    μ[|s] = μ.withDensity (fun x =>
      ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) := by
  have hc : ENNReal.ofReal ((μ.real s)⁻¹) = (μ s)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpos, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ s)]
  have hfun : (fun x => ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) =
      s.indicator (fun _ => (μ s)⁻¹) := by
    ext x
    by_cases hx : x ∈ s <;> simp [CouplingMarginalBounds.uniformDensity, hx, hc]
  rw [hfun, withDensity_indicator hs, withDensity_const]
  rfl

omit [MeasurableSpace X] in
lemma ofReal_mixture_density (q : ℝ) (p : I → ℝ) (g : I → X → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hg : ∀ i x, 0 ≤ g i x) (x : X) :
    ENNReal.ofReal (q + ∑ i, p i * g i x) =
      ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (g i x) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hp i))

lemma mixture_fst_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hu : ∀ i, u i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).fst =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_fst]
  simp_rw [hu, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

lemma mixture_snd_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hv : ∀ i, v i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).snd =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_snd]
  simp_rw [hv, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma replacement_ae_ordered {m a b : ℝ} (hm : 2 ≤ m) (i : Fin 5) :
    ∀ᵐ z ∂(leftLaw m a b i).prod (rightLaw m a b i), z.1 ≤ z.2 := by
  have hm0 : 0 < m := by linarith
  have hinv : 1 / m ≤ 1 / 2 := by
    apply (div_le_iff₀ hm0).2
    linarith
  fin_cases i <;>
    simp only [leftLaw, rightLaw]
  all_goals apply intervalLaw_pair_ordered
  all_goals linarith

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma interval_subset_unit {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Ico a b ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

lemma baseLaw_interval_measure {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    baseLaw.real (Ico a b) = b - a := by
  rw [measureReal_def, baseLaw_eq_restrict, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma intervalLaw_eq_base_cond {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    intervalLaw a b = baseLaw[|Ico a b] := by
  rw [baseLaw_eq_restrict]
  simp only [intervalLaw, ProbabilityTheory.cond,
    Measure.restrict_apply measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb)]

lemma intervalLaw_eq_base_withDensity {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    intervalLaw a b = baseLaw.withDensity (fun x =>
      ENNReal.ofReal (uniformDensity baseLaw (Ico a b) x)) := by
  rw [intervalLaw_eq_base_cond ha hb]
  apply cond_eq_withDensity_uniformDensity measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_OneCoordinateDensity
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma intervalDensity_measurable (a b : ℝ) : Measurable (intervalDensity a b) :=
  measurable_const.indicator measurableSet_Ico

lemma intervalDensity_nonneg (a b x : ℝ) : 0 ≤ intervalDensity a b x := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (measureReal_nonneg)]
  · simp [intervalDensity, uniformDensity, hx]

lemma intervalDensity_memLp (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (intervalDensity a b) p baseLaw :=
  uniformDensity_memLp measurableSet_Ico p

lemma intervalDensity_variance {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) = (b - a)⁻¹ - 1 := by
  have hpos : 0 < baseLaw.real (Ico a b) := by
    rw [baseLaw_interval_measure ha hb hab.le]
    exact sub_pos.mpr hab
  rw [intervalDensity, uniformDensity_variance measurableSet_Ico hpos,
    baseLaw_interval_measure ha hb hab.le]

lemma intervalDensity_le_inv_length {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (x : ℝ) :
    intervalDensity a b x ≤ (b - a)⁻¹ := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, baseLaw_interval_measure ha hb hab.le]
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (sub_nonneg.mpr hab.le)]

lemma intervalDensity_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) (x : ℝ) :
    intervalDensity a b x ≤ 2 / w := by
  have hab : a < b := by linarith
  apply (intervalDensity_le_inv_length ha hb hab x).trans
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sub_pos.mpr hab) hw).2
  linarith

lemma leftLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    leftLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftLaw, leftDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma rightLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    rightLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightLaw, rightDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma leftDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ leftDensity m a b i x ∧ leftDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 0) (b := 1 / m)
        (by norm_num) (by linarith) hinv0 x

lemma rightDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ rightDensity m a b i x ∧ rightDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 1 - 1 / m) (b := 1)
        (by linarith) (by norm_num) (by linarith) x

lemma intervalDensity_variance_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) ≤ 2 / w := by
  apply uniformDensity_variance_le measurableSet_Ico hw
  rw [baseLaw_interval_measure ha hb (by linarith)]
  exact hlen

lemma leftDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (leftDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity 0 (1 / m) x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by norm_num) (by linarith) hinv0]
    simp

lemma rightDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (rightDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity (1 - 1 / m) 1 x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by linarith) (by norm_num) (by linarith)]
    simp

lemma marginalDensity_sub_one (κ m a b t : ℝ) (d : Fin 5 → ℝ) :
    diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * d i - 1 =
      ∑ i, componentProbabilities κ m a b t i * (d i - 1) := by
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitGeometry
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace Invariant233.CircleDigitCoupling

lemma bin_subset_unit {r : ℕ} [NeZero r] (d : Fin r) :
    bin r d ⊆ Ico (0 : ℝ) 1 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  intro x hx
  have hd : (d : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt d.isLt
  exact ⟨(div_nonneg (by positivity) hr.le).trans hx.1,
    hx.2.trans_le ((div_le_iff₀ hr).mpr (by simpa using hd))⟩

lemma bin_length {r : ℕ} (d : Fin r) :
    ((d : ℝ) + 1) / r - (d : ℝ) / r = 1 / r := by ring

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleDigitCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma baseLaw_bin {r : ℕ} [NeZero r] (d : Fin r) :
    baseLaw (bin r d) = (r : ℝ≥0∞)⁻¹ := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  rw [baseLaw_eq_restrict, Measure.restrict_apply (show MeasurableSet (bin r d) from measurableSet_Ico),
    inter_eq_left.mpr (bin_subset_unit d)]
  rw [bin, Real.volume_Ico, bin_length]
  rw [ENNReal.ofReal_div_of_pos hr]
  simp

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hm ha ha' hb hb' in
lemma endpointLaw_isProbabilityMeasure (side : Bool) (l : Label) :
    IsProbabilityMeasure (endpointLaw side m a b l) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  cases l with
  | none => exact baseLaw_isProbabilityMeasure
  | some i =>
    cases side
    · exact leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb' i
    · exact rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb' i

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitDensity
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hm ha ha' hb hb' in
lemma endpointLaw_eq_density (side : Bool) (l : Label) :
    endpointLaw side m a b l = baseLaw.withDensity
      (fun x => ENNReal.ofReal (endpointDensity side m a b l x)) := by
  have hm0 : 0 < m := by linarith
  cases l with
  | none => simp [endpointLaw, endpointDensity]
  | some i =>
    cases side
    · exact leftLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i
    · exact rightLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i

lemma endpointDensity_measurable (side : Bool) (m a b : ℝ) (l : Label) :
    Measurable (endpointDensity side m a b l) := by
  cases l with
  | none => exact measurable_const
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_measurable _ _

lemma endpointDensity_nonneg (side : Bool) (m a b : ℝ) (l : Label) (x : ℝ) :
    0 ≤ endpointDensity side m a b l x := by
  cases l with
  | none => norm_num [endpointDensity]
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_nonneg _ _ _

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma marginalDensity_bounds (side : Bool) (x : ℝ) :
    49 / 50 ≤ marginalDensity side κ m a b t x ∧
      marginalDensity side κ m a b t x ≤ 3 + 8 * κ ∧
      marginalDensity side κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hd (i : Fin 5) : 0 ≤ endpointDensity side m a b (some i) x ∧
      endpointDensity side m a b (some i) x ≤ componentVarianceBounds (2 * m) a b i := by
    cases side
    · exact leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x
    · exact rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x
  have hρa := rho_div_width_le hκ0 hm0 ha
  have hρb := rho_div_width_le hκ0 hm0 hb
  have hρa0 := rho_nonneg (m := m) (w := a) hκ0
  have hρb0 := rho_nonneg (m := m) (w := b) hκ0
  have hq := diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
  have htag0 : 0 ≤ t / m := div_nonneg ht0 hm0.le
  have htag : (t / m) * endpointDensity side m a b (some 4) x ≤ 2 := by
    calc
      _ ≤ (t / m) * (2 * m) := mul_le_mul_of_nonneg_left (hd 4).2 htag0
      _ = 2 * t := by field_simp
      _ ≤ 2 := by linarith
  have hw (w : ℝ) (v : ℝ) (hw0 : 0 < w) (hρ : rho κ m w / w ≤ κ)
      (hv : v ≤ 2 / w) : rho κ m w * v ≤ 2 * κ := by
    calc
      _ ≤ rho κ m w * (2 / w) := mul_le_mul_of_nonneg_left hv (rho_nonneg hκ0)
      _ = 2 * (rho κ m w / w) := by ring
      _ ≤ _ := by linarith
  have h0 := hw a _ ha0 hρa (hd 0).2
  have h1 := hw a _ ha0 hρa (hd 1).2
  have h2 := hw b _ hb0 hρb (hd 2).2
  have h3 := hw b _ hb0 hρb (hd 3).2
  have hp0 (i : Fin 5) : 0 ≤ componentProbabilities κ m a b t i *
      endpointDensity side m a b (some i) x :=
    mul_nonneg (componentProbabilities_nonneg hκ0 hm0 ht0 i) (hd i).1
  have hlo : 49 / 50 ≤ marginalDensity side κ m a b t x := by
    exact hq.1.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hp0 i)))
  have hup : marginalDensity side κ m a b t x ≤ 3 + 8 * κ := by
    unfold marginalDensity
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    change diagonalMass κ m a b t + (rho κ m a * endpointDensity side m a b (some 0) x +
      (rho κ m a * endpointDensity side m a b (some 1) x +
      (rho κ m b * endpointDensity side m a b (some 2) x +
      (rho κ m b * endpointDensity side m a b (some 3) x +
      t / m * endpointDensity side m a b (some 4) x)))) ≤ _
    linarith [hq.2]
  exact ⟨hlo, hup, by linarith⟩

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma ofReal_marginalDensity (side : Bool) (x : ℝ) :
    ENNReal.ofReal (marginalDensity side κ m a b t x) =
      labelMass κ m a b t none + ∑ i : Fin 5,
        labelMass κ m a b t (some i) *
          ENNReal.ofReal (endpointDensity side m a b (some i) x) := by
  have hm0 : 0 < m := by linarith
  apply ofReal_mixture_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i y
    exact endpointDensity_nonneg side m a b (some i) y

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_eq_integral (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) =
      ∫⁻ x in bin r d, ENNReal.ofReal (marginalDensity side κ m a b t x) ∂baseLaw := by
  have h := withDensity_finite_mixture baseLaw (labelMass κ m a b t none)
    (fun i : Fin 5 => labelMass κ m a b t (some i))
    (fun i x => ENNReal.ofReal (endpointDensity side m a b (some i) x))
    (fun i => (endpointDensity_measurable side m a b (some i)).ennreal_ofReal)
  simp_rw [← ofReal_marginalDensity hκ0 hκ hm ha ha' hb hb' ht0 ht side] at h
  have heval := congrArg (fun ν : Measure ℝ => ν (bin r d)) h
  rw [withDensity_apply _ (show MeasurableSet (bin r d) from measurableSet_Ico)] at heval
  rw [heval, Fintype.sum_option]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← endpointLaw_eq_density hm ha ha' hb hb' side (some i)]
  rfl

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_le_ten (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≤ 10 * baseLaw (bin r d) := by
  rw [digitWeight_total_eq_integral hκ0 hκ hm ha ha' hb hb' ht0 ht]
  calc
    _ ≤ ∫⁻ _x in bin r d, (10 : ℝ≥0∞) ∂baseLaw := by
      apply lintegral_mono
      intro x
      exact le_trans (ENNReal.ofReal_le_ofReal
        (marginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht side x).2.2.le)
        (by norm_num)
    _ = _ := by simp

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitDisintegration
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

private lemma map_label_observe {D : Type*} [MeasurableSpace D]
    (ν : Measure (ℝ × ℝ)) [SFinite ν] (l : Label) (f : ℝ × ℝ → D) (hf : Measurable f) :
    (ν.map (fun z => (l, z))).map (fun z : CoordinateSample => (f z.2, z.1)) =
      (ν.map f).prod (Measure.dirac l) := by
  have hin : Measurable (fun z : ℝ × ℝ => (l, z)) := by fun_prop
  have hout : Measurable (fun z : CoordinateSample => (f z.2, z.1)) := by fun_prop
  rw [Measure.map_map hout hin, Measure.prod_dirac]
  rw [Measure.map_map (show Measurable (fun x : D => (x, l)) from by fun_prop) hf]
  rfl

private lemma observed_pair_left {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [SFinite ν] [IsProbabilityMeasure η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.1) = ν.map Q := by
  change (ν.prod η).map (Q ∘ Prod.fst) = _
  rw [← Measure.map_map hQ measurable_fst, Measure.map_fst_prod]
  simp

private lemma observed_pair_right {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [IsProbabilityMeasure ν] [SFinite η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.2) = η.map Q := by
  change (ν.prod η).map (Q ∘ Prod.snd) = _
  rw [← Measure.map_map hQ measurable_snd, Measure.map_snd_prod]
  simp

variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma endpointLaw_ae_unit (side : Bool) (l : Label) :
    ∀ᵐ x ∂endpointLaw side m a b l, x ∈ Ico (0 : ℝ) 1 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hinv : 1 / (2 * m) ≤ 1 := by apply (div_le_iff₀ (by linarith : 0 < 2 * m)).2; linarith
  have hinv0 : 0 < 1 / (2 * m) := one_div_pos.mpr (by linarith)
  cases l with
  | none => exact intervalLaw_ae_mem 0 1
  | some i =>
    cases side <;> fin_cases i <;> simp only [endpointLaw, Bool.false_eq_true, ite_false, if_false,
      ite_true, if_true, leftLaw, rightLaw]
    all_goals
      filter_upwards [intervalLaw_ae_mem _ _] with x hx
      constructor <;> linarith [hx.1, hx.2]

lemma endpointLaw_quantize_singleton (side : Bool) (r : ℕ) [NeZero r]
    (l : Label) (d : Fin r) :
    (endpointLaw side m a b l).map (UniformQuantization.quantize r) {d} =
      endpointLaw side m a b l (bin r d) := by
  rw [Measure.map_apply (UniformQuantization.measurable_quantize r) (measurableSet_singleton d)]
  apply measure_congr
  filter_upwards [endpointLaw_ae_unit hm ha ha' hb hb' side l] with x hx
  exact propext (UniformQuantization.quantize_eq_iff d hx)

lemma digitJoint_eq_sum (side : Bool) (r : ℕ) [NeZero r] :
    digitJoint side r κ m a b t =
      ∑ l, labelMass κ m a b t l •
        ((endpointLaw side m a b l).map (UniformQuantization.quantize r)).prod (Measure.dirac l) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have hQ := UniformQuantization.measurable_quantize r
  have hmap : Measurable (fun z : CoordinateSample =>
      (UniformQuantization.quantize r (endpoint side z), z.1)) := by
    cases side <;> dsimp [endpoint] <;> fun_prop
  unfold digitJoint rawLaw labelledMixture
  rw [Measure.map_add _ _ hmap, map_finsetSum _ _ hmap, Fintype.sum_option]
  simp only [Measure.map_smul]
  congr 1
  · cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      labelMass, endpointLaw]
    all_goals
      first
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop)]
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop)]
      congr 2
      unfold CouplingMixture.diagonal
      have hdiag : Measurable (fun x : ℝ => (x, x)) := by fun_prop
      have hleft : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) := by fun_prop
      have hright : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) := by fun_prop
      first
      | rw [Measure.map_map hleft hdiag]
      | rw [Measure.map_map hright hdiag]
      rfl
  · apply Finset.sum_congr rfl
    intro i _
    cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      labelMass, endpointLaw]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop), observed_pair_left _ _ _ hQ]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop), observed_pair_right _ _ _ hQ]

lemma digitJoint_fst_singleton (side : Bool) (r : ℕ) [NeZero r] (d : Fin r) :
    (digitJoint side r κ m a b t).fst {d} =
      ∑ l, digitWeight side r κ m a b t l d := by
  rw [digitJoint_eq_sum hm ha ha' hb hb', Measure.fst,
    map_finsetSum _ _ measurable_fst]
  simp only [Measure.map_smul, Measure.map_fst_prod,
    measure_univ, one_smul,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [endpointLaw_quantize_singleton hm ha ha' hb hb']
  rfl

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixNonterminal
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge _root_.OAI.Invariant233.MixedRadix.hybrid_apply_lt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233

theorem infinitePi_eventually_mem_null
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : (n : ℕ) → Set (X n)) (hs : ∀ n, MeasurableSet (s n))
    {q : ℝ≥0∞} (hq : q < 1) (hprob : ∀ n, μ n (s n) ≤ q) :
    (Measure.infinitePi μ) {x | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} = 0 := by
  have htail (N k : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤ q ^ k := by
    calc
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤
          (Measure.infinitePi μ) (Set.pi (Finset.Ico N (N + k)) s) := by
        apply measure_mono
        intro x hx n hn
        exact hx n (Finset.mem_Ico.mp hn).1
      _ = ∏ n ∈ Finset.Ico N (N + k), μ n (s n) :=
        Measure.infinitePi_pi μ (fun n _ => hs n)
      _ ≤ ∏ _n ∈ Finset.Ico N (N + k), q :=
        Finset.prod_le_prod' (fun n _ => hprob n)
      _ = q ^ k := by simp
  have hnull (N : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} = 0 := by
    apply le_antisymm _ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Eventually.of_forall (htail N))
  have heq : {x : (n : ℕ) → X n | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} =
      ⋃ N : ℕ, {x | ∀ n, N ≤ n → x n ∈ s n} := by
    ext x
    simp
  rw [heq]
  exact measure_iUnion_null hnull

namespace MixedRadix

variable {r : ℕ → ℕ} [∀ n, NeZero (r n)]

theorem uniformDigit_singleton (n : ℕ) (a : Fin (r n)) :
    (PMF.uniformOfFintype (Fin (r n))).toMeasure {a} = (r n : ℝ≥0∞)⁻¹ := by
  simp

theorem ae_nonterminal_uniformDigits (hr : ∀ n, 2 ≤ r n) :
    ∀ᵐ d ∂Measure.infinitePi (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure),
      Nonterminal d := by
  let s : (n : ℕ) → Set (Fin (r n)) := fun n => {a | ¬(a : ℕ) + 1 < r n}
  have hs (n : ℕ) : MeasurableSet (s n) := Set.toFinite (s n) |>.measurableSet
  have heq (n : ℕ) : s n = {⟨r n - 1, by have := hr n; omega⟩} := by
    ext a
    simp only [s, Set.mem_ofPred_eq, Set.mem_singleton_iff, Fin.ext_iff]
    have ha := a.isLt
    have h := hr n
    omega
  have hprob (n : ℕ) : (PMF.uniformOfFintype (Fin (r n))).toMeasure (s n) ≤
      (2 : ℝ≥0∞)⁻¹ := by
    rw [heq, uniformDigit_singleton]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hr n)
  have hnull := infinitePi_eventually_mem_null
    (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure) s hs
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1) hprob
  rw [ae_iff]
  simpa only [Nonterminal, Set.mem_ofPred_eq, not_forall, not_exists, not_and, s] using hnull

end MixedRadix
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingNonterminal
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma initial_digit_singleton {p : CircleParameterData}
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    (initialLaw.map (observedDigit p hr side i)) {d} =
      (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  rw [initialLaw, Measure.map_map (measurable_observedDigit hr side i)
    (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop)]
  cases side <;>
    change (baseLaw.map (UniformQuantization.quantize _)) {d} = _
  all_goals rw [baseLaw_eq_restrict]; exact UniformQuantization.map_quantize_singleton _ d

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma observed_singleton_le_half (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    ((coordinateLaw p j i).map (observedDigit p hr side i)) {d} ≤ (2 : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initial_digit_singleton]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible i))
  obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (by omega)
  have hidx := p.blockIndex_eq_of_mem hp.m_pos his
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have ht := tag_bounds j s
  have h20 : (20 : ℝ) ≤ MixedRadix.radices p.q i := by
    have hN := hp.coupling_radix_ge_N hs his
    have hK : (100 : ℝ) ≤ p.K s := by exact_mod_cast hp.coupling_K_ge s hs
    dsimp [N] at hN
    nlinarith
  rw [coordinateLaw, ite_eq_right hi, hidx]
  have hfst := Measure.fst_map_prodMk (μ := rawLaw (kappa s) (p.m s) (p.a s) (p.b s) (tag j s))
    (X := observedDigit p hr side i) measurable_fst
  rw [← hfst]
  change (digitJoint side (MixedRadix.radices p.q i) (kappa s) (p.m s) (p.a s) (p.b s) (tag j s)).fst {d} ≤ _
  rw [digitJoint_fst_singleton hm ha.1 ha.2 hb.1 hb.2]
  calc
    _ ≤ 10 * baseLaw (bin _ d) := digitWeight_total_le_ten hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side _ d
    _ = 10 * (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by rw [baseLaw_bin]
    _ ≤ 10 * (20 : ℝ≥0∞)⁻¹ := mul_le_mul_right (ENNReal.inv_le_inv.mpr (by exact_mod_cast h20)) 10
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

lemma ae_nonterminal_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, MixedRadix.Nonterminal (digits p hr side ω) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let s : ℕ → Set CoordinateSample := fun i =>
    {z | ¬(observedDigit p hr side i z : ℕ) + 1 < MixedRadix.radices p.q i}
  have heq (i : ℕ) : s i = observedDigit p hr side i ⁻¹'
      {⟨MixedRadix.radices p.q i - 1, by have := hr i; omega⟩} := by
    ext z
    simp only [s, mem_ofPred_eq, mem_preimage, mem_singleton_iff, Fin.ext_iff]
    have := (observedDigit p hr side i z).isLt
    omega
  have hs (i : ℕ) : MeasurableSet (s i) := by
    rw [heq]
    exact (measurable_observedDigit hr side i) (measurableSet_singleton _)
  have hprob (i : ℕ) : coordinateLaw p j i (s i) ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [heq, ← Measure.map_apply (measurable_observedDigit hr side i) (measurableSet_singleton _)]
    exact observed_singleton_le_half hp j hr side i _
  have hnull := infinitePi_eventually_mem_null (coordinateLaw p j) s hs
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1) hprob
  rw [ae_iff]
  simpa only [law, MixedRadix.Nonterminal, digits, mem_ofPred_eq,
    not_forall, not_exists, not_and, s] using hnull

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixTransport
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge _root_.OAI.Invariant233.MixedRadix.hybrid_apply_lt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MixedRadix

theorem measurePreserving_unitCircle :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ico 0 1)) volume := by
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

theorem measurable_circleCanonical (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    Measurable (circleCanonical r hr) :=
  (measurable_canonicalDigits r hr).comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable)

theorem circleCanonical_circleValue {r : ℕ → ℕ} (hp : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) :
    circleCanonical r hp (circleValue d) = d := by
  have hx : ofDigits d ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa using ofDigits_mem_Ico hp d hnt
  unfold circleCanonical circleValue
  rw [AddCircle.equivIco_coe_eq hx]
  exact canonicalDigits_ofDigits hp d hnt

theorem circleValue_measurePreserving {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (μ : Measure (Digits r))
    (hlaw : μ.map ofDigits = volume.restrict (Set.Ico 0 1)) :
    MeasurePreserving (@circleValue r) μ volume := by
  exact measurePreserving_unitCircle.comp ⟨measurable_ofDigits hr, hlaw⟩

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingCrossings
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinate_point_eq_tail (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) (hnt : MixedRadix.Nonterminal (digits p hr side ω)) (i : ℕ) :
    p.coordinate i (point p hr side ω) = MixedRadix.tailValue (digits p hr side ω) i := by
  unfold coordinate point MixedRadix.circleValue
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  change CircleParameterData.rep (((p.q i : ℝ) * MixedRadix.ofDigits (digits p hr side ω) : ℝ) : Circle) = _
  rw [show CircleParameterData.rep = (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) from rfl,
    CircleCharacterDynamics.representative_coe]
  exact MixedRadix.coordinate_eq_tailValue hp.frequency_zero hp.q_pos
    hp.frequency_increasing hp.frequency_divisible _ hnt i

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingSupport
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMixture CouplingMarginalBounds OneCoordinateCoupling

lemma rawLaw_ae_of_components {κ m a b t : ℝ} {P : CoordinateSample → Prop}
    (hP : MeasurableSet {z | P z})
    (hdiag : ∀ᵐ x ∂baseLaw, P (none, (x, x)))
    (hcomp : ∀ i : Fin 5, ∀ᵐ z ∂(leftLaw (2 * m) a b i).prod (rightLaw (2 * m) a b i),
      P (some i, z)) : ∀ᵐ z ∂rawLaw κ m a b t, P z := by
  unfold rawLaw labelledMixture
  rw [ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop).aemeasurable hP).2
    unfold CouplingMixture.diagonal
    exact (ae_map_iff (show Measurable (fun x : ℝ => (x, x)) from by fun_prop).aemeasurable
      (show MeasurableSet {z : ℝ × ℝ | P (none, z)} from
        (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop) hP)).2 hdiag
  · intro i _
    exact Measure.ae_smul_measure
      ((ae_map_iff (show Measurable (fun z : ℝ × ℝ => (some i, z)) from by fun_prop).aemeasurable hP).2 (hcomp i)) _

section Parameters
variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma rawLaw_ae_endpoint_property (side : Bool) {P : Label → ℝ → Prop}
    (hP : MeasurableSet {z : CoordinateSample | P z.1 (endpoint side z)})
    (hbase : ∀ᵐ x ∂baseLaw, P none x)
    (hl : ∀ i : Fin 5, ∀ᵐ x ∂endpointLaw side m a b (some i), P (some i) x) :
    ∀ᵐ z ∂rawLaw κ m a b t, P z.1 (endpoint side z) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply rawLaw_ae_of_components hP
  · cases side <;> exact hbase
  · intro i
    cases side
    · exact (measurePreserving_fst (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)
    · exact (measurePreserving_snd (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)

lemma rawLaw_ae_endpoint_unit (side : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, endpoint side z ∈ Ico (0 : ℝ) 1 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' side (P := fun _ x => x ∈ Ico (0 : ℝ) 1)
  · apply measurableSet_Ico.preimage
    cases side
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  · exact intervalLaw_ae_mem 0 1
  · intro i
    exact endpointLaw_ae_unit hm ha ha' hb hb' side (some i)

end Parameters
end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingOrder
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.UniformQuantization

lemma quantize_mono_on_unit {q : ℕ} [NeZero q] {x y : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) (hxy : x ≤ y) :
    quantize q x ≤ quantize q y := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hfx : ⌊(q : ℝ) * x⌋₊ < q :=
    (Nat.floor_lt (mul_nonneg hq.le hx.1)).mpr (by nlinarith [hx.2])
  have hfy : ⌊(q : ℝ) * y⌋₊ < q :=
    (Nat.floor_lt (mul_nonneg hq.le hy.1)).mpr (by nlinarith [hy.2])
  change ⌊(q : ℝ) * x⌋₊ % q ≤ ⌊(q : ℝ) * y⌋₊ % q
  rw [Nat.mod_eq_of_lt hfx, Nat.mod_eq_of_lt hfy]
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hxy hq.le)

end Invariant233.UniformQuantization

namespace Invariant233.CircleDigitCoupling
open OneCoordinateCoupling

lemma rawLaw_ae_ordered {κ m a b t : ℝ} (hm : 1 ≤ m) :
    ∀ᵐ z ∂rawLaw κ m a b t, endpoint false z ≤ endpoint true z := by
  apply rawLaw_ae_of_components
  · exact measurableSet_le (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)
  · exact Eventually.of_forall (fun _ => le_rfl)
  · exact replacement_ae_ordered (by linarith : 2 ≤ 2 * m)

end Invariant233.CircleDigitCoupling

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinateLaw_ae_ordered (j i : ℕ) :
    ∀ᵐ z ∂coordinateLaw p j i, endpoint false z ≤ endpoint true z := by
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (measurableSet_le (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd))).2
    exact Eventually.of_forall (fun _ => le_rfl)
  · rw [coordinateLaw, ite_eq_right hi]
    apply rawLaw_ae_ordered
    have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    exact_mod_cast (show 1 ≤ p.m (p.blockIndex i) by
      have := hp.m_ge_200 _ hs
      omega)

lemma coordinateLaw_ae_endpoint_unit (j : ℕ) (side : Bool) (i : ℕ) :
    ∀ᵐ z ∂coordinateLaw p j i, endpoint side z ∈ Ico (0 : ℝ) 1 := by
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    have hmeas : Measurable (endpoint side) := by
      cases side
      · exact measurable_fst.comp measurable_snd
      · exact measurable_snd.comp measurable_snd
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (measurableSet_Ico.preimage hmeas)).2
    cases side <;> exact CouplingMixture.intervalLaw_ae_mem 0 1
  · rw [coordinateLaw, ite_eq_right hi]
    have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
      exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by
        have := hp.m_ge_200 _ hs
        omega)
    exact rawLaw_ae_endpoint_unit hm (hp.coupling_a_bounds _ hs).1
      (hp.coupling_a_bounds _ hs).2 (hp.coupling_b_bounds _ hs).1
      (hp.coupling_b_bounds _ hs).2 side

lemma ae_digits_ordered (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ i, digits p hr false ω i ≤ digits p hr true ω i := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply ae_all_iff.2
  intro i
  have h : ∀ᵐ z ∂coordinateLaw p j i,
      observedDigit p hr false i z ≤ observedDigit p hr true i z := by
    filter_upwards [coordinateLaw_ae_ordered hp j i,
      coordinateLaw_ae_endpoint_unit hp j false i,
      coordinateLaw_ae_endpoint_unit hp j true i] with z hz hx hy
    let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
    exact UniformQuantization.quantize_mono_on_unit hx hy hz
  exact (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae h

lemma ae_coordinates_ordered (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ i,
      p.coordinate i (point p hr false ω) ≤ p.coordinate i (point p hr true ω) := by
  filter_upwards [ae_digits_ordered hp j hr, ae_nonterminal_digits hp j hr false,
    ae_nonterminal_digits hp j hr true] with ω horder hx hy
  intro i
  rw [coordinate_point_eq_tail hp hr false ω hx i,
    coordinate_point_eq_tail hp hr true ω hy i]
  exact MixedRadix.tailValue_mono hr horder i

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open Filter
open scoped Topology

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem shifted_K_pos (n : ℕ) : 0 < (p.K (n + 1) : ℝ) := by
  exact_mod_cast hp.K_pos (n + 1) (by omega)

theorem shifted_K_double (n : ℕ) :
    2 * (p.K (n + 1) : ℝ) ≤ (p.K (n + 1 + 1) : ℝ) := by
  exact_mod_cast (hp.K_double (n + 1) (by omega)).le

theorem summable_reciprocal : Summable (fun n : ℕ => 1 / (p.K (n + 1) : ℝ)) :=
  ParameterTails.summable_reciprocal hp.shifted_K_pos hp.shifted_K_double

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CirclePhaseSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open scoped BigOperators ENNReal

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_sum_le (j : ℕ) (hj : 1 ≤ j) :
    (∑ i ∈ p.block j, p.alpha θ i) ≤ 2 / (p.K j : ℝ) := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    (∑ i ∈ p.block j, p.alpha θ i) ≤ ∑ i ∈ p.block j, 2 / p.N j := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hp.phase_bounds j hj i hi).2.le
    _ = ((p.block j).card : ℝ) * (2 / p.N j) := by simp
    _ = 2 / (p.K j : ℝ) := by
      rw [p.card_block j hj]
      simp only [CircleParameterData.N]
      field_simp

theorem summable_block_phases :
    Summable (fun n : ℕ => ∑ i ∈ p.block (n + 1), p.alpha θ i) := by
  apply Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg (fun i _ => Int.fract_nonneg _))
    (fun n => hp.block_phase_sum_le (n + 1) (by omega))
  simpa only [mul_one_div] using hp.summable_reciprocal.mul_left 2

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ParameterCircleCocycle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped BigOperators ENNReal

namespace Invariant233

namespace CircleParameterData

theorem coord_phase_eq (p : CircleParameterData) (θ : ℝ) (i : p.Coord) :
    CircleWeights.phase θ p.coordFrequency i = p.alpha θ i.2 := by
  simp only [CircleWeights.phase, coordFrequency, alpha, Int.cast_natCast]

theorem coord_coordinate_eq (p : CircleParameterData) (i : p.Coord) (x : Circle) :
    CircleWeights.coordinate p.coordFrequency i x = p.coordinate i.2 x := by
  simp only [CircleWeights.coordinate, CircleWeights.representative,
    coordFrequency, coordinate, rep, natCast_zsmul]

theorem floorCocycle_pos (p : CircleParameterData) (θ : ℝ) (k : ℤ) (x : Circle) :
    0 < p.floorCocycle θ k x := Real.exp_pos _

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem summable_coord_phases : Summable (CircleWeights.phase θ p.coordFrequency) := by
  rw [show CircleWeights.phase θ p.coordFrequency =
    (fun i : p.Coord => p.alpha θ i.2) from funext (p.coord_phase_eq θ)]
  apply (summable_sigma_of_nonneg (fun i => Int.fract_nonneg _)).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · apply hp.summable_block_phases.congr
    intro j
    simp only [tsum_fintype]
    exact (Finset.sum_attach (p.block (j + 1)) (p.alpha θ)).symm

theorem exists_parameter_cocycle_set :
    ∃ s : Set Circle, MeasurableSet s ∧ (∀ᵐ x ∂circleMeasure, x ∈ s) ∧
      (∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i : p.Coord =>
          Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        p.floorCocycle θ (k + n) x =
          p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x) := by
  simpa only [circleMeasure, CircleParameterData.floorCocycle,
    p.coord_phase_eq, p.coord_coordinate_eq] using
    CircleWeights.exists_cocycle_set θ p.coordFrequency hp.coordFrequency_ne_zero
      p.coordCost hp.summable_coord_phases

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleMarginalBudget
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233
namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

private theorem budgetBlocks_partition :
    ∀ i : ℕ, ∃! s : ℕ, i ∈ budgetBlocks p s := by
  intro i
  by_cases hi : i = 0
  · subst i
    refine ⟨0, by simp [budgetBlocks], ?_⟩
    intro s hs
    by_contra h
    have hb : 0 ∈ p.block s := by simpa [budgetBlocks, h] using hs
    have hb' := (p.mem_block_iff s 0).mp hb
    omega
  · obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (by omega)
    have hs0 : s ≠ 0 := by omega
    refine ⟨s, by simpa [budgetBlocks, hs0] using his, ?_⟩
    intro t hit
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      simp [budgetBlocks, hi] at hit
    have ht : i ∈ p.block t := by simpa [budgetBlocks, ht0] using hit
    exact p.block_index_unique hp.m_pos ht his

theorem normalized_block_budget (a : ℕ → ℝ) (ha : ∀ s, 0 ≤ a s)
    (has : Summable a) :
    Summable (fun i : ℕ => if i = 0 then 0 else
      a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) ∧
    (∑' i : ℕ, if i = 0 then 0 else
      a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) ≤ ∑' s, a s := by
  classical
  let f : ℕ → ℝ := fun i => if i = 0 then 0 else
    a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)
  have hfnonneg : ∀ i, 0 ≤ f i := by
    intro i
    simp only [f]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (ha _) (Nat.cast_nonneg _)
  have hblock (s : ℕ) :
      (∑' i : budgetBlocks p s, f i) = if s = 0 then 0 else a s := by
    rw [Finset.tsum_subtype]
    by_cases hs : s = 0
    · subst s
      simp [budgetBlocks, f]
    · have hspos : 1 ≤ s := by omega
      rw [ite_eq_right hs]
      simp only [budgetBlocks, ite_eq_right hs]
      have hm : (p.m s : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos s hspos).ne'
      calc
        (∑ i ∈ p.block s, f i) = ∑ _i ∈ p.block s, a s / (p.m s : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi0 : i ≠ 0 := by
            have := (p.mem_block_iff s i).mp hi
            omega
          simp only [f, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
        _ = a s := by
          simp only [Finset.sum_const, nsmul_eq_mul, p.card_block s hspos]
          field_simp
  have hgnonneg : ∀ s, 0 ≤ (if s = 0 then 0 else a s) := by
    intro s
    split_ifs
    · exact le_rfl
    · exact ha s
  have hgle : ∀ s, (if s = 0 then 0 else a s) ≤ a s := by
    intro s
    split_ifs
    · exact ha s
    · exact le_rfl
  have hgs : Summable (fun s : ℕ => if s = 0 then 0 else a s) :=
    Summable.of_nonneg_of_le hgnonneg hgle has
  have hfs : Summable f := by
    apply (summable_partition hfnonneg hp.budgetBlocks_partition).mpr
    constructor
    · intro s
      exact (hasSum_fintype _).summable
    · apply hgs.congr
      intro s
      exact (hblock s).symm
  refine ⟨hfs, ?_⟩
  let e := Set.sigmaEquiv (fun s => (budgetBlocks p s : Set ℕ)) hp.budgetBlocks_partition
  have he (z : Σ s, (budgetBlocks p s : Set ℕ)) : e z = z.2 := rfl
  have hsig : Summable (fun z : Σ s, (budgetBlocks p s : Set ℕ) => f z.2) := by
    apply (e.summable_iff.mpr hfs).congr
    intro z
    change f (e z) = f z.2
    rw [he]
  calc
    (∑' i, f i) = ∑' z : Σ s, (budgetBlocks p s : Set ℕ), f z.2 :=
      by simpa only [he] using (e.tsum_eq f).symm
    _ = ∑' s, ∑' i : budgetBlocks p s, f i := hsig.tsum_sigma
    _ = ∑' s, if s = 0 then 0 else a s := tsum_congr hblock
    _ ≤ ∑' s, a s := hgs.tsum_le_tsum hgle has

end CircleParameterLaws

namespace CircleParameterData

theorem summable_kappa_sq : Summable (fun s : ℕ => kappa s ^ 2) := by
  have h : Summable (fun s : ℕ => 1 / (s : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (h.mul_left ((1 / 100 : ℝ) ^ 2)).congr
  intro s
  simp only [kappa, div_pow, mul_pow]
  ring

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem circle_marginal_budget (j : ℕ) :
    Summable (fun i : ℕ => if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) ∧
    (∑' i : ℕ, if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) ≤
      50 * ((∑' s : ℕ, CircleParameterData.kappa s ^ 2) + 1) := by
  let a : ℕ → ℝ := fun s => 50 *
    (CircleParameterData.kappa s ^ 2 + if s = j then 1 else 0)
  have ha : ∀ s, 0 ≤ a s := by
    intro s
    dsimp [a]
    positivity
  have hs : Summable a :=
    (CircleParameterData.summable_kappa_sq.add (hasSum_ite_eq j (1 : ℝ)).summable).mul_left 50
  have heq : (fun i : ℕ => if i = 0 then 0 else
      50 * (CircleParameterData.kappa (p.blockIndex i) ^ 2 /
        (p.m (p.blockIndex i) : ℝ) +
        (if p.blockIndex i = j then 1 else 0) / (p.m (p.blockIndex i) : ℝ))) =
      (fun i : ℕ => if i = 0 then 0 else
        a (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ)) := by
    funext i
    dsimp [a]
    split_ifs <;> ring
  rw [heq]
  obtain ⟨hsum, hle⟩ := hp.normalized_block_budget a ha hs
  refine ⟨hsum, hle.trans_eq ?_⟩
  simp only [a, tsum_mul_left, Summable.tsum_add CircleParameterData.summable_kappa_sq
    (hasSum_ite_eq j (1 : ℝ)).summable, tsum_ite_eq]

end CircleParameterLaws
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.ProductDensity

theorem integral_sq_eq_one_add_centered_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} (hh : MemLp h 2 μ) (hmean : ∫ x, h x ∂μ = 1) :
    (∫ x, h x ^ 2 ∂μ) = 1 + ∫ x, (h x - 1) ^ 2 ∂μ := by
  have hv := ProbabilityTheory.variance_eq_sub hh
  rw [ProbabilityTheory.variance_eq_integral hh.aemeasurable, hmean] at hv
  norm_num at hv
  linarith

theorem integral_finite_product_sq
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, (1 + ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  calc
    _ = ∫ x, ∏ i, (h i (x i)) ^ 2 ∂Measure.pi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = ∏ i, ∫ x, (h i x) ^ 2 ∂μ i := integral_fintype_prod_eq_prod (μ := μ) (fun i x => h i x ^ 2)
    _ = _ := Finset.prod_congr rfl fun i _ =>
      integral_sq_eq_one_add_centered_sq (hh i) (hmean i)

theorem integral_finite_product_sq_le_exp
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤
      Real.exp (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  rw [integral_finite_product_sq hh hmean]
  exact Real.prod_one_add_le_exp_sum _ fun i => integral_nonneg fun x => sq_nonneg _

theorem integral_finite_product_sq_le_exp_of_sum_le
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤ Real.exp C :=
  (integral_finite_product_sq_le_exp hh hmean).trans (Real.exp_le_exp.mpr hC)

theorem eLpNorm_finite_product_le_exp_half
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i, h i (x i)) 2 (Measure.pi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (memLp_finite_product hh)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.exp C) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (integral_finite_product_sq_le_exp_of_sum_le hh hmean hC) (by positivity)
    _ = Real.exp (C / 2) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem eLpNorm_partial_product_le_exp_half
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i ∈ s, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  have heq := eLpNorm_comp_measurePreserving
    (memLp_finite_product (fun i : s => hh i)).aestronglyMeasurable
    (measurePreserving_restrict_infinitePi μ s) (p := (2 : ℝ≥0∞))
  have hbound := eLpNorm_finite_product_le_exp_half (fun i : s => hh i)
    (fun i : s => hmean i) (C := C) (by
      exact (Finset.sum_coe_sort s (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i)).le.trans hC)
  rw [partial_product_eq_restrict h s]
  exact heq.le.trans hbound

theorem eLpNorm_partial_product_le_exp_half_of_tsum_le
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  apply eLpNorm_partial_product_le_exp_half s hh hmean
  exact (hsum.sum_le_tsum s fun i _ => integral_nonneg fun x => sq_nonneg _).trans hC

theorem integral_partial_product
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} (s : Finset ι)
    (hh : ∀ i, Integrable (h i) (μ i)) :
    (∫ x, ∏ i ∈ s, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ∂μ i := by
  rw [partial_product_eq_restrict h s]
  change (∫ x, (fun y : (i : s) → Ω i => ∏ i : s, h i (y i)) (s.restrict x)
    ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi (μ := μ) (s := s)
    (f := fun y : (i : s) → Ω i => ∏ i : s, h i (y i))
    (Integrable.fintype_prod_dep (fun i : s => hh i)).aestronglyMeasurable]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort s (fun i => ∫ x, h i x ∂μ i)

theorem partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t) (x : (i : ι) → Ω i) :
    (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) =
      ∏ i ∈ t, if i ∈ s then h i (x i) ^ 2 else h i (x i) := by
  have heq : (∏ i ∈ t, if i ∈ s then h i (x i) else 1) =
      ∏ i ∈ s, h i (x i) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [← heq, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> ring

theorem integral_partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∫ x, (∏ i ∈ s, h i (x i)) ^ 2 ∂Measure.infinitePi μ := by
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then h i x ^ 2 else h i x) (μ i) := by
    intro i
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using (hh i).integrable_sq
    · simpa only [ite_eq_right hi] using (hh i).integrable (by norm_num)
  have hleft : (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ^ 2 ∂μ i := by
    simp_rw [partial_product_mul_of_subset h hst]
    rw [integral_partial_product t hmixed]
    calc
      _ = ∏ i ∈ t, if i ∈ s then ∫ x, h i x ^ 2 ∂μ i else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ s
        · simp only [ite_eq_left his]
        · simp only [ite_eq_right his, hmean]
      _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [hleft]
  symm
  calc
    _ = ∫ x, ∏ i ∈ s, h i (x i) ^ 2 ∂Measure.infinitePi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = _ := integral_partial_product s (fun i => (hh i).integrable_sq)

theorem indicator_partial_product
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t)
    (a : (i : ι) → Set (Ω i)) (x : (i : ι) → Ω i) :
    (Set.pi (s : Set ι) a).indicator (fun y => ∏ i ∈ t, h i (y i)) x =
      ∏ i ∈ t, if i ∈ s then (a i).indicator (h i) (x i) else h i (x i) := by
  classical
  by_cases hx : x ∈ Set.pi (s : Set ι) a
  · rw [Set.indicator_of_mem hx]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases his : i ∈ s
    · rw [ite_eq_left his, Set.indicator_of_mem ((Set.mem_pi.mp hx) i his)]
    · rw [ite_eq_right his]
  · rw [Set.indicator_of_notMem hx]
    symm
    have hex : ∃ i ∈ s, x i ∉ a i := by
      by_contra hnone
      apply hx
      apply Set.mem_pi.mpr
      intro i hi
      by_contra hix
      exact hnone ⟨i, hi, hix⟩
    obtain ⟨i, his, hix⟩ := hex
    apply Finset.prod_eq_zero (hst his)
    rw [ite_eq_left his, Set.indicator_of_notMem hix]

theorem setIntegral_partial_product_pi
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, Integrable (h i) (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (a : (i : ι) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ι) a, ∏ i ∈ t, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  classical
  have hmeas : MeasurableSet (Set.pi (s : Set ι) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [← integral_indicator hmeas]
  simp_rw [indicator_partial_product h hst a]
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then (a i).indicator (h i) x else h i x) (μ i) := by
    intro i
    by_cases his : i ∈ s
    · simpa only [ite_eq_left his] using (hh i).indicator (ha i)
    · simpa only [ite_eq_right his] using hh i
  rw [integral_partial_product t hmixed]
  calc
    _ = ∏ i ∈ t, if i ∈ s then ∫ x in a i, h i x ∂μ i else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · simp only [ite_eq_left his, integral_indicator (ha i)]
      · simp only [ite_eq_right his, hmean]
    _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_OrthogonalPrefixLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductDensity

theorem cauchySeq_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) : CauchySeq f := by
  have hdist : ∀ n m, n ≤ m → dist (f n) (f m) ^ 2 = ‖f m‖ ^ 2 - ‖f n‖ ^ 2 := by
    intro n m hnm
    rw [dist_eq_norm, norm_sub_sq_real, hinner n m hnm]
    ring
  have hmono : Monotone (fun n => ‖f n‖ ^ 2) := by
    intro n m hnm
    have := sq_nonneg (dist (f n) (f m))
    rw [hdist n m hnm] at this
    linarith
  have hc : CauchySeq (fun n => ‖f n‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbound).cauchySeq
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hreal := hN n hn m hm
  rw [Real.dist_eq] at hreal
  rcases le_total n m with hnm | hmn
  · have hs := hdist n m hnm
    have hl := (abs_lt.mp hreal).1
    nlinarith [dist_nonneg (x := f n) (y := f m)]
  · have hs := hdist m n hmn
    have hl := (abs_lt.mp hreal).2
    rw [dist_comm (f m) (f n)] at hs
    nlinarith [dist_nonneg (x := f n) (y := f m)]

theorem exists_limit_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) :
    ∃ g : E, Tendsto f atTop (𝓝 g) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_prefix_inner f hinner hbound)

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensityLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductDensity

theorem inner_toLp_eq_integral_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp [hfx, hgx, mul_comm]

theorem partialDensityLp_inner
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) {n m : ℕ} (hnm : n ≤ m) :
    inner ℝ (partialDensityLp hh n) (partialDensityLp hh m) =
      ‖partialDensityLp hh n‖ ^ 2 := by
  calc
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) *
        (∏ i ∈ Finset.range m, h i (x i)) ∂Measure.infinitePi μ :=
      inner_toLp_eq_integral_mul _ _
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) ^ 2 ∂Measure.infinitePi μ :=
      integral_partial_product_mul_of_subset (Finset.range_mono hnm) hh hmean
    _ = inner ℝ (partialDensityLp hh n) (partialDensityLp hh n) := by
      rw [partialDensityLp, inner_toLp_eq_integral_mul]
      congr 1
      funext x
      ring
    _ = _ := real_inner_self_eq_norm_sq _

theorem exists_partialDensityLp_limit
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ g : Lp ℝ 2 (Measure.infinitePi μ),
      Tendsto (partialDensityLp hh) atTop (𝓝 g) ∧ ‖g‖ ≤ Real.exp (C / 2) := by
  have hb : ∀ n, ‖partialDensityLp hh n‖ ≤ Real.exp (C / 2) := by
    intro n
    rw [partialDensityLp, Lp.norm_toLp]
    have hnorm := eLpNorm_partial_product_le_exp_half_of_tsum_le
      (Finset.range n) hh hmean hsum hC
    have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
  obtain ⟨g, hg⟩ := exists_limit_of_prefix_inner (partialDensityLp hh)
    (fun n m hnm => partialDensityLp_inner hh hmean hnm)
    ⟨(Real.exp (C / 2)) ^ 2, by
      rintro _ ⟨n, rfl⟩
      exact pow_le_pow_left₀ (norm_nonneg _) (hb n) 2⟩
  exact ⟨g, hg, le_of_tendsto hg.norm (Filter.Eventually.of_forall hb)⟩

theorem tendsto_eLpNorm_one_partialDensity_sub
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      1 (Measure.infinitePi μ)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      2 (Measure.infinitePi μ)) atTop (𝓝 0) := by
    have ht := hg.edist (tendsto_const_nhds (x := g))
    simp only [edist_self] at ht
    apply ht.congr
    intro n
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    exact (memLp_partial_product (Finset.range n) hh).coeFn_toLp.sub Filter.EventuallyEq.rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
  intro n
  exact eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | exact (memLp_partial_product (Finset.range n) hh).aestronglyMeasurable.sub (Lp.aestronglyMeasurable g) | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)

theorem partialDensityLp_limit_nonneg
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    0 ≤ᵐ[Measure.infinitePi μ] (g : ((i : ℕ) → Ω i) → ℝ) := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp g).integrable (by norm_num))
  intro s hs hsf
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) s
  exact ge_of_tendsto hi (Filter.Eventually.of_forall fun n =>
    integral_nonneg fun x => Finset.prod_nonneg fun i _ => hnonneg i (x i))

theorem partialDensityLp_limit_integral
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (∫ x, g x ∂Measure.infinitePi μ) = 1 := by
  have hi := tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (g : ((i : ℕ) → Ω i) → ℝ)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg)
  have heq : ∀ n, (∫ x, ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) = 1 := by
    intro n
    rw [integral_partial_product (Finset.range n) (fun i => (hh i).integrable (by norm_num))]
    simp [hmean]
  simp_rw [heq] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

theorem partialDensityLp_limit_setIntegral_pi
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g))
    (s : Finset ℕ) (a : (i : ℕ) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ℕ) a, g x ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) (Set.pi (s : Set ℕ) a)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  have heq : (fun n => ∫ x in Set.pi (s : Set ℕ) a,
      ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) =ᶠ[atTop]
      (fun _ => ∏ i ∈ s, ∫ x in a i, h i x ∂μ i) := by
    apply Filter.eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    exact setIntegral_partial_product_pi (hN.trans (Finset.range_mono hn))
      (fun i => (hh i).integrable (by norm_num)) hmean a ha
  exact tendsto_nhds_unique hi (tendsto_const_nhds.congr' heq.symm)

theorem isProbabilityMeasure_withDensity_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h : Ω → ℝ} (hh : Integrable h μ) (hnonneg : 0 ≤ᵐ[μ] h)
    (hmean : ∫ x, h x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hh hnonneg, hmean]
  simp

theorem partialDensityLp_limit_withDensity
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (g x)) =
      Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  let : ∀ i, IsProbabilityMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isProbabilityMeasure_withDensity_ofReal ((hh i).integrable (by norm_num))
      (Filter.Eventually.of_forall (hnonneg i)) (hmean i)
  have hgnonneg := partialDensityLp_limit_nonneg hh hnonneg hg
  have hgi := (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply Measure.eq_infinitePi
  intro s a ha
  have hmeas : MeasurableSet (Set.pi (s : Set ℕ) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [withDensity_apply _ hmeas,
    ← ofReal_integral_eq_lintegral_ofReal hgi.restrict (ae_restrict_of_ae hgnonneg),
    partialDensityLp_limit_setIntegral_pi hh hmean hg s a ha]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (ha i)]
  exact ofReal_integral_eq_lintegral_ofReal ((hh i).integrable (by norm_num)).restrict
    (Filter.Eventually.of_forall (hnonneg i))

theorem exists_product_density
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  obtain ⟨g, hg, hgbound⟩ := exists_partialDensityLp_limit hh hmean hsum hC
  refine ⟨g, Lp.memLp g, partialDensityLp_limit_nonneg hh hnonneg hg,
    partialDensityLp_limit_integral hh hmean hg, ?_,
    partialDensityLp_limit_withDensity hh hnonneg hmean hg⟩
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hgbound

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitEnergy
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma endpointDensity_memLp (side : Bool) (m a b : ℝ) (l : Label) :
    MemLp (endpointDensity side m a b l) 2 baseLaw := by
  cases l with
  | none => exact memLp_const 1
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma marginalDensity_memLp (side : Bool) (κ m a b t : ℝ) :
    MemLp (marginalDensity side κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (endpointDensity_memLp side m a b (some i)).const_mul _)

lemma endpointDensity_integral {m a b : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) (side : Bool) (l : Label) :
    (∫ x, endpointDensity side m a b l x ∂baseLaw) = 1 := by
  have := endpointLaw_isProbabilityMeasure hm ha ha' hb hb' side l
  have h := congrArg (fun ν : Measure ℝ => ν univ)
    (endpointLaw_eq_density hm ha ha' hb hb' side l)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      ((endpointDensity_memLp side m a b l).integrable (by norm_num))
      (Filter.Eventually.of_forall (endpointDensity_nonneg side m a b l))] at h
  have hn : 0 ≤ ∫ x, endpointDensity side m a b l x ∂baseLaw :=
    integral_nonneg (endpointDensity_nonneg side m a b l)
  exact (ENNReal.ofReal_eq_ofReal_iff hn (by norm_num)).mp (by simpa using h.symm)

lemma marginalDensity_integral {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) (side : Bool) :
    (∫ x, marginalDensity side κ m a b t x ∂baseLaw) = 1 := by
  have hi (i : Fin 5) : Integrable
      (fun x => componentProbabilities κ m a b t i * endpointDensity side m a b (some i) x)
      baseLaw :=
    ((endpointDensity_memLp side m a b (some i)).integrable (by norm_num)).const_mul _
  unfold marginalDensity
  rw [integral_add (integrable_const _) (integrable_finsetSum Finset.univ (fun i _ => hi i)),
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    endpointDensity_integral hm ha ha' hb hb' side, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma marginalDensity_energy {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (∫ x, (marginalDensity side κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      50 * (κ ^ 2 / m + t / m) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hf (i : Fin 5) : MemLp
      (fun x => endpointDensity side m a b (some i) x - 1) 2 baseLaw :=
    (endpointDensity_memLp side m a b (some i)).sub (memLp_const 1)
  have hv (i : Fin 5) :
      (∫ x, (endpointDensity side m a b (some i) x - 1) ^ 2 ∂baseLaw) ≤
        componentVarianceBounds (2 * m) a b i := by
    cases side
    · exact leftDensity_variance_bound (by linarith) ha0 ha' hb0 hb' i
    · exact rightDensity_variance_bound (by linarith) ha0 ha' hb0 hb' i
  have hcs := integral_sq_weighted_sum_le hf (componentProbabilities κ m a b t)
  have hs : (∑ i, componentProbabilities κ m a b t i ^ 2 *
      ∫ x, (endpointDensity side m a b (some i) x - 1) ^ 2 ∂baseLaw) ≤
      ∑ i, componentProbabilities κ m a b t i ^ 2 *
        componentVarianceBounds (2 * m) a b i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (sq_nonneg _))
  have he : (∑ i, componentProbabilities κ m a b t i ^ 2 *
      componentVarianceBounds (2 * m) a b i) = 8 * κ ^ 2 / m + 2 * t ^ 2 / m := by
    simp only [componentProbabilities, componentVarianceBounds, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    have hra := rho_sq_div_width (κ := κ) hm0 ha0
    have hrb := rho_sq_div_width (κ := κ) hm0 hb0
    have htag : (t / m) ^ 2 * (2 * m) = 2 * t ^ 2 / m := by field_simp
    rw [htag]
    simp only [div_eq_mul_inv] at hra hrb ⊢
    nlinarith
  have ht2 : t ^ 2 / m ≤ t / m :=
    div_le_div_of_nonneg_right (by nlinarith) hm0.le
  have hκ2 : 0 ≤ κ ^ 2 / m := div_nonneg (sq_nonneg _) hm0.le
  have htdiv : 0 ≤ t / m := div_nonneg ht0 hm0.le
  simp only [Fintype.card_fin] at hcs
  calc
    _ = ∫ x, (∑ i, componentProbabilities κ m a b t i *
        (endpointDensity side m a b (some i) x - 1)) ^ 2 ∂baseLaw := by
      congr 1
      funext x
      rw [marginalDensity, OneCoordinateCoupling.marginalDensity_sub_one]
    _ ≤ 5 * (∑ i, componentProbabilities κ m a b t i ^ 2 *
        componentVarianceBounds (2 * m) a b i) :=
      hcs.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ ≤ _ := by
      rw [he]
      simp only [div_eq_mul_inv] at ht2 hκ2 htdiv ⊢
      nlinarith

lemma rawLaw_map_endpoint {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) =
      baseLaw.withDensity (fun x => ENNReal.ofReal (marginalDensity side κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    (by norm_num : (0 : ℝ) ≤ 49 / 50).trans
      (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  cases side
  · change (rawLaw κ m a b t).map (Prod.fst ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_fst measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_fst_real_density baseLaw _ _ _ _
      (leftDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (leftLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')
  · change (rawLaw κ m a b t).map (Prod.snd ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_snd measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_snd_real_density baseLaw _ _ _ _
      (rightDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (rightLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_FinitePrefixLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped Classical

namespace Invariant233.FiniteUniformLaw

theorem infinitePi_fin_uniform (α : ℕ → Type*)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)] (N : ℕ) :
    (Measure.infinitePi (fun i => (PMF.uniformOfFintype (α i)).toMeasure)).map
        (fun d (i : Fin N) => d i) =
      (PMF.uniformOfFintype ((i : Fin N) → α i)).toMeasure := by
  classical
  let e : (Finset.range N) ≃ Fin N :=
    { toFun := fun i => ⟨i.1, Finset.mem_range.mp i.2⟩
      invFun := fun i => ⟨i.1, Finset.mem_range.mpr i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E : ((i : Finset.range N) → α i) ≃ ((i : Fin N) → α i) :=
    Equiv.piCongrLeft (fun i : Fin N => α i) e
  have hcomp : (fun d (i : Fin N) => d i) =
      E ∘ (Finset.range N).restrict := by rfl
  rw [hcomp, ← Measure.map_map (measurable_of_finite E) (Finset.measurable_restrict _),
    infinitePi_restrict_uniform]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_finite E) (measurableSet_singleton a)]
  have he : E ⁻¹' {a} = {E.symm a} := by
    ext b
    exact E.eq_symm_apply.symm
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply]
  congr 2
  simp only [← Nat.card_eq_fintype_card]
  exact Nat.card_congr E

end Invariant233.FiniteUniformLaw

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge _root_.OAI.Invariant233.MixedRadix.hybrid_apply_lt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators Classical

namespace Invariant233.MixedRadix

theorem measurable_prefix_sum (r : ℕ → ℕ) (N : ℕ) :
    Measurable (fun d : Digits r => ∑ n ∈ Finset.range N, term d n) := by
  apply Finset.measurable_sum
  intro n hn
  exact ((measurable_of_finite (fun a : Fin (r n) => (a : ℝ))).comp
    (measurable_pi_apply n)).div_const _

theorem tendsto_prefix_sum {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, term d n) atTop (𝓝 (ofDigits d)) :=
  (summable_terms hr d).hasSum.tendsto_sum_nat

theorem tendsto_quantized_prefix {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) /
      (denominator r N : ℝ)) atTop (𝓝 x) := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  have heq : (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) /
      (denominator r N : ℝ)) =
      (fun N => ∑ n ∈ Finset.range N, term (canonicalDigits r hp x) n) := by
    funext N
    have hq : (denominator r N : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast denominator_pos hp N)
    have h := denominator_mul_prefix hp (canonicalDigits r hp x) N
    rw [prefixRank_canonicalDigits hp hx N] at h
    exact (eq_div_iff hq).mpr (by simpa [mul_comm] using h) |>.symm
  rw [heq]
  have hrec : ofDigits (canonicalDigits r hp x) = x := ofDigits_canonicalDigits hr hx
  simpa only [hrec] using tendsto_prefix_sum hp (canonicalDigits r hp x)

theorem map_prefixRank_uniform (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) [NeZero (denominator r N)] :
    (digitLaw r hr).map
      (fun d => finitePrefixRankEquiv r hr N (fun i : Fin N => d i)) =
      (PMF.uniformOfFintype (Fin (denominator r N))).toMeasure := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  let : NeZero (denominator r N) := ⟨ne_of_gt (denominator_pos hr N)⟩
  let E := finitePrefixRankEquiv r hr N
  have hp : (digitLaw r hr).map (fun d (i : Fin N) => d i) =
      (PMF.uniformOfFintype ((i : Fin N) → Fin (r i))).toMeasure := by
    unfold digitLaw
    exact FiniteUniformLaw.infinitePi_fin_uniform (fun n => Fin (r n)) N
  have hm : Measurable (fun d : Digits r => fun i : Fin N => d i) :=
    Measurable.of_eval (fun index => measurable_pi_apply (index : ℕ))
  change (digitLaw r hr).map (E ∘ (fun d (i : Fin N) => d i)) = _
  rw [← Measure.map_map (measurable_of_finite E) hm, hp]
  exact FiniteUniformLaw.map_equiv E

theorem prefix_sum_eq_normalized_rank (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (N : ℕ) (d : Digits r) :
    (∑ n ∈ Finset.range N, term d n) =
      ((finitePrefixRankEquiv r hr N (fun i : Fin N => d i) : ℕ) : ℝ) /
        (denominator r N : ℝ) := by
  rw [finitePrefixRankEquiv_val]
  have heq : prefixRank (extendPrefix r hr N (fun i : Fin N => d i)) N =
      prefixRank d N := by
    apply prefixRank_congr
    intro n hn
    simp [hn]
  rw [heq]
  have hq : (denominator r N : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast denominator_pos hr N)
  exact (eq_div_iff hq).mpr (by simpa [mul_comm] using denominator_mul_prefix hr d N)

theorem map_prefix_sum_eq_quantized (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) :
    (digitLaw r hr).map (fun d => ∑ n ∈ Finset.range N, term d n) =
      (volume.restrict (Ico (0 : ℝ) 1)).map
        (fun x => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ)) := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  let : NeZero (denominator r N) := ⟨ne_of_gt (denominator_pos hr N)⟩
  let R : Digits r → Fin (denominator r N) :=
    fun d => finitePrefixRankEquiv r hr N (fun i : Fin N => d i)
  let g : Fin (denominator r N) → ℝ := fun a => (a : ℝ) / (denominator r N : ℝ)
  have hR : Measurable R := (measurable_of_finite (finitePrefixRankEquiv r hr N)).comp
    (Measurable.of_eval (fun index : Fin N => measurable_pi_apply (index : ℕ)))
  have hg : Measurable g := measurable_of_finite _
  have heq : (fun d => ∑ n ∈ Finset.range N, term d n) = g ∘ R := by
    funext d
    exact prefix_sum_eq_normalized_rank r hr N d
  rw [heq, ← Measure.map_map hg hR]
  have hRlaw : (digitLaw r hr).map R =
      (PMF.uniformOfFintype (Fin (denominator r N))).toMeasure :=
    map_prefixRank_uniform r hr N
  rw [hRlaw, ← UniformQuantization.map_quantize_uniform (denominator r N),
    Measure.map_map hg (UniformQuantization.measurable_quantize _)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with x hx
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hfloor : ⌊(denominator r N : ℝ) * x⌋₊ < denominator r N :=
    (Nat.floor_lt (mul_nonneg hq.le hx.1)).mpr (by nlinarith [hx.2])
  simp [g, UniformQuantization.quantize, Nat.mod_eq_of_lt hfloor]

theorem map_ofDigits_eq_volume (r : ℕ → ℕ) (hr : ∀ n, 2 ≤ r n) :
    (digitLaw r (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n))).map ofDigits =
      volume.restrict (Ico (0 : ℝ) 1) := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  let μ := digitLaw r hp
  let ν := (volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have : IsProbabilityMeasure μ := digitLaw_isProbability r hp
  have hX : ∀ N, AEMeasurable (fun d : Digits r => ∑ n ∈ Finset.range N, term d n) μ :=
    fun N => (measurable_prefix_sum r N).aemeasurable
  have hY : ∀ N, AEMeasurable
      (fun x : ℝ => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ)) ν := by
    intro N
    exact (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_const.mul measurable_id).nat_floor).div_const _).aemeasurable
  have hZ : AEMeasurable (ofDigits : Digits r → ℝ) μ :=
    (continuous_ofDigits hr).measurable.aemeasurable
  have hW : AEMeasurable (id : ℝ → ℝ) ν := measurable_id.aemeasurable
  have hXZ : ∀ᵐ d ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, term d n)
      atTop (𝓝 (ofDigits d)) := Filter.Eventually.of_forall (tendsto_prefix_sum hp)
  have hYW : ∀ᵐ x ∂ν, Tendsto
      (fun N => (⌊(denominator r N : ℝ) * x⌋₊ : ℝ) / (denominator r N : ℝ))
      atTop (𝓝 (id x)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with x hx
    exact tendsto_quantized_prefix hr hx
  have h := Invariant233.map_eq_of_ae_limits_of_map_eq hX hY hZ hW hXZ hYW
    (map_prefix_sum_eq_quantized r hp)
  simpa only [Measure.map_id] using h

end Invariant233.MixedRadix

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixHaarLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MixedRadix

theorem digitLaw_ae_nonterminal {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (hp : ∀ n, 0 < r n) : ∀ᵐ d ∂digitLaw r hp, Nonterminal d := by
  let : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hp n)⟩
  simpa only [digitLaw] using ae_nonterminal_uniformDigits hr

theorem circleValue_measurePreserving_digitLaw {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    MeasurePreserving (@circleValue r) (digitLaw r hp) volume := by
  exact circleValue_measurePreserving hr (digitLaw r hp) (map_ofDigits_eq_volume r hr)

theorem map_circleValue_digitLaw {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    (digitLaw r hp).map circleValue = volume :=
  (circleValue_measurePreserving_digitLaw hr hp).map_eq

theorem ae_circleCanonical_circleValue {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    ∀ᵐ d ∂digitLaw r hp, circleCanonical r hp (circleValue d) = d := by
  filter_upwards [digitLaw_ae_nonterminal hr hp] with d hd
  exact circleCanonical_circleValue hp d hd

theorem map_circleCanonical_volume {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    (volume : Measure (AddCircle (1 : ℝ))).map (circleCanonical r hp) =
      digitLaw r hp :=
  DensityTransport.map_inverse_eq (measurable_circleValue hr)
    (measurable_circleCanonical r hp) (map_circleValue_digitLaw hr hp)
    (ae_circleCanonical_circleValue hr hp)

theorem circleCanonical_measurePreserving {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n) :
    MeasurePreserving (circleCanonical r hp) volume (digitLaw r hp) :=
  ⟨measurable_circleCanonical r hp, map_circleCanonical_volume hr hp⟩

theorem digitLaw_circle_density_transport_ae {r : ℕ → ℕ}
    (hr : ∀ n, 2 ≤ r n) (hp : ∀ n, 0 < r n)
    {h : Digits r → ℝ} (hh : AEMeasurable h (digitLaw r hp)) :
    ((digitLaw r hp).withDensity (fun d => ENNReal.ofReal (h d))).map circleValue =
      volume.withDensity (fun x : AddCircle (1 : ℝ) =>
        ENNReal.ofReal (h (circleCanonical r hp x))) ∧
    eLpNorm (h ∘ circleCanonical r hp) 2 volume = eLpNorm h 2 (digitLaw r hp) :=
  DensityTransport.real_density_transport_ae (measurable_circleValue hr)
    (measurable_circleCanonical r hp) (map_circleValue_digitLaw hr hp)
    (ae_circleCanonical_circleValue hr hp) hh

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleQuantizedMarginals
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma digitReference_isProbabilityMeasure (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (i : ℕ) :
    IsProbabilityMeasure (digitReference p hr i) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  unfold digitReference
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma rawDensity_memLp (p : CircleParameterData) (j : ℕ) (side : Bool) (i : ℕ) :
    MemLp (rawDensity p j side i) 2 baseLaw := by
  unfold rawDensity
  split_ifs
  · exact memLp_const 1
  · exact marginalDensity_memLp _ _ _ _ _ _

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma rawDensity_laws (j : ℕ) (side : Bool) (i : ℕ) :
    (∀ x, 0 ≤ rawDensity p j side i x ∧ rawDensity p j side i x ≤ 10) ∧
      (∫ x, rawDensity p j side i x ∂baseLaw) = 1 ∧
      (∫ x, (rawDensity p j side i x - 1) ^ 2 ∂baseLaw) ≤
        (if i = 0 then 0 else 50 *
          (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
            tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
  by_cases hi : i = 0
  · simp [rawDensity, hi]
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have hκ := CircleParameterLaws.coupling_kappa_bounds _ hs
  have ha := hp.coupling_a_bounds _ hs
  have hb := hp.coupling_b_bounds _ hs
  have ht := tag_bounds j (p.blockIndex i)
  simp only [rawDensity, ite_eq_right hi]
  refine ⟨fun x => ?_, marginalDensity_integral hm ha.1 ha.2 hb.1 hb.2 side,
    marginalDensity_energy hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side⟩
  have hx := marginalDensity_bounds hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side x
  exact ⟨(by norm_num : (0 : ℝ) ≤ 49 / 50).trans hx.1, hx.2.2.le⟩

lemma coordinateLaw_map_endpoint (j : ℕ) (side : Bool) (i : ℕ) :
    (coordinateLaw p j i).map (endpoint side) =
      baseLaw.withDensity (fun x => ENNReal.ofReal (rawDensity p j side i x)) := by
  by_cases hi : i = 0
  · simp only [coordinateLaw, rawDensity, ite_eq_left hi]
    unfold initialLaw
    rw [Measure.map_map (by cases side; exact measurable_fst.comp measurable_snd; exact measurable_snd.comp measurable_snd)
      (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop)]
    cases side <;> simp [endpoint, Function.comp_def]
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have hκ := CircleParameterLaws.coupling_kappa_bounds _ hs
  have ha := hp.coupling_a_bounds _ hs
  have hb := hp.coupling_b_bounds _ hs
  have ht := tag_bounds j (p.blockIndex i)
  simpa only [coordinateLaw, rawDensity, ite_eq_right hi] using
    rawLaw_map_endpoint hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side

lemma observedDigit_density (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    (coordinateLaw p j i).map (observedDigit p hr side i) =
      (digitReference p hr i).withDensity
        (fun d => ENNReal.ofReal (digitDensity p hr j side i d)) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  change (coordinateLaw p j i).map (UniformQuantization.quantize _ ∘ endpoint side) = _
  rw [← Measure.map_map (UniformQuantization.measurable_quantize _)
    (by cases side; exact measurable_fst.comp measurable_snd; exact measurable_snd.comp measurable_snd), coordinateLaw_map_endpoint hp]
  have hh := (rawDensity_memLp p j side i).integrable (by norm_num)
  have hn : ∀ᵐ x ∂baseLaw, 0 ≤ rawDensity p j side i x :=
    Filter.Eventually.of_forall (fun x => ((rawDensity_laws hp j side i).1 x).1)
  rw [baseLaw_eq_restrict] at hh hn ⊢
  exact UniformQuantization.map_withDensity_quantize _ hh hn

lemma digitDensity_laws (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    (∀ d, 0 ≤ digitDensity p hr j side i d ∧ digitDensity p hr j side i d ≤ 10) ∧
      (∫ d, digitDensity p hr j side i d ∂digitReference p hr i) = 1 ∧
      (∫ d, (digitDensity p hr j side i d - 1) ^ 2 ∂digitReference p hr i) ≤
        (if i = 0 then 0 else 50 *
          (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
            tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  have hraw := rawDensity_laws hp j side i
  have hh := rawDensity_memLp p j side i
  rw [baseLaw_eq_restrict] at hh hraw
  refine ⟨fun d => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact UniformQuantization.binAverage_nonneg _
      (Filter.Eventually.of_forall (fun x => (hraw.1 x).1)) d
  · exact UniformQuantization.binAverage_le _ (hh.integrable (by norm_num))
      (Filter.Eventually.of_forall (fun x => (hraw.1 x).2)) d
  · exact (UniformQuantization.integral_binAverage _ (hh.integrable (by norm_num))).trans hraw.2.1
  · exact (UniformQuantization.integral_binAverage_energy_le _ hh).trans hraw.2.2

lemma digitDensity_memLp (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    MemLp (digitDensity p hr j side i) 2 (digitReference p hr i) := by
  have := digitReference_isProbabilityMeasure p hr i
  exact memLp_of_bounded (Filter.Eventually.of_forall (digitDensity_laws hp j hr side i).1)
    (measurable_of_finite _).aestronglyMeasurable 2

omit hp in
lemma measurable_hybridDigits (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    Measurable (hybridDigits p hr ε) :=
  Measurable.of_eval (fun index => (measurable_observedDigit hr (ε index) index).comp
    (measurable_pi_apply index))

lemma map_hybridDigits (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    (law p j).map (hybridDigits p hr ε) =
      Measure.infinitePi (fun i => (digitReference p hr i).withDensity
        (fun d => ENNReal.ofReal (digitDensity p hr j (ε i) i d))) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  change (Measure.infinitePi (coordinateLaw p j)).map
    (fun ω i => observedDigit p hr (ε i) i (ω i)) = _
  rw [Measure.infinitePi_map_pi (coordinateLaw p j) (fun i => measurable_observedDigit hr (ε i) i)]
  congr 1
  funext i
  exact observedDigit_density hp j hr (ε i) i

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleMarginalDensity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleParameterData

theorem hybrid_density_of_coordinate_budget {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (fun i : ℕ => if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))))
    (hC : (∑' i : ℕ, if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) ≤ C) :
    ∃ H : Circle → ℝ, MemLp H 2 volume ∧ (0 ≤ᵐ[volume] H) ∧
      (∫ x, H x) = 1 ∧ eLpNorm H 2 volume ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law p j).map (hybridPoint p hr ε) =
        volume.withDensity (fun x => ENNReal.ofReal (H x)) := by
  let : ∀ i, IsProbabilityMeasure (digitReference p hr i) :=
    digitReference_isProbabilityMeasure p hr
  have he (i : ℕ) := (digitDensity_laws hp j hr (ε i) i).2.2
  have hsE : Summable (fun i =>
      ∫ d, (digitDensity p hr j (ε i) i d - 1) ^ 2 ∂digitReference p hr i) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun d => sq_nonneg _)) he hsum
  obtain ⟨H, hH, hnonneg, hmean, hnorm, hmeasure⟩ :=
    ProductDensity.exists_product_density
      (μ := fun i => digitReference p hr i)
      (h := fun i => digitDensity p hr j (ε i) i) (C := C)
      (fun i => digitDensity_memLp hp j hr (ε i) i)
      (fun i d => ((digitDensity_laws hp j hr (ε i) i).1 d).1)
      (fun i => (digitDensity_laws hp j hr (ε i) i).2.1)
      hsE ((hsE.tsum_le_tsum he hsum).trans hC)
  have htwo := MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible
  change MemLp H 2 (MixedRadix.digitLaw (MixedRadix.radices p.q) hr) at hH
  change (0 ≤ᵐ[MixedRadix.digitLaw (MixedRadix.radices p.q) hr] H) at hnonneg
  change (∫ d, H d ∂MixedRadix.digitLaw (MixedRadix.radices p.q) hr) = 1 at hmean
  change eLpNorm H 2 (MixedRadix.digitLaw (MixedRadix.radices p.q) hr) ≤ _ at hnorm
  change (MixedRadix.digitLaw (MixedRadix.radices p.q) hr).withDensity
    (fun d => ENNReal.ofReal (H d)) = _ at hmeasure
  let G : Circle → ℝ := H ∘ MixedRadix.circleCanonical (MixedRadix.radices p.q) hr
  have hcan := MixedRadix.circleCanonical_measurePreserving htwo hr
  have htransport := MixedRadix.digitLaw_circle_density_transport_ae htwo hr
    hH.aestronglyMeasurable.aemeasurable
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.comp_measurePreserving hcan
  · change ∀ᵐ x ∂(volume : Measure Circle),
      0 ≤ H (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr x)
    exact hcan.quasiMeasurePreserving.ae (p := fun d => 0 ≤ H d) hnonneg
  · have hHm : AEStronglyMeasurable H
        ((volume : Measure Circle).map (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr)) := by
      rw [hcan.map_eq]
      exact hH.aestronglyMeasurable
    have hi := integral_map hcan.measurable.aemeasurable hHm
    rw [hcan.map_eq] at hi
    exact hi.symm.trans hmean
  · exact htransport.2.le.trans hnorm
  · change (law p j).map
      (MixedRadix.circleValue ∘ hybridDigits p hr ε) = _
    rw [← Measure.map_map (MixedRadix.measurable_circleValue htwo)
      (measurable_hybridDigits hr ε), map_hybridDigits hp, ← hmeasure]
    exact htransport.1

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitMarginalLaws
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleParameterData

theorem digitMarginalLaws {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) : DigitMarginalLaws p hr := by
  refine ⟨Real.exp_pos _, fun j ε => ?_⟩
  obtain ⟨hs, hC⟩ := hp.circle_marginal_budget j
  have hs' : Summable (fun i : ℕ => if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
    simpa only [tag] using hs
  have hC' : (∑' i : ℕ, if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) ≤
      50 * ((∑' s : ℕ, kappa s ^ 2) + 1) := by
    simpa only [tag] using hC
  have h := hybrid_density_of_coordinate_budget hp j hr ε hs' hC'
  have he : 50 * ((∑' s : ℕ, kappa s ^ 2) + 1) / 2 =
      25 * ((∑' s : ℕ, kappa s ^ 2) + 1) := by ring
  simpa only [marginalBound, he] using h

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingHybrid
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Invariant233.CircleCoupling
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma uniformlyAbsolutelyContinuous_hybrids
    (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun ε : ℕ → Bool => (law p j).map (hybridPoint p hr ε)) := by
  apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities
    circleMeasure _ marginalBound
  intro ε
  obtain ⟨H, hH, hn, _, hb, he⟩ := (digitMarginalLaws hp hr).2 j ε
  change MemLp H 2 circleMeasure at hH
  change (0 ≤ᵐ[circleMeasure] H) at hn
  change eLpNorm H 2 circleMeasure ≤ ENNReal.ofReal marginalBound at hb
  change (law p j).map (hybridPoint p hr ε) =
    circleMeasure.withDensity (fun x => ENNReal.ofReal (H x)) at he
  refine ⟨hH.toLp H, ?_, ?_, ?_⟩
  · filter_upwards [hH.coeFn_toLp, hn] with x hx hnx
    rwa [hx]
  · rw [he]
    apply withDensity_congr_ae
    filter_upwards [hH.coeFn_toLp] with x hx
    rw [hx]
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hb

lemma hybridPoint_absolutelyContinuous (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    (law p j).map (hybridPoint p hr ε) ≪ circleMeasure :=
  (uniformlyAbsolutelyContinuous_hybrids hp j hr).absolutelyContinuous ε

lemma point_absolutelyContinuous (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    (law p j).map (point p hr side) ≪ circleMeasure :=
  hybridPoint_absolutelyContinuous hp j hr (fun _ => side)

lemma ae_ratio_cap_of_order (j : ℕ) (x y : Sample → Circle)
    (hx : Measurable x) (hy : Measurable y)
    (hax : (law p j).map x ≪ circleMeasure) (hay : (law p j).map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂law p j, ∀ i, p.coordinate i (x ω) ≤ p.coordinate i (y ω)) :
    ∀ᵐ ω ∂law p j, ∀ k : ℤ,
      0 < p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ∧
      p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ 1 := by
  obtain ⟨s, _, hs, _, hfinite, _⟩ := hp.exists_parameter_cocycle_set
  have hsx := ae_of_ae_map hx.aemeasurable (hax.ae_le hs)
  have hsy := ae_of_ae_map hy.aemeasurable (hay.ae_le hs)
  filter_upwards [horder, hsx, hsy] with ω ho hxs hys
  intro k
  refine ⟨div_pos (p.floorCocycle_pos θ k _) (p.floorCocycle_pos θ k _), ?_⟩
  have hcap := CircleWeights.cocycle_ratio_cap_finite_exceptions θ
    p.coordFrequency p.coordCost k (x ω) (y ω) ∅
    (fun i => (hp.coordCost_pos i).le)
    (fun i _ => by simpa only [p.coord_coordinate_eq] using ho i.2)
    (by simpa only [p.coord_coordinate_eq, p.coord_phase_eq] using hfinite _ hxs k)
    (by simpa only [p.coord_coordinate_eq, p.coord_phase_eq] using hfinite _ hys k)
  simpa only [floorCocycle, Finset.sum_empty, Real.exp_zero] using hcap

lemma ae_endpoint_ratio_cap_oai (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ k : ℤ,
      0 < p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ∧
      p.floorCocycle θ k (point p hr true ω) / p.floorCocycle θ k (point p hr false ω) ≤ 1 :=
  ae_ratio_cap_of_order hp j _ _ (measurable_point hp hr false) (measurable_point hp hr true)
    (point_absolutelyContinuous hp j hr false) (point_absolutelyContinuous hp j hr true)
    (ae_coordinates_ordered hp j hr)

end Invariant233.CircleCoupling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap_oai := @OAI.Invariant233.CircleCoupling.ae_endpoint_ratio_cap_oai
