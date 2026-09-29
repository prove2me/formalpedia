-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/15f7d574-0a8a-519e-8a77-b204871521c8

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn
import Theorems.Thm_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_zetaEntire_diagOne_mul
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Prod
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.MinMax
import Mathlib.Order.RelClasses
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul

set_option autoImplicit false

section StripHolomorphyPart

open MeasureTheory Filter Topology

namespace StripHolomorphy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem integrable_of_strip_bound (F : X → ℂ → ℂ) (hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun θ => F θ s) μ)
    (hdom : ∀ σ₁ σ₂ : ℝ, ∃ g : X → ℝ, Integrable g μ ∧ ∃ M : ℝ, ∀ᵐ θ ∂μ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖F θ s‖ ≤ g θ * Real.exp (M * |s.im|)) (s : ℂ) :
    Integrable (fun θ => F θ s) μ := by
  obtain ⟨g, hg, M, hae⟩ := hdom s.re s.re
  refine (hg.mul_const (Real.exp (M * |s.im|))).mono' (hmeas s) ?_
  exact hae.mono fun θ hθ => hθ s le_rfl le_rfl

private theorem norm_integral_le_of_strip_bound (F : X → ℂ → ℂ) {σ₁ σ₂ : ℝ} {g : X → ℝ} (hg : Integrable g μ) {M : ℝ}
    (hae : ∀ᵐ θ ∂μ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖F θ s‖ ≤ g θ * Real.exp (M * |s.im|))
    (s : ℂ) (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) :
    ‖∫ θ, F θ s ∂μ‖ ≤ (∫ θ, g θ ∂μ) * Real.exp (M * |s.im|) := by
  have hb : ∀ᵐ θ ∂μ, ‖F θ s‖ ≤ g θ * Real.exp (M * |s.im|) := hae.mono fun θ hθ => hθ s h₁ h₂
  exact (norm_integral_le_of_norm_le (hg.mul_const _) hb).trans_eq (integral_mul_const _ g)

private theorem differentiable_integral_of_strip_bound (F : X → ℂ → ℂ)
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun θ => F θ s) μ) (hent : ∀ᵐ θ ∂μ, Differentiable ℂ (F θ))
    (hdom : ∀ σ₁ σ₂ : ℝ, ∃ g : X → ℝ, Integrable g μ ∧ ∃ M : ℝ, ∀ᵐ θ ∂μ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖F θ s‖ ≤ g θ * Real.exp (M * |s.im|)) :
    Differentiable ℂ (fun s : ℂ => ∫ θ, F θ s ∂μ) := by
  intro s₀
  obtain ⟨g, hg, M, hae⟩ := hdom (s₀.re - 2) (s₀.re + 2)
  set K : ℝ := Real.exp (|M| * (|s₀.im| + 2)) with hK
  have hderiv_meas : AEStronglyMeasurable (fun θ => deriv (F θ) s₀) μ := by
    set t : ℕ → ℂ := fun n => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) with ht
    have ht0 : Tendsto t atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h := (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa [ht, Function.comp_def] using h
      · simp only [ht, Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n θ => (t n)⁻¹ • (F θ (s₀ + t n) - F θ s₀)) (fun n => ?_) ?_
    · exact ((hmeas (s₀ + t n)).sub (hmeas s₀)).const_smul ((t n)⁻¹)
    · refine hent.mono fun θ hθ => ?_
      exact (hasDerivAt_iff_tendsto_slope_zero.1 (hθ s₀).hasDerivAt).comp ht0
  have hball : Metric.ball s₀ 1 ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ zero_lt_one
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s₀)
    (F := fun s θ => F θ s) (F' := fun s θ => deriv (F θ) s) (bound := fun θ => ‖g θ‖ * K) hball
    (Eventually.of_forall hmeas) (integrable_of_strip_bound F hmeas hdom s₀) hderiv_meas ?_
    (hg.norm.mul_const K) ?_
  · exact key.2.differentiableAt
  ·
    refine (hent.and hae).mono fun θ ⟨hθ, hθb⟩ s hs => ?_
    have hs' : ‖s - s₀‖ < 1 := by rwa [Metric.mem_ball, Complex.dist_eq] at hs
    refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one hθ.diffContOnCl
      fun z hz => ?_).trans_eq (div_one _)
    have hz' : ‖z - s‖ = 1 := by rwa [Metric.mem_sphere, Complex.dist_eq] at hz
    have hzs₀ : ‖z - s₀‖ ≤ 2 := by
      have h := norm_add_le (z - s) (s - s₀)
      rw [sub_add_sub_cancel] at h
      linarith
    have hre := abs_le.1 ((Complex.abs_re_le_norm (z - s₀)).trans hzs₀)
    rw [Complex.sub_re] at hre
    have him := abs_le.1 ((Complex.abs_im_le_norm (z - s₀)).trans hzs₀)
    rw [Complex.sub_im] at him
    have hzim : |z.im| ≤ |s₀.im| + 2 := by
      have h1 := le_abs_self s₀.im
      have h2 := neg_abs_le s₀.im
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hexp : Real.exp (M * |z.im|) ≤ K := by
      rw [hK]
      refine Real.exp_le_exp.2 ?_
      calc M * |z.im| ≤ |M| * |z.im| := mul_le_mul_of_nonneg_right (le_abs_self M) (abs_nonneg _)
        _ ≤ |M| * (|s₀.im| + 2) := mul_le_mul_of_nonneg_left hzim (abs_nonneg M)
    calc ‖F θ z‖ ≤ g θ * Real.exp (M * |z.im|) := hθb z (by linarith [hre.1]) (by linarith [hre.2])
      _ ≤ ‖g θ‖ * Real.exp (M * |z.im|) :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm) (Real.exp_pos _).le
      _ ≤ ‖g θ‖ * K := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
  · exact hent.mono fun θ hθ s _ => (hθ s).hasDerivAt

private theorem differentiable_integral_and_strip_bound (F : X → ℂ → ℂ)
    (hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun θ => F θ s) μ) (hent : ∀ᵐ θ ∂μ, Differentiable ℂ (F θ))
    (hdom : ∀ σ₁ σ₂ : ℝ, ∃ g : X → ℝ, Integrable g μ ∧ ∃ M : ℝ, ∀ᵐ θ ∂μ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖F θ s‖ ≤ g θ * Real.exp (M * |s.im|)) :
    Differentiable ℂ (fun s : ℂ => ∫ θ, F θ s ∂μ) ∧
      ∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖∫ θ, F θ s ∂μ‖ ≤ C * Real.exp (A * |s.im|) := by
  refine ⟨differentiable_integral_of_strip_bound F hmeas hent hdom, fun σ₁ σ₂ => ?_⟩
  obtain ⟨g, hg, M, hae⟩ := hdom σ₁ σ₂
  exact ⟨∫ θ, g θ ∂μ, M, fun s h₁ h₂ => norm_integral_le_of_strip_bound F hg hae s h₁ h₂⟩

end StripHolomorphy

end StripHolomorphyPart

section PolarChartPart

open MeasureTheory Set Real

namespace SingularArrays

private theorem volume_setOf_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} :=
    measurableSet_eq_fun (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  refine Filter.Eventually.of_forall fun u => ?_
  have hsub : Prod.mk u ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} ⊆ {r₁ * u / r₀} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith [hv]
  exact measure_mono_null hsub (Real.volume_singleton)

private theorem volume_setOf_vector_on_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (Fin 2 → ℝ)) {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} = 0 := by
  have hpre : {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} =
      MeasurableEquiv.piFinTwo (fun _ => ℝ) ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} := by
    ext q; rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).map_eq]
  exact volume_setOf_line_eq_zero r₀ r₁ h

private theorem volume_setOf_det_eq_zero :
    (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0 := by
  have hdet : ∀ x : Fin 2 → Fin 2 → ℝ, (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := fun x => by
    rw [Matrix.det_fin_two]; rfl
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hpre : {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} =
      MeasurableEquiv.piFinTwo (fun _ => Fin 2 → ℝ) ⁻¹' S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hdet, hS]
    rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).map_eq]
  have hmeas : MeasurableSet S := by
    refine measurableSet_eq_fun ?_ measurable_const
    exact ((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_pi_apply 1).comp measurable_snd) |>.sub
      (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_pi_apply 0).comp measurable_snd))
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  have hae : ∀ᵐ r : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), r 0 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 (0 : ℝ)
  filter_upwards [hae] with r hr
  have hfib : Prod.mk r ⁻¹' S ⊆ {q : Fin 2 → ℝ | r 0 * q 1 = r 1 * q 0} := by
    intro q hq
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hq
    simp only [Set.mem_setOf_eq]
    linarith [hq]
  exact measure_mono_null hfib (volume_setOf_vector_on_line_eq_zero (r 0) (r 1) hr)

end SingularArrays

namespace ColumnPolar

private noncomputable def polarArray (p : ℝ × ℝ) (v : ℝ × ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![p.1 * cos p.2, v.1], ![p.1 * sin p.2, v.2]]

@[scoped simp] private theorem polarArray_zero_zero (p v : ℝ × ℝ) : polarArray p v 0 0 = p.1 * cos p.2 := rfl
@[scoped simp] private theorem polarArray_one_zero (p v : ℝ × ℝ) : polarArray p v 1 0 = p.1 * sin p.2 := rfl
@[scoped simp] private theorem polarArray_zero_one (p v : ℝ × ℝ) : polarArray p v 0 1 = v.1 := rfl
@[scoped simp] private theorem polarArray_one_one (p v : ℝ × ℝ) : polarArray p v 1 1 = v.2 := rfl

private def columns : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piCongrRight fun _ : Fin 2 => (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)).trans
    ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)
        (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)))

private theorem columns_apply (x : Fin 2 → Fin 2 → ℝ) : columns x = ((x 0 0, x 1 0), (x 0 1, x 1 1)) := rfl

private theorem columns_polarArray (p v : ℝ × ℝ) : columns (polarArray p v) = (polarCoord.symm p, v) := rfl

private theorem columns_symm_polarCoord_symm (p v : ℝ × ℝ) : columns.symm (polarCoord.symm p, v) = polarArray p v :=
  columns.symm_apply_eq.2 (columns_polarArray p v).symm

private theorem measurePreserving_columns : MeasurePreserving columns := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin 2 => (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)) :=
    volume_preserving_pi fun _ => volume_preserving_finTwoArrow ℝ
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 2)
  have h3 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)) (volume : Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ)))
      (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) :=
    (volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)
  exact (h3.comp h2).comp h1

private theorem source_prod_univ_ae_eq_univ :
    (polarCoord.source ×ˢ (univ : Set (ℝ × ℝ)) : Set ((ℝ × ℝ) × (ℝ × ℝ))) =ᵐ[volume] univ := by
  rw [ae_eq_univ]
  have hsub : (polarCoord.source ×ˢ (univ : Set (ℝ × ℝ)))ᶜ ⊆ polarCoord.sourceᶜ ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun q hq => ⟨fun h => hq ⟨h, trivial⟩, trivial⟩
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, ae_eq_univ.1 polarCoord_source_ae_eq_univ, zero_mul]

private scoped instance instIsAddHaarMeasureVolumeProdProd :
    Measure.IsAddHaarMeasure (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) :=
  Measure.prod.instIsAddHaarMeasure _ _

private theorem measurableSet_target_prod : MeasurableSet (polarCoord.target ×ˢ (univ : Set (ℝ × ℝ))) :=
  polarCoord.open_target.measurableSet.prod MeasurableSet.univ

private theorem hasFDerivAt_polar_fst (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    HasFDerivAt (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ))
      ((fderivPolarCoordSymm q.1).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))) q :=
  HasFDerivAt.prodMap q (hasFDerivAt_polarCoord_symm q.1) (hasFDerivAt_id q.2)

private theorem injOn_polar_fst :
    InjOn (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ)) (polarCoord.target ×ˢ (univ : Set (ℝ × ℝ))) := by
  intro q hq q' hq' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (polarCoord.symm.injOn hq.1 hq'.1 h1) h2

private theorem image_polar_fst :
    Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ) '' (polarCoord.target ×ˢ (univ : Set (ℝ × ℝ))) =
      polarCoord.source ×ˢ (univ : Set (ℝ × ℝ)) := by
  rw [prodMap_image_prod, image_id, polarCoord.symm_image_target_eq_source]

private theorem det_polar_fst (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    ((fderivPolarCoordSymm q.1).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))).det = q.1.1 := by
  have h := det_fderivPolarCoordSymm q.1
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one] at h ⊢
  exact h

private theorem integral_comp_polarCoord_symm_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (ℝ × ℝ) × (ℝ × ℝ) → E) :
    (∫ q in polarCoord.target ×ˢ (univ : Set (ℝ × ℝ)), q.1.1 • G (polarCoord.symm q.1, q.2)) = ∫ q, G q := by
  symm
  calc ∫ q, G q = ∫ q in polarCoord.source ×ˢ (univ : Set (ℝ × ℝ)), G q := by
        rw [← setIntegral_univ]
        exact (setIntegral_congr_set source_prod_univ_ae_eq_univ).symm
    _ = ∫ q in polarCoord.target ×ˢ (univ : Set (ℝ × ℝ)),
          |((fderivPolarCoordSymm q.1).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))).det| •
            G (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ) q) := by
        rw [← image_polar_fst]
        exact integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_target_prod
          (fun q _ => (hasFDerivAt_polar_fst q).hasFDerivWithinAt) injOn_polar_fst G
    _ = ∫ q in polarCoord.target ×ˢ (univ : Set (ℝ × ℝ)), q.1.1 • G (polarCoord.symm q.1, q.2) := by
        refine setIntegral_congr_fun measurableSet_target_prod fun q hq => ?_
        rw [det_polar_fst, abs_of_pos hq.1.1]
        rfl

private theorem integral_eq_integral_polarArray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin 2 → Fin 2 → ℝ) → E) :
    ∫ x, f x = ∫ q in polarCoord.target ×ˢ (univ : Set (ℝ × ℝ)), q.1.1 • f (polarArray q.1 q.2) := by
  have h1 := measurePreserving_columns.integral_comp' fun q => f (columns.symm q)
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [h1, ← integral_comp_polarCoord_symm_fst fun q => f (columns.symm q)]
  refine setIntegral_congr_fun measurableSet_target_prod fun q _ => ?_
  simp only [columns_symm_polarCoord_symm]

private theorem integrable_iff_integrableOn_polarArray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin 2 → Fin 2 → ℝ) → E) :
    Integrable f ↔
      IntegrableOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1.1 • f (polarArray q.1 q.2))
        (polarCoord.target ×ˢ (univ : Set (ℝ × ℝ))) := by
  have e1 : Integrable f ↔ Integrable (f ∘ columns.symm) :=
    ((measurePreserving_columns.symm columns).integrable_comp_emb columns.symm.measurableEmbedding).symm
  rw [e1, ← integrableOn_univ, ← integrableOn_congr_set_ae source_prod_univ_ae_eq_univ, ← image_polar_fst,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_target_prod
      (fun q _ => (hasFDerivAt_polar_fst q).hasFDerivWithinAt) injOn_polar_fst]
  refine integrableOn_congr_fun (fun q hq => ?_) measurableSet_target_prod
  have hρ : (0 : ℝ) < q.1.1 := hq.1.1
  have hc : columns.symm (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ) q) = polarArray q.1 q.2 :=
    columns_symm_polarCoord_symm q.1 q.2
  simp only [det_polar_fst, abs_of_pos hρ, Function.comp_apply, hc]

private theorem ae_det_ne_zero : ∀ᵐ x : Fin 2 → Fin 2 → ℝ, (Matrix.of x).det ≠ 0 := by
  have h := compl_mem_ae_iff.2 SingularArrays.volume_setOf_det_eq_zero
  filter_upwards [h] with x hx
  exact hx

private theorem ae_not_firstColumn_eq_zero : ∀ᵐ x : Fin 2 → Fin 2 → ℝ, ¬ (x 0 0 = 0 ∧ x 1 0 = 0) := by
  filter_upwards [ae_det_ne_zero] with x hx h
  apply hx
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, h.1, h.2, zero_mul, mul_zero, sub_zero]

end ColumnPolar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace ColumnPolar

private theorem polarCoord_symm_apply' (p : ℝ × ℝ) : polarCoord.symm p = (p.1 * cos p.2, p.1 * sin p.2) := rfl

private theorem measurableSet_halfStrip_prod :
    MeasurableSet (((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) :=
  (MeasurableSet.univ.prod measurableSet_Ioo).prod MeasurableSet.univ

private theorem measurableSet_punctured_prod :
    MeasurableSet ((({0} : Set ℝ)ᶜ ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) :=
  ((measurableSet_singleton (0 : ℝ)).compl.prod measurableSet_Ioo).prod MeasurableSet.univ

private theorem punctured_prod_ae_eq :
    ((({0} : Set ℝ)ᶜ ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ)) : Set ((ℝ × ℝ) × (ℝ × ℝ))) =ᵐ[volume]
      ((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ)) := by
  have hnull : volume ((({0} : Set ℝ) ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set (ℝ × ℝ))) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton,
      zero_mul, zero_mul]
  rw [ae_eq_set]
  refine ⟨?_, measure_mono_null (fun q hq => ?_) hnull⟩
  · rw [diff_eq_empty.2 (prod_mono (prod_mono (subset_univ _) subset_rfl) subset_rfl), measure_empty]
  · refine ⟨⟨?_, trivial⟩, trivial⟩
    by_contra h0
    exact hq.2 ⟨⟨h0, hq.1.1.2⟩, trivial⟩

private theorem injOn_half :
    InjOn (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ)) ((({0} : Set ℝ)ᶜ ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) := by
  rintro ⟨⟨ρ, θ⟩, v⟩ ⟨⟨hρ, hθ⟩, -⟩ ⟨⟨ρ', θ'⟩, v'⟩ ⟨⟨hρ', hθ'⟩, -⟩ h
  simp only [Prod.map, polarCoord_symm_apply', id, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hρ'0 : ρ' ≠ 0 := fun h0 => hρ' h0
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hs' : 0 < sin θ' := sin_pos_of_pos_of_lt_pi hθ'.1 hθ'.2
  have hρρ : ρ = ρ' := by
    have e : (ρ * cos θ) ^ 2 = (ρ' * cos θ') ^ 2 := by rw [h1]
    have e' : (ρ * sin θ) ^ 2 = (ρ' * sin θ') ^ 2 := by rw [h2]
    have hsq : ρ ^ 2 = ρ' ^ 2 := by
      linear_combination (-ρ ^ 2) * sin_sq_add_cos_sq θ + ρ' ^ 2 * sin_sq_add_cos_sq θ' + e + e'
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hh | hh
    · exact hh
    · exfalso
      rw [hh] at h2
      have hzero : ρ' * (sin θ + sin θ') = 0 := by linarith
      rcases mul_eq_zero.1 hzero with h0 | h0
      · exact hρ'0 h0
      · linarith
  have hθθ : θ = θ' := by
    rw [hρρ] at h1
    exact injOn_cos ⟨hθ.1.le, hθ.2.le⟩ ⟨hθ'.1.le, hθ'.2.le⟩ (mul_left_cancel₀ hρ'0 h1)
  rw [hρρ, hθθ, h3]

private theorem image_half_ae_eq_univ :
    (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ) '' ((({0} : Set ℝ)ᶜ ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) :
      Set ((ℝ × ℝ) × (ℝ × ℝ))) =ᵐ[volume] univ := by
  rw [ae_eq_univ]
  have hnull : volume (((univ : Set ℝ) ×ˢ ({0} : Set ℝ)) ×ˢ (univ : Set (ℝ × ℝ))) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton,
      mul_zero, zero_mul]
  refine measure_mono_null (fun q hq => ?_) hnull
  refine ⟨⟨trivial, ?_⟩, trivial⟩
  by_contra hy
  have hy' : q.1.2 ≠ 0 := fun h0 => hy h0
  apply hq
  rcases hy'.lt_or_gt with hneg | hpos
  ·
    have hwsrc : -q.1 ∈ polarCoord.source := by
      refine Or.inr ?_
      show (-q.1).2 ≠ 0
      rw [Prod.snd_neg]
      exact neg_ne_zero.2 hy'
    have hp : polarCoord (-q.1) ∈ polarCoord.target := polarCoord.map_source hwsrc
    have hr : 0 < (polarCoord (-q.1)).1 := hp.1
    have hinv : polarCoord.symm (polarCoord (-q.1)) = -q.1 := polarCoord.left_inv hwsrc
    have him : 0 < (Complex.equivRealProd.symm (-q.1)).im := by simp [hneg]
    have harg : (polarCoord (-q.1)).2 ∈ Ioo 0 π := by
      refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 him.le) fun h0 => ?_, Complex.arg_lt_pi_iff.2 (Or.inr him.ne')⟩
      have := (Complex.arg_eq_zero_iff.1 h0.symm).2
      linarith
    refine ⟨((-(polarCoord (-q.1)).1, (polarCoord (-q.1)).2), q.2),
      ⟨⟨fun h0 => (neg_ne_zero.2 hr.ne') h0, harg⟩, trivial⟩, ?_⟩
    refine Prod.ext ?_ rfl
    show polarCoord.symm (-(polarCoord (-q.1)).1, (polarCoord (-q.1)).2) = q.1
    have h1 : polarCoord.symm (-(polarCoord (-q.1)).1, (polarCoord (-q.1)).2) =
        -polarCoord.symm (polarCoord (-q.1)) := by
      rw [polarCoord_symm_apply', polarCoord_symm_apply']
      ext <;> simp only [Prod.fst_neg, Prod.snd_neg, neg_mul]
    rw [h1, hinv, neg_neg]
  ·
    have hsrc : q.1 ∈ polarCoord.source := Or.inr hy'
    have hp : polarCoord q.1 ∈ polarCoord.target := polarCoord.map_source hsrc
    have hr : 0 < (polarCoord q.1).1 := hp.1
    have hinv : polarCoord.symm (polarCoord q.1) = q.1 := polarCoord.left_inv hsrc
    have him : 0 < (Complex.equivRealProd.symm q.1).im := by simp [hpos]
    have harg : (polarCoord q.1).2 ∈ Ioo 0 π := by
      refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 him.le) fun h0 => ?_, Complex.arg_lt_pi_iff.2 (Or.inr him.ne')⟩
      have := (Complex.arg_eq_zero_iff.1 h0.symm).2
      linarith
    exact ⟨(polarCoord q.1, q.2), ⟨⟨fun h0 => hr.ne' h0, harg⟩, trivial⟩, Prod.ext hinv rfl⟩

private theorem integral_comp_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : (ℝ × ℝ) × (ℝ × ℝ) → E) :
    (∫ q in ((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ)), |q.1.1| • G (polarCoord.symm q.1, q.2)) =
      ∫ q, G q := by
  symm
  calc ∫ q, G q
      = ∫ q in Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ) ''
          ((({0} : Set ℝ)ᶜ ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))), G q := by
        rw [← setIntegral_univ]
        exact (setIntegral_congr_set image_half_ae_eq_univ).symm
    _ = ∫ q in (({0} : Set ℝ)ᶜ ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ)),
          |((fderivPolarCoordSymm q.1).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))).det| •
            G (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ) q) :=
        integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_punctured_prod
          (fun q _ => (hasFDerivAt_polar_fst q).hasFDerivWithinAt) injOn_half G
    _ = ∫ q in (({0} : Set ℝ)ᶜ ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ)), |q.1.1| • G (polarCoord.symm q.1, q.2) := by
        refine setIntegral_congr_fun measurableSet_punctured_prod fun q _ => ?_
        rw [det_polar_fst]
        rfl
    _ = ∫ q in ((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ)), |q.1.1| • G (polarCoord.symm q.1, q.2) :=
        setIntegral_congr_set punctured_prod_ae_eq

private theorem integral_eq_integral_polarArray_halfCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin 2 → Fin 2 → ℝ) → E) :
    ∫ x, f x = ∫ q in ((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ)), |q.1.1| • f (polarArray q.1 q.2) := by
  have h1 := measurePreserving_columns.integral_comp' fun q => f (columns.symm q)
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [h1, ← integral_comp_half fun q => f (columns.symm q)]
  refine setIntegral_congr_fun measurableSet_halfStrip_prod fun q _ => ?_
  simp only [columns_symm_polarCoord_symm]

private theorem integrable_iff_integrableOn_polarArray_halfCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin 2 → Fin 2 → ℝ) → E) :
    Integrable f ↔
      IntegrableOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1| • f (polarArray q.1 q.2))
        (((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have e1 : Integrable f ↔ Integrable (f ∘ columns.symm) :=
    ((measurePreserving_columns.symm columns).integrable_comp_emb columns.symm.measurableEmbedding).symm
  rw [e1, ← integrableOn_univ, ← integrableOn_congr_set_ae image_half_ae_eq_univ,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_punctured_prod
      (fun q _ => (hasFDerivAt_polar_fst q).hasFDerivWithinAt) injOn_half,
    integrableOn_congr_set_ae punctured_prod_ae_eq]
  refine integrableOn_congr_fun (fun q _ => ?_) measurableSet_halfStrip_prod
  have hc : columns.symm (Prod.map polarCoord.symm (id : ℝ × ℝ → ℝ × ℝ) q) = polarArray q.1 q.2 :=
    columns_symm_polarCoord_symm q.1 q.2
  simp only [det_polar_fst, Function.comp_apply, hc]

private theorem integral_eq_integral_integral_integral_polarArray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : (Fin 2 → Fin 2 → ℝ) → E) (hf : Integrable f) :
    ∫ x, f x = ∫ w : ℝ × ℝ, ∫ θ in Ioo 0 π, ∫ ρ : ℝ, |ρ| • f (polarArray (ρ, θ) w) := by
  have hg := (integrable_iff_integrableOn_polarArray_halfCircle f).1 hf
  have hS : (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict (((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) =
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioo 0 π))).prod (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), ← Measure.prod_restrict, Measure.restrict_univ,
      Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [integral_eq_integral_polarArray_halfCircle f, hS]
  rw [IntegrableOn, hS] at hg
  rw [integral_prod_symm _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_left_ae] with w hw
  exact integral_prod_symm _ hw

private def shuffle : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) × ℝ :=
  (MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ℝ × ℝ)) MeasurableEquiv.prodComm)).trans
    MeasurableEquiv.prodAssoc.symm

private theorem shuffle_apply (q : (ℝ × ℝ) × (ℝ × ℝ)) : shuffle q = ((q.2, q.1.2), q.1.1) := rfl

private theorem measurePreserving_shuffle :
    MeasurePreserving shuffle
      (((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioo 0 π))).prod (volume : Measure (ℝ × ℝ)))
      (((volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).restrict (Ioo 0 π))).prod (volume : Measure ℝ)) := by
  have h1 : MeasurePreserving (Prod.swap : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ))
      (((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioo 0 π))).prod (volume : Measure (ℝ × ℝ)))
      ((volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioo 0 π)))) :=
    Measure.measurePreserving_swap
  have h2 : MeasurePreserving (Prod.map (id : ℝ × ℝ → ℝ × ℝ) (Prod.swap : ℝ × ℝ → ℝ × ℝ))
      ((volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioo 0 π))))
      ((volume : Measure (ℝ × ℝ)).prod (((volume : Measure ℝ).restrict (Ioo 0 π)).prod (volume : Measure ℝ))) :=
    (MeasurePreserving.id _).prod Measure.measurePreserving_swap
  have h3 := (measurePreserving_prodAssoc (volume : Measure (ℝ × ℝ)) ((volume : Measure ℝ).restrict (Ioo 0 π))
    (volume : Measure ℝ)).symm MeasurableEquiv.prodAssoc
  exact (h3.comp h2).comp h1

private theorem integral_eq_integral_prod_integral_polarArray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : (Fin 2 → Fin 2 → ℝ) → E) (hf : Integrable f) :
    ∫ x, f x = ∫ r : (ℝ × ℝ) × ℝ, (∫ ρ : ℝ, |ρ| • f (polarArray (ρ, r.2) r.1))
      ∂((volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).restrict (Ioo 0 π))) := by
  have hg := (integrable_iff_integrableOn_polarArray_halfCircle f).1 hf
  have hS : (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict (((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) =
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioo 0 π))).prod (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), ← Measure.prod_restrict, Measure.restrict_univ,
      Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [integral_eq_integral_polarArray_halfCircle f, hS]
  rw [IntegrableOn, hS] at hg
  set lam : Measure ℝ := (volume : Measure ℝ).restrict (Ioo 0 π) with hlam
  set P : Measure ((ℝ × ℝ) × ℝ) := (volume : Measure (ℝ × ℝ)).prod lam with hP
  set h' : ((ℝ × ℝ) × ℝ) × ℝ → E := fun y => |y.2| • f (polarArray (y.2, y.1.2) y.1.1) with hh'_def
  have hcomp : (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1| • f (polarArray q.1 q.2)) = h' ∘ shuffle := by
    funext q
    simp only [Function.comp_apply, shuffle_apply, hh'_def]
  have hh' : Integrable h' (P.prod (volume : Measure ℝ)) := by
    rw [hcomp] at hg
    exact (measurePreserving_shuffle.integrable_comp_emb shuffle.measurableEmbedding).1 hg
  calc ∫ q, |q.1.1| • f (polarArray q.1 q.2) ∂(((volume : Measure ℝ).prod lam).prod (volume : Measure (ℝ × ℝ)))
      = ∫ q, h' (shuffle q) ∂(((volume : Measure ℝ).prod lam).prod (volume : Measure (ℝ × ℝ))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only [shuffle_apply, hh'_def]
    _ = ∫ y, h' y ∂(P.prod (volume : Measure ℝ)) :=
        measurePreserving_shuffle.integral_comp shuffle.measurableEmbedding h'
    _ = ∫ r : (ℝ × ℝ) × ℝ, (∫ ρ : ℝ, h' (r, ρ)) ∂P := integral_prod h' hh'

private theorem integral_eq_setIntegral_integral_polarArray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : (Fin 2 → Fin 2 → ℝ) → E) (hf : Integrable f) :
    ∫ x, f x = ∫ r in (univ : Set (ℝ × ℝ)) ×ˢ Ioo 0 π, ∫ ρ : ℝ, |ρ| • f (polarArray (ρ, r.2) r.1) := by
  rw [integral_eq_integral_prod_integral_polarArray f hf, Measure.volume_eq_prod (ℝ × ℝ) ℝ, ← Measure.prod_restrict,
    Measure.restrict_univ]

end ColumnPolar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace ColumnPolar

private theorem restrict_halfStrip_prod_eq_prod :
    (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict (((univ : Set ℝ) ×ˢ Ioo 0 π) ×ˢ (univ : Set (ℝ × ℝ))) =
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioo 0 π))).prod (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, Measure.restrict_univ]

private theorem integrable_iff_integrable_polarArray_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin 2 → Fin 2 → ℝ) → E) :
    Integrable f ↔
      Integrable (fun p : ((ℝ × ℝ) × ℝ) × ℝ => |p.2| • f (polarArray (p.2, p.1.2) p.1.1))
        (((volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).restrict (Ioo 0 π))).prod (volume : Measure ℝ)) := by
  rw [integrable_iff_integrableOn_polarArray_halfCircle f, IntegrableOn, restrict_halfStrip_prod_eq_prod,
    ← measurePreserving_shuffle.integrable_comp_emb shuffle.measurableEmbedding]
  rfl

end ColumnPolar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end PolarChartPart
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace CharacterAtReal

open NumberField NumberField.StandardAddChar AutomorphicForm.StandardKernel

private theorem psiArch_eq_exp (x : InfiniteAdeleRing ℚ) :
    psiArch x = Complex.exp ((2 * Real.pi * Complex.I) * ((realCoord x : ℝ) : ℂ)) := by
  rw [psiArch_apply, finprod_eq_prod_of_fintype, Fintype.prod_unique, psiArchPlace_apply, realCoord_apply]
  rfl

private theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r := by
  rw [realCoord_apply]
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).apply_symm_apply r

private theorem realCoord_algebraMap (q : ℚ) : realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) q) = (q : ℝ) := by
  have h : realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ)) = Rat.castHom ℝ := Subsingleton.elim _ _
  have := RingHom.congr_fun h q
  rw [RingHom.comp_apply] at this
  exact this

private theorem psiInf_ofReal (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ) (a : ℚ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) (r : ℝ) :
    psiInf (ofReal r) = Complex.exp ((2 * Real.pi * Complex.I) * (((a : ℝ) * r : ℝ) : ℂ)) := by
  rw [hpsiInf, psiArch_eq_exp, map_mul, realCoord_algebraMap, realCoord_ofReal]

end CharacterAtReal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

noncomputable section

open MeasureTheory NumberField AutomorphicForm LanglandsTunnell.Converse

namespace DualStripDecay

section QuasiChar

p2m_open "LanglandsTunnell.Converse.ArchR"

private theorem quasiChar_mul (u : ℂ) (a : ZMod 2) (x y : ℝ) :
    quasiChar u a (x * y) = quasiChar u a x * quasiChar u a y := by
  unfold quasiChar
  rw [abs_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg x) (abs_nonneg y)]
  split_ifs with ha
  · ring
  · rw [sign_mul, SignType.coe_mul, Complex.ofReal_mul]
    ring

private theorem signType_sign_inv_eq (y : ℝ) : SignType.sign y⁻¹ = SignType.sign y := by
  rcases lt_trichotomy y 0 with h | h | h
  · rw [sign_neg (inv_lt_zero.mpr h), sign_neg h]
  · rw [h, inv_zero]
  · rw [sign_pos (inv_pos.mpr h), sign_pos h]

private theorem quasiChar_inv (u : ℂ) (a : ZMod 2) (y : ℝ) : quasiChar u a y⁻¹ = quasiChar (-u) a y := by
  unfold quasiChar
  have h0 : ((|y| : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (abs_nonneg y)]
    exact Real.pi_ne_zero.symm
  rw [abs_inv, Complex.ofReal_inv, Complex.inv_cpow_eq_ite, if_neg h0, ← Complex.cpow_neg, signType_sign_inv_eq]

private theorem quasiChar_mul_quasiChar (u u' : ℂ) (a a' : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    quasiChar u a y * quasiChar u' a' y = quasiChar (u + u') (a + a') y := by
  unfold quasiChar
  have hpos : (0 : ℝ) < |y| := abs_pos.mpr hy
  have hne : ((|y| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [Complex.cpow_add _ _ hne]
  have hsign : ((SignType.sign y : ℝ) : ℂ) * ((SignType.sign y : ℝ) : ℂ) = 1 := by
    rcases lt_or_gt_of_ne hy with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]
  have h2 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 a' with rfl | rfl <;> simp [h11] <;>
    first
    | ring1
    | linear_combination ((|y| : ℝ) : ℂ) ^ u * ((|y| : ℝ) : ℂ) ^ u' * hsign

end QuasiChar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

section
open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR DualStripDecay

namespace RadialTransport

private theorem det_diagOne (ρ : ℝ) : (diagOne ρ).det = ρ := by
  simp [diagOne, Matrix.det_fin_two_of]

private theorem det_mul_diagOne (x : Matrix (Fin 2) (Fin 2) ℝ) (ρ : ℝ) : (x * diagOne ρ).det = x.det * ρ := by
  rw [Matrix.det_mul, det_diagOne]

private theorem diagOne_mul_diagOne (α β : ℝ) : diagOne α * diagOne β = diagOne (α * β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagOne_one : diagOne (1 : ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagOne]

private theorem diagOne_inv {ρ : ℝ} (hρ : ρ ≠ 0) : (diagOne ρ)⁻¹ = diagOne ρ⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [diagOne_mul_diagOne, mul_inv_cancel₀ hρ, diagOne_one]

private theorem diagOne_mul_mul_diagOne_inv (a : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    diagOne a * (x * diagOne ρ)⁻¹ = diagOne (a * ρ⁻¹) * x⁻¹ := by
  rw [Matrix.mul_inv_rev, diagOne_inv hρ, ← Matrix.mul_assoc, diagOne_mul_diagOne]

private theorem det_mul_diagOne_ne_zero {x : Matrix (Fin 2) (Fin 2) ℝ} (hx : x.det ≠ 0) {ρ : ℝ} (hρ : ρ ≠ 0) :
    (x * diagOne ρ).det ≠ 0 := by
  rw [det_mul_diagOne]; exact mul_ne_zero hx hρ

private theorem quasiChar_zero_sign (u : ℂ) (y : ℝ) : quasiChar u 0 y = ((|y| : ℝ) : ℂ) ^ u := by
  simp [quasiChar]

private theorem zmod2_add_self (b : ZMod 2) : b + b = 0 := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl <;> decide

private theorem quasiChar_inv_eq
    (u : ℂ) (b : ZMod 2) {y : ℝ} (hy : y ≠ 0) : (quasiChar u b y)⁻¹ = quasiChar (-u) b y := by
  have h : quasiChar u b y * quasiChar (-u) b y = 1 := by
    rw [quasiChar_mul_quasiChar u (-u) b b hy, add_neg_cancel, zmod2_add_self, quasiChar_zero_sign, Complex.cpow_zero]
  exact inv_eq_of_mul_eq_one_right h

private theorem ofReal_inv_sq_abs (y : ℝ) : ((((|y| ^ 2)⁻¹ : ℝ)) : ℂ) = quasiChar (-2) 0 y := by
  rw [quasiChar_zero_sign, show (-2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  ring

private theorem abs_cpow_eq_quasiChar (y : ℝ) (z : ℂ) : ((|y| : ℝ) : ℂ) ^ z = quasiChar z 0 y :=
  (quasiChar_zero_sign z y).symm

private theorem rho_bookkeeping (u₃ t s : ℂ) (a₃ e : ZMod 2) (d a : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ((|ρ| : ℝ) : ℂ) * ((|ρ| : ℝ) : ℂ)⁻¹ * quasiChar (u₃ + 2) a₃ (d * ρ) * (((|d * ρ| ^ 2)⁻¹ : ℝ) : ℂ) *
        ((quasiChar t e (a * ρ⁻¹))⁻¹ * ((|a * ρ⁻¹| : ℝ) : ℂ) ^ (1 - s)) =
      quasiChar (s + u₃ + t - 1) (a₃ + e) ρ *
        (quasiChar (u₃ + 2) a₃ d * (((|d| ^ 2)⁻¹ : ℝ) : ℂ) * (quasiChar t e a)⁻¹ * ((|a| : ℝ) : ℂ) ^ (1 - s)) := by
  have hρ' : ((|ρ| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mpr hρ).ne'
  rw [mul_inv_cancel₀ hρ', one_mul, quasiChar_mul (u₃ + 2) a₃ d ρ, ofReal_inv_sq_abs (d * ρ), quasiChar_mul (-2) 0 d ρ,
    quasiChar_mul t e a ρ⁻¹, quasiChar_inv t e ρ, mul_inv, quasiChar_inv_eq (-t) e hρ, neg_neg,
    abs_cpow_eq_quasiChar (a * ρ⁻¹), quasiChar_mul (1 - s) 0 a ρ⁻¹, quasiChar_inv (1 - s) 0 ρ,
    abs_cpow_eq_quasiChar a, ofReal_inv_sq_abs d]
  have hmerge : quasiChar (u₃ + 2) a₃ ρ * quasiChar (-2) 0 ρ * quasiChar t e ρ * quasiChar (-(1 - s)) 0 ρ =
      quasiChar (s + u₃ + t - 1) (a₃ + e) ρ := by
    rw [quasiChar_mul_quasiChar _ _ _ _ hρ, quasiChar_mul_quasiChar _ _ _ _ hρ, quasiChar_mul_quasiChar _ _ _ _ hρ]
    congr 1
    · ring
    · simp
  rw [← hmerge]
  ring

private def parity (b : ZMod 2) : ℕ := if b = 0 then 0 else 1

private theorem parity_cast (b : ZMod 2) : ((parity b : ℕ) : ℂ) = signShift b := by
  unfold parity signShift
  split_ifs <;> simp

private theorem coe_signType_sign (ρ : ℝ) : ((SignType.sign ρ : ℝ)) = Real.sign ρ := by
  rcases lt_trichotomy ρ 0 with h | rfl | h
  · rw [sign_neg h, Real.sign_of_neg h]; simp
  · simp
  · rw [sign_pos h, Real.sign_of_pos h]; simp

private theorem quasiChar_eq_sign_pow_mul (z : ℂ) (b : ZMod 2) (ρ : ℝ) :
    quasiChar z b ρ = (Real.sign ρ : ℂ) ^ parity b * ((|ρ| : ℝ) : ℂ) ^ z := by
  unfold quasiChar parity
  split_ifs with hb
  · simp
  · rw [pow_one, coe_signType_sign, mul_comm]

end RadialTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

noncomputable section

namespace AssemblyBridges

open NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.Converse.ArchR CharacterAtReal
open NumberField.StandardAddChar

private theorem godementInner3_eq
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ) (a : ℚ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 psiInf (fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M)
        h m =
      ∫ v : Fin 2 → ℝ,
        (MvPolynomial.eval (fun ib : Fin 2 × Fin 3 =>
            (((h * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b]) ib.1 ib.2 : ℝ) : ℂ)) p *
          gaussian3 (h * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])) *
        Complex.exp ((2 * Real.pi * Complex.I) * (((a : ℝ) * (-(v 1)) : ℝ) : ℂ)) := by
  unfold godementInner3
  congr 1
  funext v
  rw [psiInf_ofReal psiInf a hpsiInf]

private noncomputable def unitArray
    (θ : ℝ) (w : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, w.1; Real.sin θ, w.2]

private theorem of_polarArray (ρ θ : ℝ) (w : ℝ × ℝ) :
    Matrix.of (ColumnPolar.polarArray (ρ, θ) w) = unitArray θ w * diagOne ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ColumnPolar.polarArray, unitArray, diagOne, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem unitArray_slice (θ : ℝ) (w : ℝ × ℝ) : unitArray θ w 0 0 ^ 2 + unitArray θ w 1 0 ^ 2 = 1 := by
  simp [unitArray, Real.cos_sq_add_sin_sq]

private theorem det_unitArray (θ : ℝ) (w : ℝ × ℝ) : (unitArray θ w).det = Real.cos θ * w.2 - w.1 * Real.sin θ := by
  simp [unitArray, Matrix.det_fin_two_of]

private theorem continuous_unitArray : Continuous (fun r : (ℝ × ℝ) × ℝ => unitArray r.2 r.1) := by
  unfold unitArray
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end AssemblyBridges
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

section
open MeasureTheory LanglandsTunnell.Converse.ArchR LanglandsTunnell.CubicInduction

namespace ArrayGaussian

private theorem integral_comp_mulVec {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) {f : (Fin 2 → ℝ) → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    ∫ v : Fin 2 → ℝ, f (M.mulVec v) = (|M.det|⁻¹ : ℝ) * ∫ y : Fin 2 → ℝ, f y := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hM
  have hφ : AEMeasurable (Matrix.toLin' M) (volume : Measure (Fin 2 → ℝ)) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable.aemeasurable
  have hfm : AEStronglyMeasurable f (Measure.map (Matrix.toLin' M) volume) := by
    rw [hmap]; exact hf.smul_measure _
  have h1 : ∫ v : Fin 2 → ℝ, f (M.mulVec v) = ∫ y, f y ∂(Measure.map (Matrix.toLin' M) volume) := by
    rw [integral_map hφ hfm]
    simp only [Matrix.toLin'_apply]
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  exact Complex.real_smul

private theorem integral_cexp_mulVec
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) {b : ℝ} (hb : 0 < b) (c : Fin 2 → ℂ) :
    ∫ v : Fin 2 → ℝ, Complex.exp (-(b : ℂ) * ∑ i, ((M.mulVec v i : ℝ) : ℂ) ^ 2 + ∑ i, c i * ((M.mulVec v i : ℝ) : ℂ)) =
      (|M.det|⁻¹ : ℝ) * ((Real.pi / b : ℝ) * Complex.exp ((∑ i, c i ^ 2) / (4 * (b : ℂ)))) := by
  have hcont : Continuous fun y : Fin 2 → ℝ =>
      Complex.exp (-(b : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, c i * ((y i : ℝ) : ℂ)) := by fun_prop
  rw [integral_comp_mulVec hM hcont.aestronglyMeasurable]
  congr 1
  have hbre : 0 < ((b : ℂ)).re := by simpa using hb
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add hbre c, Fintype.card_fin]
  congr 1
  rw [show ((2 : ℕ) / 2 : ℂ) = 1 by norm_num, Complex.cpow_one]
  push_cast
  ring

end ArrayGaussian
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace GaussianMoments

private noncomputable def gk (b : ℝ) (c : ℂ) (k : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ k * Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + c * (y : ℂ))

private lemma norm_gk (b : ℝ) (c : ℂ) (k : ℕ) (y : ℝ) :
    ‖gk b c k y‖ = |y| ^ k * Real.exp (-b * y ^ 2 + c.re * y) := by
  unfold gk
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  congr 2
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]

private lemma integrable_gk {b : ℝ} (hb : 0 < b) (c : ℂ) (k : ℕ) : Integrable (gk b c k) := by
  have hb2 : 0 < b / 2 := by positivity
  have hdom : Integrable (fun y : ℝ => Real.exp (c.re ^ 2 / (2 * b)) * (y ^ k * Real.exp (-(b / 2) * y ^ 2))) := by
    refine Integrable.const_mul ?_ _
    have := integrable_rpow_mul_exp_neg_mul_sq hb2 (s := (k : ℝ)) (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)
    refine this.congr ?_
    filter_upwards with y
    simp [Real.rpow_natCast]
  refine hdom.norm.mono' ?_ ?_
  · unfold gk
    fun_prop
  · filter_upwards with y
    rw [norm_gk, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Real.abs_exp, Real.abs_exp]
    have hlin : c.re * y ≤ c.re ^ 2 / (2 * b) + b / 2 * y ^ 2 := by
      rw [← sub_nonneg]
      have hid : c.re ^ 2 / (2 * b) + b / 2 * y ^ 2 - c.re * y = (b * y - c.re) ^ 2 / (2 * b) := by
        field_simp
        ring
      rw [hid]
      positivity
    have hexp : Real.exp (-b * y ^ 2 + c.re * y) ≤ Real.exp (c.re ^ 2 / (2 * b)) * Real.exp (-(b / 2) * y ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [hlin])
    calc |y| ^ k * Real.exp (-b * y ^ 2 + c.re * y)
        ≤ |y| ^ k * (Real.exp (c.re ^ 2 / (2 * b)) * Real.exp (-(b / 2) * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp (c.re ^ 2 / (2 * b)) * (|y| ^ k * Real.exp (-(b / 2) * y ^ 2)) := by ring

private noncomputable def _root_.GaussianMoments.mk (b : ℝ) (c : ℂ) (k : ℕ) : ℂ := ∫ y : ℝ, gk b c k y

p2m_export "GaussianMoments" "mk"
private lemma hasDerivAt_gk (b : ℝ) (c : ℂ) (k : ℕ) (y : ℝ) :
    HasDerivAt (gk b c (k + 1))
      (((k : ℂ) + 1) * gk b c k y - 2 * (b : ℂ) * gk b c (k + 2) y + c * gk b c (k + 1) y) y := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (k + 1)) (((k : ℂ) + 1) * (y : ℂ) ^ k) y := by
    have := (Complex.ofRealCLM.hasDerivAt (x := y)).pow (k + 1)
    simp [Nat.cast_add, Nat.cast_one, mul_comm] at this ⊢
    exact this
  have h2 : HasDerivAt (fun y : ℝ => Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + c * (y : ℂ)))
      ((-(b : ℂ) * (2 * (y : ℂ)) + c) * Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + c * (y : ℂ))) y := by
    have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
    have hsq : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) (2 * (y : ℂ)) y := by
      have h__af := hy.pow 2
      simp at h__af
      exact h__af
    have hlin : HasDerivAt (fun y : ℝ => -(b : ℂ) * (y : ℂ) ^ 2 + c * (y : ℂ)) (-(b : ℂ) * (2 * (y : ℂ)) + c * 1) y :=
      (hsq.const_mul _).add (hy.const_mul c)
    exact hlin.cexp.congr_deriv (by ring)
  have := h1.mul h2
  refine this.congr_deriv ?_
  unfold gk
  ring

private lemma integrable_deriv_gk {b : ℝ} (hb : 0 < b) (c : ℂ) (k : ℕ) :
    Integrable (fun y : ℝ => ((k : ℂ) + 1) * gk b c k y - 2 * (b : ℂ) * gk b c (k + 2) y + c * gk b c (k + 1) y) :=
  (((integrable_gk hb c k).const_mul _).sub ((integrable_gk hb c (k + 2)).const_mul _)).add
    ((integrable_gk hb c (k + 1)).const_mul _)

private lemma recurrence {b : ℝ} (hb : 0 < b) (c : ℂ) (k : ℕ) :
    2 * (b : ℂ) * mk b c (k + 2) = ((k : ℂ) + 1) * mk b c k + c * mk b c (k + 1) := by
  have h0 : ∫ y : ℝ, (((k : ℂ) + 1) * gk b c k y - 2 * (b : ℂ) * gk b c (k + 2) y + c * gk b c (k + 1) y) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_gk b c k) (integrable_deriv_gk hb c k)
      (integrable_gk hb c (k + 1))
  have e : ∫ y : ℝ, (((k : ℂ) + 1) * gk b c k y - 2 * (b : ℂ) * gk b c (k + 2) y + c * gk b c (k + 1) y) =
      ((k : ℂ) + 1) * mk b c k - 2 * (b : ℂ) * mk b c (k + 2) + c * mk b c (k + 1) := by
    have i1 : Integrable (fun y : ℝ => ((k : ℂ) + 1) * gk b c k y) := (integrable_gk hb c k).const_mul _
    have i2 : Integrable (fun y : ℝ => 2 * (b : ℂ) * gk b c (k + 2) y) := (integrable_gk hb c (k + 2)).const_mul _
    have i3 : Integrable (fun y : ℝ => c * gk b c (k + 1) y) := (integrable_gk hb c (k + 1)).const_mul _
    have i12 : Integrable (fun y : ℝ => ((k : ℂ) + 1) * gk b c k y - 2 * (b : ℂ) * gk b c (k + 2) y) := i1.sub i2
    have e1 : ∫ y : ℝ, ((k : ℂ) + 1) * gk b c k y = ((k : ℂ) + 1) * ∫ y : ℝ, gk b c k y :=
      integral_const_mul ((k : ℂ) + 1) (gk b c k)
    have e2 : ∫ y : ℝ, 2 * (b : ℂ) * gk b c (k + 2) y = 2 * (b : ℂ) * ∫ y : ℝ, gk b c (k + 2) y :=
      integral_const_mul (2 * (b : ℂ)) (gk b c (k + 2))
    have e3 : ∫ y : ℝ, c * gk b c (k + 1) y = c * ∫ y : ℝ, gk b c (k + 1) y := integral_const_mul c (gk b c (k + 1))
    unfold mk
    rw [integral_add i12 i3, integral_sub i1 i2, e1, e2, e3]
  rw [e] at h0
  linear_combination -h0

private lemma recurrence_zero {b : ℝ} (hb : 0 < b) (c : ℂ) : 2 * (b : ℂ) * mk b c 1 = c * mk b c 0 := by
  have hd : ∀ y : ℝ, HasDerivAt (gk b c 0) (-(2 * (b : ℂ)) * gk b c 1 y + c * gk b c 0 y) y := by
    intro y
    have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
    have hsq : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) (2 * (y : ℂ)) y := by have h__af := hy.pow 2; simp at h__af; exact h__af
    have hlin : HasDerivAt (fun y : ℝ => -(b : ℂ) * (y : ℂ) ^ 2 + c * (y : ℂ)) (-(b : ℂ) * (2 * (y : ℂ)) + c * 1) y :=
      (hsq.const_mul _).add (hy.const_mul c)
    have h := hlin.cexp
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with z
      simp [gk]
    · simp only [gk, pow_zero, pow_one, one_mul]
      ring
  have hint : Integrable (fun y : ℝ => -(2 * (b : ℂ)) * gk b c 1 y + c * gk b c 0 y) :=
    ((integrable_gk hb c 1).const_mul _).add ((integrable_gk hb c 0).const_mul _)
  have h0 : ∫ y : ℝ, (-(2 * (b : ℂ)) * gk b c 1 y + c * gk b c 0 y) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hd hint (integrable_gk hb c 0)
  have e : ∫ y : ℝ, (-(2 * (b : ℂ)) * gk b c 1 y + c * gk b c 0 y) = -(2 * (b : ℂ)) * mk b c 1 + c * mk b c 0 := by
    have i1 : Integrable (fun y : ℝ => -(2 * (b : ℂ)) * gk b c 1 y) := (integrable_gk hb c 1).const_mul _
    have i0 : Integrable (fun y : ℝ => c * gk b c 0 y) := (integrable_gk hb c 0).const_mul _
    have e1 : ∫ y : ℝ, -(2 * (b : ℂ)) * gk b c 1 y = -(2 * (b : ℂ)) * ∫ y : ℝ, gk b c 1 y :=
      integral_const_mul (-(2 * (b : ℂ))) (gk b c 1)
    have e0 : ∫ y : ℝ, c * gk b c 0 y = c * ∫ y : ℝ, gk b c 0 y := integral_const_mul c (gk b c 0)
    unfold mk
    rw [integral_add i1 i0, e1, e0]
  rw [e] at h0
  linear_combination -h0

private lemma mk_zero {b : ℝ} (hb : 0 < b) (c : ℂ) :
    mk b c 0 = ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * Complex.exp (c ^ 2 / (4 * (b : ℂ))) := by
  have hb' : (-(b : ℂ)).re < 0 := by simpa using hb
  have h := integral_cexp_quadratic hb' c 0
  unfold mk gk
  simp only [pow_zero, one_mul]
  rw [show (fun y : ℝ => Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + c * (y : ℂ))) =
      fun y : ℝ => Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2 + c * (y : ℂ) + 0) by
        funext y; rw [add_zero]]
  rw [h, neg_neg]
  congr 1
  congr 1
  ring

private noncomputable def Q (b : ℝ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.C (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ))
  | 1 => Polynomial.C (1 / (2 * (b : ℂ))) * (Polynomial.X * Polynomial.C (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ)))
  | k + 2 => Polynomial.C (1 / (2 * (b : ℂ))) * (Polynomial.C ((k : ℂ) + 1) * Q b k + Polynomial.X * Q b (k + 1))

private lemma Q_zero (b : ℝ) : Q b 0 = Polynomial.C (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ)) := rfl
private lemma Q_one (b : ℝ) :
    Q b 1 = Polynomial.C (1 / (2 * (b : ℂ))) * (Polynomial.X * Polynomial.C (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ))) := rfl
private lemma Q_succ_succ (b : ℝ) (k : ℕ) :
    Q b (k + 2) =
      Polynomial.C (1 / (2 * (b : ℂ))) * (Polynomial.C ((k : ℂ) + 1) * Q b k + Polynomial.X * Q b (k + 1)) :=
  rfl

private lemma mk_eq {b : ℝ} (hb : 0 < b) (c : ℂ) (k : ℕ) :
    mk b c k = (Q b k).eval c * Complex.exp (c ^ 2 / (4 * (b : ℂ))) := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hb0 : (2 * (b : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hbC
  suffices H : ∀ n : ℕ, mk b c n = (Q b n).eval c * Complex.exp (c ^ 2 / (4 * (b : ℂ))) ∧
      mk b c (n + 1) = (Q b (n + 1)).eval c * Complex.exp (c ^ 2 / (4 * (b : ℂ))) from (H k).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [mk_zero hb, Q_zero, Polynomial.eval_C]
    · have h1 := recurrence_zero hb c
      rw [mk_zero hb] at h1
      show mk b c 1 = (Q b 1).eval c * Complex.exp (c ^ 2 / (4 * (b : ℂ)))
      rw [Q_one]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      have h2 : mk b c 1 =
          c * (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * Complex.exp (c ^ 2 / (4 * (b : ℂ)))) / (2 * b) := by
        rw [eq_div_iff hb0]
        linear_combination h1
      rw [h2]
      ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := recurrence hb c n
    rw [ih.1, ih.2] at h
    show mk b c (n + 2) = (Q b (n + 2)).eval c * Complex.exp (c ^ 2 / (4 * (b : ℂ)))
    rw [Q_succ_succ]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
    have h2 : mk b c (n + 2) = (((n : ℂ) + 1) * ((Q b n).eval c * Complex.exp (c ^ 2 / (4 * (b : ℂ)))) +
        c * ((Q b (n + 1)).eval c * Complex.exp (c ^ 2 / (4 * (b : ℂ))))) / (2 * b) := by
      rw [eq_div_iff hb0]
      linear_combination h
    rw [h2]
    ring

private noncomputable def E2 (b : ℝ) (c : Fin 2 → ℂ) (y : Fin 2 → ℝ) : ℂ :=
  Complex.exp (-(b : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, c i * ((y i : ℝ) : ℂ))

private lemma E2_eq_prod (b : ℝ) (c : Fin 2 → ℂ) (y : Fin 2 → ℝ) :
    E2 b c y = ∏ i, Complex.exp (-(b : ℂ) * ((y i : ℝ) : ℂ) ^ 2 + c i * ((y i : ℝ) : ℂ)) := by
  unfold E2
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Complex.exp_sum]

private lemma monomial_integrand_eq (b : ℝ) (c : Fin 2 → ℂ) (d : Fin 2 →₀ ℕ) (y : Fin 2 → ℝ) :
    MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (MvPolynomial.monomial d (1 : ℂ)) * E2 b c y =
      ∏ i, gk b (c i) (d i) (y i) := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_pow, E2_eq_prod, ← Finset.prod_mul_distrib]
  rfl

private noncomputable def Tmono (b : ℝ) (d : Fin 2 →₀ ℕ) : MvPolynomial (Fin 2) ℂ :=
  ∏ i, Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ) (Q b (d i))

private lemma eval_Tmono (b : ℝ) (d : Fin 2 →₀ ℕ) (c : Fin 2 → ℂ) :
    MvPolynomial.eval c (Tmono b d) = ∏ i, (Q b (d i)).eval (c i) := by
  unfold Tmono
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval c) (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ)
    (Q b (d i))
  rw [MvPolynomial.aeval_X] at h
  have h' : (MvPolynomial.aeval c) (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ) (Q b (d i))) =
      MvPolynomial.eval c (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ) (Q b (d i))) := rfl
  rw [h', ← Polynomial.coe_aeval_eq_eval] at *
  exact h.symm

private noncomputable def Tmap (b : ℝ) : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.basisMonomials (Fin 2) ℂ).constr ℂ (Tmono b)

private lemma Tmap_monomial_one (b : ℝ) (d : Fin 2 →₀ ℕ) : Tmap b (MvPolynomial.monomial d (1 : ℂ)) = Tmono b d := by
  unfold Tmap
  have h := (MvPolynomial.basisMonomials (Fin 2) ℂ).constr_basis ℂ (Tmono b) d
  rwa [MvPolynomial.coe_basisMonomials] at h

private noncomputable def F2 (b : ℝ) (c : Fin 2 → ℂ) (P : MvPolynomial (Fin 2) ℂ) (y : Fin 2 → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P * E2 b c y

private lemma F2_monomial (b : ℝ) (c : Fin 2 → ℂ) (d : Fin 2 →₀ ℕ) (a : ℂ) :
    F2 b c (MvPolynomial.monomial d a) = fun y => a * ∏ i, gk b (c i) (d i) (y i) := by
  funext y
  rw [← monomial_integrand_eq b c d y]
  simp only [F2, MvPolynomial.eval_monomial, one_mul, mul_assoc]

private lemma F2_add (b : ℝ) (c : Fin 2 → ℂ) (p q : MvPolynomial (Fin 2) ℂ) :
    F2 b c (p + q) = fun y => F2 b c p y + F2 b c q y := by
  funext y
  simp only [F2, MvPolynomial.eval_add, add_mul]

private lemma moment_identity {b : ℝ} (hb : 0 < b) (P : MvPolynomial (Fin 2) ℂ) (c : Fin 2 → ℂ) :
    Integrable (F2 b c P) ∧
      ∫ y : Fin 2 → ℝ, F2 b c P y = MvPolynomial.eval c (Tmap b P) * Complex.exp ((∑ i, c i ^ 2) / (4 * (b : ℂ))) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    have hprod : Integrable (fun y : Fin 2 → ℝ => ∏ i, gk b (c i) (d i) (y i)) :=
      Integrable.fintype_prod (f := fun i (t : ℝ) => gk b (c i) (d i) t) fun i => integrable_gk hb (c i) (d i)
    have hmono : MvPolynomial.monomial d a = a • MvPolynomial.monomial d (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    refine ⟨?_, ?_⟩
    · rw [F2_monomial]
      exact hprod.const_mul a
    · have ea : ∫ y : Fin 2 → ℝ, a * ∏ i, gk b (c i) (d i) (y i) = a * ∫ y : Fin 2 → ℝ, ∏ i, gk b (c i) (d i) (y i) :=
        integral_const_mul a (fun y : Fin 2 → ℝ => ∏ i, gk b (c i) (d i) (y i))
      have ep : ∫ y : Fin 2 → ℝ, ∏ i, gk b (c i) (d i) (y i) = ∏ i, mk b (c i) (d i) :=
        integral_fintype_prod_volume_eq_prod (fun i (t : ℝ) => gk b (c i) (d i) t)
      simp only [F2_monomial]
      rw [ea, ep, hmono, map_smul, Tmap_monomial_one, MvPolynomial.smul_eval, eval_Tmono]
      simp only [mk_eq hb]
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_div]
      ring
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · rw [F2_add]
      exact hp.1.add hq.1
    · rw [F2_add, integral_add hp.1 hq.1, hp.2, hq.2, map_add, MvPolynomial.eval_add]
      ring

private theorem exists_moment_map (b : ℝ) (hb : 0 < b) :
    ∃ T : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ,
      ∀ (P : MvPolynomial (Fin 2) ℂ) (c : Fin 2 → ℂ),
        Integrable (fun y : Fin 2 → ℝ =>
          MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P *
            Complex.exp (-(b : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, c i * ((y i : ℝ) : ℂ))) ∧
        ∫ y : Fin 2 → ℝ,
            MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P *
              Complex.exp (-(b : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, c i * ((y i : ℝ) : ℂ)) =
          MvPolynomial.eval c (T P) * Complex.exp ((∑ i, c i ^ 2) / (4 * (b : ℂ))) := by
  refine ⟨Tmap b, fun P c => ?_⟩
  obtain ⟨h1, h2⟩ := moment_identity hb P c
  exact ⟨h1, h2⟩

end GaussianMoments
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

noncomputable section

namespace RadialProfile

private abbrev Arr := Matrix (Fin 2) (Fin 2) ℝ

private def gauge (x : Arr) : ℝ := (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) * (1 + (x.det ^ 2)⁻¹)

private theorem one_le_gauge (x : Arr) : 1 ≤ gauge x := by
  unfold gauge
  have h1 : 0 ≤ x 0 1 ^ 2 + x 1 1 ^ 2 := by positivity
  have h2 : 0 ≤ (x.det ^ 2)⁻¹ := by positivity
  nlinarith

private theorem gauge_pos (x : Arr) : 0 < gauge x := lt_of_lt_of_le one_pos (one_le_gauge x)

private theorem gauge_pow_le_gauge_pow {x : Arr} {M N : ℕ} (h : M ≤ N) : gauge x ^ M ≤ gauge x ^ N :=
  pow_le_pow_right₀ (one_le_gauge x) h

private theorem gauge_pow_nonneg (x : Arr) (N : ℕ) : 0 ≤ gauge x ^ N := pow_nonneg (gauge_pos x).le N

private theorem abs_le_one_of_sq_add_sq (t s : ℝ) (h : t ^ 2 + s ^ 2 = 1) : |t| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg s, sq_nonneg (t + 1), sq_nonneg (t - 1)]

private theorem abs_le_one_add_sq_add_sq (t s : ℝ) : |t| ≤ 1 + (t ^ 2 + s ^ 2) := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg s, sq_nonneg (t + 1), sq_nonneg (t - 1)]

private theorem abs_col0_le_gauge {x : Arr} (hx : x 0 0 ^ 2 + x 1 0 ^ 2 = 1) (i : Fin 2) : |x i 0| ≤ gauge x := by
  have h1 : |x i 0| ≤ 1 := by
    fin_cases i
    · exact abs_le_one_of_sq_add_sq (x 0 0) (x 1 0) hx
    · exact abs_le_one_of_sq_add_sq (x 1 0) (x 0 0) (by linarith)
  exact h1.trans (one_le_gauge x)

private theorem abs_col1_le_gauge (x : Arr) (i : Fin 2) : |x i 1| ≤ gauge x := by
  have h0 : 0 ≤ (x.det ^ 2)⁻¹ := by positivity
  have h1 : |x i 1| ≤ 1 + (x 0 1 ^ 2 + x 1 1 ^ 2) := by
    fin_cases i
    · exact abs_le_one_add_sq_add_sq (x 0 1) (x 1 1)
    · simpa [add_comm] using abs_le_one_add_sq_add_sq (x 1 1) (x 0 1)
  unfold gauge
  have h2 : 0 ≤ 1 + (x 0 1 ^ 2 + x 1 1 ^ 2) := by positivity
  nlinarith

private theorem abs_inv_det_le_gauge (x : Arr) : |x.det⁻¹| ≤ gauge x := by
  have h1 : |x.det⁻¹| ≤ 1 + (x.det ^ 2)⁻¹ := by
    have : |x.det⁻¹| ^ 2 = (x.det ^ 2)⁻¹ := by rw [sq_abs, inv_pow]
    nlinarith [abs_nonneg x.det⁻¹, this]
  unfold gauge
  have h2 : 0 ≤ x 0 1 ^ 2 + x 1 1 ^ 2 := by positivity
  have h3 : 0 ≤ 1 + (x.det ^ 2)⁻¹ := by positivity
  nlinarith

private def Tempered (F : Arr → ℝ → ℂ) : Prop :=
  ∃ (R : Arr → Polynomial ℂ) (n : ℕ) (K : ℝ) (N : ℕ),
    (∀ x ρ, F x ρ = (R x).eval (ρ : ℂ)) ∧
    (∀ x, (R x).natDegree ≤ n) ∧
    (∀ j : ℕ, ContinuousOn (fun x => (R x).coeff j) {x : Arr | x.det ≠ 0}) ∧
    (∀ x : Arr, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 → ∀ j : ℕ, ‖(R x).coeff j‖ ≤ K * gauge x ^ N)

private theorem Tempered.congr {F G : Arr → ℝ → ℂ} (hF : Tempered F) (h : ∀ x ρ, G x ρ = F x ρ) : Tempered G := by
  obtain ⟨R, n, K, N, h1, h2, h3, h4⟩ := hF
  exact ⟨R, n, K, N, fun x ρ => (h x ρ).trans (h1 x ρ), h2, h3, h4⟩

private theorem Tempered.of_const {g : Arr → ℂ} (hg : ContinuousOn g {x : Arr | x.det ≠ 0}) {K : ℝ} {N : ℕ}
    (hb : ∀ x : Arr, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 → ‖g x‖ ≤ K * gauge x ^ N) :
    Tempered fun x _ => g x := by
  refine ⟨fun x => Polynomial.C (g x), 0, max K 0, N, ?_, ?_, ?_, ?_⟩
  · intro x ρ; simp
  · intro x; simp
  · intro j
    by_cases hj : j = 0
    · subst hj; simpa using hg
    · simp [Polynomial.coeff_C, hj, continuousOn_const]
  · intro x hx hdet j
    rw [Polynomial.coeff_C]
    split_ifs
    · exact (hb x hx hdet).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gauge_pow_nonneg x N))
    · simp only [norm_zero]
      exact mul_nonneg (le_max_right _ _) (gauge_pow_nonneg x N)

private theorem Tempered.const (z : ℂ) : Tempered fun _ _ => z :=
  Tempered.of_const (K := ‖z‖) (N := 0) continuousOn_const (fun x _ _ => by simp)

private theorem Tempered.rho : Tempered fun _ ρ => (ρ : ℂ) := by
  refine ⟨fun _ => Polynomial.X, 1, 1, 0, ?_, ?_, ?_, ?_⟩
  · intro x ρ; simp
  · intro x; simp
  · intro j; exact continuousOn_const
  · intro x _ _ j
    rw [Polynomial.coeff_X]
    split_ifs <;> simp

private theorem Tempered.add
    {F G : Arr → ℝ → ℂ} (hF : Tempered F) (hG : Tempered G) : Tempered fun x ρ => F x ρ + G x ρ := by
  obtain ⟨R, n, K, N, h1, h2, h3, h4⟩ := hF
  obtain ⟨S, m, L, M, g1, g2, g3, g4⟩ := hG
  refine ⟨fun x => R x + S x, max n m, max K 0 + max L 0, max N M, ?_, ?_, ?_, ?_⟩
  · intro x ρ; simp [h1, g1]
  · intro x
    exact (Polynomial.natDegree_add_le _ _).trans (max_le_max (h2 x) (g2 x))
  · intro j
    simp only [Polynomial.coeff_add]
    exact (h3 j).add (g3 j)
  · intro x hx hdet j
    simp only [Polynomial.coeff_add]
    have hg1 := one_le_gauge x
    calc ‖(R x).coeff j + (S x).coeff j‖ ≤ ‖(R x).coeff j‖ + ‖(S x).coeff j‖ := norm_add_le _ _
      _ ≤ K * gauge x ^ N + L * gauge x ^ M := add_le_add (h4 x hx hdet j) (g4 x hx hdet j)
      _ ≤ max K 0 * gauge x ^ max N M + max L 0 * gauge x ^ max N M :=
          add_le_add
            (mul_le_mul (le_max_left K 0) (gauge_pow_le_gauge_pow (le_max_left N M)) (gauge_pow_nonneg x N)
              (le_max_right K 0))
            (mul_le_mul (le_max_left L 0) (gauge_pow_le_gauge_pow (le_max_right N M)) (gauge_pow_nonneg x M)
              (le_max_right L 0))
      _ = (max K 0 + max L 0) * gauge x ^ max N M := by ring

private theorem Tempered.mul
    {F G : Arr → ℝ → ℂ} (hF : Tempered F) (hG : Tempered G) : Tempered fun x ρ => F x ρ * G x ρ := by
  obtain ⟨R, n, K, N, h1, h2, h3, h4⟩ := hF
  obtain ⟨S, m, L, M, g1, g2, g3, g4⟩ := hG
  refine ⟨fun x => R x * S x, n + m, (n + m + 1 : ℕ) * (max K 0 * max L 0), N + M, ?_, ?_, ?_, ?_⟩
  · intro x ρ; simp [h1, g1]
  · intro x
    exact (Polynomial.natDegree_mul_le).trans (add_le_add (h2 x) (g2 x))
  · intro j
    simp only [Polynomial.coeff_mul]
    exact continuousOn_finsetSum _ fun ij _ => (h3 ij.1).mul (g3 ij.2)
  · intro x hx hdet j
    simp only [Polynomial.coeff_mul]
    have hg1 := one_le_gauge x
    have hKL : 0 ≤ max K 0 * max L 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
    rcases lt_or_ge (n + m) j with hj | hj
    ·
      have hdeg : ((R x) * (S x)).natDegree < j :=
        lt_of_le_of_lt (Polynomial.natDegree_mul_le.trans (add_le_add (h2 x) (g2 x))) hj
      rw [← Polynomial.coeff_mul, Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, norm_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKL) (gauge_pow_nonneg x _)
    · have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
          ‖(R x).coeff ij.1 * (S x).coeff ij.2‖ ≤ max K 0 * max L 0 * gauge x ^ (N + M) := by
        intro ij _
        rw [norm_mul, pow_add]
        have hR : ‖(R x).coeff ij.1‖ ≤ max K 0 * gauge x ^ N :=
          (h4 x hx hdet ij.1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gauge_pow_nonneg x N))
        have hS : ‖(S x).coeff ij.2‖ ≤ max L 0 * gauge x ^ M :=
          (g4 x hx hdet ij.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (gauge_pow_nonneg x M))
        calc ‖(R x).coeff ij.1‖ * ‖(S x).coeff ij.2‖
            ≤ (max K 0 * gauge x ^ N) * (max L 0 * gauge x ^ M) :=
              mul_le_mul hR hS (norm_nonneg _) (mul_nonneg (le_max_right _ _) (gauge_pow_nonneg x N))
          _ = max K 0 * max L 0 * (gauge x ^ N * gauge x ^ M) := by ring
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
      calc ‖∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, (R x).coeff ij.1 * (S x).coeff ij.2‖
          ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, ‖(R x).coeff ij.1 * (S x).coeff ij.2‖ := norm_sum_le _ _
        _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal j, max K 0 * max L 0 * gauge x ^ (N + M) := Finset.sum_le_sum hterm
        _ = (j + 1 : ℕ) * (max K 0 * max L 0 * gauge x ^ (N + M)) := by
              rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        _ ≤ (n + m + 1 : ℕ) * (max K 0 * max L 0 * gauge x ^ (N + M)) :=
              mul_le_mul_of_nonneg_right hcast (mul_nonneg hKL (gauge_pow_nonneg x _))
        _ = (n + m + 1 : ℕ) * (max K 0 * max L 0) * gauge x ^ (N + M) := by ring

private theorem Tempered.smul_const (z : ℂ) {F : Arr → ℝ → ℂ} (hF : Tempered F) : Tempered fun x ρ => z * F x ρ :=
  (Tempered.const z).mul hF

private theorem Tempered.sum {ι : Type*} (s : Finset ι) {F : ι → Arr → ℝ → ℂ} (h : ∀ i ∈ s, Tempered (F i)) :
    Tempered fun x ρ => ∑ i ∈ s, F i x ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Tempered.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem Tempered.eval_fixed
    (S : MvPolynomial (Fin 2) ℂ) {cv : Fin 2 → Arr → ℝ → ℂ} (hcv : ∀ i, Tempered (cv i)) :
    Tempered fun x ρ => MvPolynomial.eval (fun i => cv i x ρ) S := by
  induction S using MvPolynomial.induction_on with
  | C a => simpa using Tempered.const a
  | add p q hp hq => simpa [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp => simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul (hcv i)

private theorem Tempered.moment (T : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ) {cv : Fin 2 → Arr → ℝ → ℂ}
    (hcv : ∀ i, Tempered (cv i)) (r : Fin 2 × Fin 3 → Arr → ℝ → ℂ) (hr : ∀ ib, Tempered (r ib)) (s : Fin 2 × Fin 3 → ℂ)
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    ∀ β : Fin 2 →₀ ℕ, Tempered fun x ρ => MvPolynomial.eval (fun i => cv i x ρ)
      (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
        MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) p *
          MvPolynomial.monomial β (1 : ℂ))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro β
    have h : ∀ x ρ, MvPolynomial.eval (fun i => cv i x ρ)
        (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
          MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) (MvPolynomial.C a) *
            MvPolynomial.monomial β (1 : ℂ)))
        = a * MvPolynomial.eval (fun i => cv i x ρ) (T (MvPolynomial.monomial β (1 : ℂ))) := by
      intro x ρ
      rw [MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_one_mul, map_smul, MvPolynomial.smul_eval]
    exact ((Tempered.const a).mul (Tempered.eval_fixed _ hcv)).congr h
  | add p q hp hq =>
    intro β
    have h : ∀ x ρ, MvPolynomial.eval (fun i => cv i x ρ)
        (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
          MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) (p + q) *
            MvPolynomial.monomial β (1 : ℂ)))
        = MvPolynomial.eval (fun i => cv i x ρ) (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
              MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) p *
                MvPolynomial.monomial β (1 : ℂ)))
          + MvPolynomial.eval (fun i => cv i x ρ) (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
              MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) q *
                MvPolynomial.monomial β (1 : ℂ))) := by
      intro x ρ
      rw [map_add, add_mul, map_add, map_add]
    exact ((hp β).add (hq β)).congr h
  | mul_X p ib hp =>
    intro β
    have h : ∀ x ρ, MvPolynomial.eval (fun i => cv i x ρ)
        (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
          MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) (p * MvPolynomial.X ib) *
            MvPolynomial.monomial β (1 : ℂ)))
        = r ib x ρ * MvPolynomial.eval (fun i => cv i x ρ) (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
              MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) p *
                MvPolynomial.monomial β (1 : ℂ)))
          + s ib * MvPolynomial.eval (fun i => cv i x ρ) (T (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
              MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) p *
                MvPolynomial.monomial (β + Finsupp.single ib.1 1) (1 : ℂ))) := by
      intro x ρ
      have hmono : (MvPolynomial.monomial β (1 : ℂ)) * MvPolynomial.X ib.1
          = MvPolynomial.monomial (β + Finsupp.single ib.1 1) (1 : ℂ) := by
        rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
      have hsplit : MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
            MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) (p * MvPolynomial.X ib) *
              MvPolynomial.monomial β (1 : ℂ)
          = r ib x ρ • (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
                MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) p *
                  MvPolynomial.monomial β (1 : ℂ))
            + s ib • (MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
                MvPolynomial.C (r ib x ρ) + MvPolynomial.C (s ib) * MvPolynomial.X ib.1) p *
                  MvPolynomial.monomial (β + Finsupp.single ib.1 1) (1 : ℂ)) := by
        rw [map_mul, MvPolynomial.aeval_X, ← hmono, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
        ring
      rw [hsplit, map_add, map_smul, map_smul, map_add, MvPolynomial.smul_eval, MvPolynomial.smul_eval]
    exact (((hr ib).mul (hp β)).add ((Tempered.const (s ib)).mul (hp (β + Finsupp.single ib.1 1)))).congr h

private theorem Tempered.unpack {F : Arr → ℝ → ℂ} (hF : Tempered F) (E : Arr → ℂ)
    (hE : ContinuousOn E {x : Arr | x.det ≠ 0}) :
    ∃ (n : ℕ) (c : Arr → Fin (n + 1) → ℂ) (K : ℝ) (N : ℕ),
      ContinuousOn c {x : Arr | x.det ≠ 0} ∧
      (∀ x ρ, E x * F x ρ = ∑ j : Fin (n + 1), c x j * (ρ : ℂ) ^ (j : ℕ)) ∧
      (∀ x : Arr, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 → ∀ j : Fin (n + 1),
        ‖c x j‖ ≤ ‖E x‖ * (K * gauge x ^ N)) := by
  obtain ⟨R, n, K, N, h1, h2, h3, h4⟩ := hF
  refine ⟨n, fun x j => E x * (R x).coeff j, K, N, ?_, ?_, ?_⟩
  · exact continuousOn_pi.2 fun j => hE.mul (h3 j)
  · intro x ρ
    rw [h1, Polynomial.eval_eq_sum_range' (Nat.lt_add_one_of_le (h2 x)), Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun j => E x * ((R x).coeff j * (ρ : ℂ) ^ j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    ring
  · intro x hx hdet j
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h4 x hx hdet j) (norm_nonneg _)

end RadialProfile
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace RadialProfile

section Geometry

variable (m : Matrix (Fin 3) (Fin 3) ℝ)

private def N₀ : Matrix (Fin 2) (Fin 3) ℝ := Matrix.of ![m 0, m 1]

private def shifted (R : Matrix (Fin 2) (Fin 3) ℝ) (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun i b => R i b + y i * m 2 b

private theorem array_eq (h : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    h * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b]
      = shifted m (h * N₀ m) (h.mulVec v) := by
  ext i b
  fin_cases i <;> simp [shifted, N₀, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

private def nm2 : ℝ := ∑ b : Fin 3, m 2 b ^ 2

private theorem nm2_pos (hm : m.det ≠ 0) : 0 < nm2 m := by
  have h0 : 0 ≤ nm2 m := by unfold nm2; positivity
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hm
    apply Matrix.det_eq_zero_of_row_eq_zero 2
    intro b
    have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (m 2 b))).1 h.symm b (Finset.mem_univ b)
    simpa using hb

private def entries (x : Arr) (ρ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := (x * diagOne ρ) * N₀ m

private theorem entries_apply (x : Arr) (ρ : ℝ) (i : Fin 2) (b : Fin 3) :
    entries m x ρ i b = ρ * x i 0 * m 0 b + x i 1 * m 1 b := by
  fin_cases i <;>
    simp only [entries, N₀, diagOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    ring

private theorem det_x_diagOne (x : Arr) (ρ : ℝ) : (x * diagOne ρ).det = x.det * ρ := by
  rw [Matrix.det_mul, diagOne, Matrix.det_fin_two_of]
  ring

private def _root_.RadialProfile.ell (x : Arr) : Fin 2 → ℝ := ![x 1 0 / x.det, -(x 0 0) / x.det]

p2m_export "RadialProfile" "ell"
private theorem ell_dot_mulVec {x : Arr} (hx : x.det ≠ 0) (ρ : ℝ) (v : Fin 2 → ℝ) :
    ∑ i : Fin 2, ell x i * ((x * diagOne ρ).mulVec v) i = -(v 1) := by
  have hdet : x.det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := Matrix.det_fin_two x
  simp only [ell, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mulVec,
    dotProduct, Matrix.mul_apply, diagOne, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  field_simp
  rw [hdet]
  ring

private def qv (R : Matrix (Fin 2) (Fin 3) ℝ) (i : Fin 2) : ℝ := ∑ b : Fin 3, R i b * m 2 b

private theorem sq_sum_shifted (R : Matrix (Fin 2) (Fin 3) ℝ) (y : Fin 2 → ℝ) :
    ∑ i : Fin 2, ∑ b : Fin 3, shifted m R y i b ^ 2
      = (∑ i : Fin 2, ∑ b : Fin 3, R i b ^ 2) + 2 * ∑ i : Fin 2, y i * qv m R i + nm2 m * ∑ i : Fin 2, y i ^ 2 := by
  simp only [shifted, qv, nm2, Matrix.of_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

private def alpha (R : Matrix (Fin 2) (Fin 3) ℝ) (i : Fin 2) : ℝ := -(2 * Real.pi * qv m R i)

private def beta (a : ℝ) (x : Arr) (i : Fin 2) : ℝ := 2 * Real.pi * a * ell x i

private def cvec (a : ℝ) (R : Matrix (Fin 2) (Fin 3) ℝ) (x : Arr) (i : Fin 2) : ℂ :=
  (alpha m R i : ℂ) + Complex.I * (beta a x i : ℂ)

private def bb : ℝ := Real.pi * nm2 m

private theorem bb_pos (hm : m.det ≠ 0) : 0 < bb m := mul_pos Real.pi_pos (nm2_pos m hm)

private def Pfix (R : Matrix (Fin 2) (Fin 3) ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval (fun ib : Fin 2 × Fin 3 =>
    MvPolynomial.C ((R ib.1 ib.2 : ℝ) : ℂ) + MvPolynomial.C ((m 2 ib.2 : ℝ) : ℂ) * MvPolynomial.X ib.1) p

private theorem eval_shifted (R : Matrix (Fin 2) (Fin 3) ℝ) (y : Fin 2 → ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    MvPolynomial.eval (fun ib : Fin 2 × Fin 3 => ((shifted m R y ib.1 ib.2 : ℝ) : ℂ)) p
      = MvPolynomial.eval (fun i : Fin 2 => ((y i : ℝ) : ℂ)) (Pfix m R p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [Pfix]
  | add p q hp hq =>
    simp only [Pfix, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p ib hp =>
    simp only [Pfix, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_add, MvPolynomial.eval_C,
      MvPolynomial.eval_X] at hp ⊢
    rw [hp]
    simp only [shifted, Matrix.of_apply]
    push_cast
    ring

private theorem exp_factor (a : ℝ) (x : Arr) (R : Matrix (Fin 2) (Fin 3) ℝ) (y : Fin 2 → ℝ) :
    gaussian3 (shifted m R y) * Complex.exp ((2 * Real.pi * Complex.I) * ((a * ∑ i : Fin 2, ell x i * y i : ℝ) : ℂ))
      = Complex.exp (-(bb m : ℂ) * ∑ i : Fin 2, ((y i : ℝ) : ℂ) ^ 2 + ∑ i : Fin 2, cvec m a R x i * ((y i : ℝ) : ℂ))
          * Complex.exp (-((Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, R i b ^ 2 : ℝ) : ℂ)) := by
  unfold gaussian3
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [sq_sum_shifted]
  simp only [cvec, alpha, beta, bb, Fin.sum_univ_two]
  push_cast
  ring

private def Aconst : ℝ := (∑ b : Fin 3, m 0 b ^ 2) - (∑ b : Fin 3, m 0 b * m 2 b) ^ 2 / nm2 m

private def Bfun (x : Arr) : ℝ :=
  (x 0 0 * x 0 1 + x 1 0 * x 1 1) *
    ((∑ b : Fin 3, m 0 b * m 1 b) - (∑ b : Fin 3, m 0 b * m 2 b) * (∑ b : Fin 3, m 1 b * m 2 b) / nm2 m)

private def Cconst : ℝ := (∑ b : Fin 3, m 1 b ^ 2) - (∑ b : Fin 3, m 1 b * m 2 b) ^ 2 / nm2 m

private def REfree (a : ℝ) (x : Arr) : ℝ :=
  -(Real.pi * (x 0 1 ^ 2 + x 1 1 ^ 2) * Cconst m) - Real.pi * a ^ 2 * (ell x 0 ^ 2 + ell x 1 ^ 2) / nm2 m

private def IMfree (a : ℝ) (x : Arr) : ℝ :=
  -(2 * Real.pi * a * (∑ b : Fin 3, m 1 b * m 2 b) * (x 0 1 * ell x 0 + x 1 1 * ell x 1) / nm2 m)

private theorem re_identity (hm : m.det ≠ 0) (a : ℝ) (x : Arr) (ρ : ℝ) :
    -(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2)
        + (∑ i : Fin 2, (alpha m (entries m x ρ) i ^ 2 - beta a x i ^ 2)) / (4 * bb m)
      = REfree m a x - Real.pi * ((x 0 0 ^ 2 + x 1 0 ^ 2) * Aconst m * ρ ^ 2 + 2 * Bfun m x * ρ) := by
  have hn : nm2 m ≠ 0 := (nm2_pos m hm).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  simp only [alpha, beta, bb, qv, entries_apply, Aconst, Bfun, Cconst, REfree, Fin.sum_univ_two, Fin.sum_univ_three]
  simp only [nm2, Fin.sum_univ_three] at hn ⊢
  field_simp
  ring

private theorem im_identity (hm : m.det ≠ 0) (a : ℝ) (x : Arr) (ρ : ℝ) :
    (∑ i : Fin 2, 2 * alpha m (entries m x ρ) i * beta a x i) / (4 * bb m) = IMfree m a x := by
  have hn : nm2 m ≠ 0 := (nm2_pos m hm).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  simp only [alpha, beta, bb, qv, entries_apply, IMfree, ell, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [nm2, Fin.sum_univ_three] at hn ⊢
  field_simp
  ring

private theorem cvec_sq (a : ℝ) (R : Matrix (Fin 2) (Fin 3) ℝ) (x : Arr) (i : Fin 2) :
    cvec m a R x i ^ 2
      = ((alpha m R i ^ 2 - beta a x i ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * alpha m R i * beta a x i : ℝ) : ℂ) := by
  unfold cvec
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private def Rfree (a : ℝ) (x : Arr) : ℂ := (REfree m a x : ℂ) + Complex.I * (IMfree m a x : ℂ)

private theorem exponent_eq (hm : m.det ≠ 0) (a : ℝ) (x : Arr) (ρ : ℝ) :
    -((Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2 : ℝ) : ℂ)
        + (∑ i : Fin 2, cvec m a (entries m x ρ) x i ^ 2) / (4 * (bb m : ℂ))
      = Rfree m a x
          - Real.pi * (((x 0 0 ^ 2 + x 1 0 ^ 2) * Aconst m : ℝ) * (ρ : ℂ) ^ 2 + 2 * (Bfun m x : ℝ) * (ρ : ℂ)) := by
  have hre := re_identity m hm a x ρ
  have him := im_identity m hm a x ρ
  simp only [cvec_sq, Finset.sum_add_distrib, ← Finset.mul_sum, Rfree]
  have h4 : (4 * (bb m : ℂ)) = ((4 * bb m : ℝ) : ℂ) := by push_cast; ring
  rw [h4, add_div, mul_div_assoc, ← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_div,
    ← Complex.ofReal_div, him]
  have hre' : ((-(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2)
      + (∑ i : Fin 2, (alpha m (entries m x ρ) i ^ 2 - beta a x i ^ 2)) / (4 * bb m) : ℝ) : ℂ)
      = ((REfree m a x - Real.pi * ((x 0 0 ^ 2 + x 1 0 ^ 2) * Aconst m * ρ ^ 2 + 2 * Bfun m x * ρ) : ℝ) : ℂ) := by
    rw [hre]
  push_cast at hre' ⊢
  linear_combination hre'

end Geometry
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end RadialProfile
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace RadialProfile

section Atoms

variable (m : Matrix (Fin 3) (Fin 3) ℝ)

private theorem continuous_entry (i j : Fin 2) : Continuous fun x : Arr => x i j :=
  (continuous_apply j).comp (continuous_apply i)

private theorem continuous_det : Continuous fun x : Arr => x.det := continuous_id.matrix_det

private theorem continuousOn_ell (i : Fin 2) : ContinuousOn (fun x : Arr => ell x i) {x : Arr | x.det ≠ 0} := by
  fin_cases i
  · exact (continuous_entry 1 0).continuousOn.div continuous_det.continuousOn fun x hx => hx
  · exact (continuous_entry 0 0).continuousOn.neg.div continuous_det.continuousOn fun x hx => hx

private theorem abs_ell_le {x : Arr} (hx : x 0 0 ^ 2 + x 1 0 ^ 2 = 1) (i : Fin 2) : |ell x i| ≤ gauge x ^ 2 := by
  have hd := abs_inv_det_le_gauge x
  have hg := (gauge_pos x).le
  fin_cases i
  · have h0 := abs_col0_le_gauge hx 1
    show |x 1 0 / x.det| ≤ gauge x ^ 2
    rw [div_eq_mul_inv, abs_mul, pow_two]
    exact mul_le_mul h0 hd (abs_nonneg _) hg
  · have h0 := abs_col0_le_gauge hx 0
    show |-(x 0 0) / x.det| ≤ gauge x ^ 2
    rw [div_eq_mul_inv, abs_mul, abs_neg, pow_two]
    exact mul_le_mul h0 hd (abs_nonneg _) hg

private theorem Tempered.entry0 (i : Fin 2) : Tempered fun (x : Arr) (_ : ℝ) => ((x i 0 : ℝ) : ℂ) := by
  refine Tempered.of_const (K := 1) (N := 1) (Complex.continuous_ofReal.comp (continuous_entry i 0)).continuousOn ?_
  intro x hx _
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul, pow_one]
  exact abs_col0_le_gauge hx i

private theorem Tempered.entry1 (i : Fin 2) : Tempered fun (x : Arr) (_ : ℝ) => ((x i 1 : ℝ) : ℂ) := by
  refine Tempered.of_const (K := 1) (N := 1) (Complex.continuous_ofReal.comp (continuous_entry i 1)).continuousOn ?_
  intro x _ _
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul, pow_one]
  exact abs_col1_le_gauge x i

private theorem Tempered.ell (i : Fin 2) : Tempered fun (x : Arr) (_ : ℝ) => ((ell x i : ℝ) : ℂ) := by
  refine Tempered.of_const (K := 1) (N := 2)
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_ell i)) ?_
  intro x hx _
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact abs_ell_le hx i

private theorem qv_entries (x : Arr) (ρ : ℝ) (i : Fin 2) :
    qv m (entries m x ρ) i = ρ * (x i 0 * ∑ b : Fin 3, m 0 b * m 2 b) + x i 1 * ∑ b : Fin 3, m 1 b * m 2 b := by
  simp only [qv, entries_apply, Fin.sum_univ_three]
  ring

private theorem Tempered.cvec_entries (a : ℝ) (i : Fin 2) :
    Tempered fun (x : Arr) (ρ : ℝ) => cvec m a (entries m x ρ) x i := by
  have h := ((Tempered.const (-(2 * Real.pi : ℂ))).mul
      ((Tempered.rho.mul ((Tempered.entry0 i).mul (Tempered.const ((∑ b : Fin 3, m 0 b * m 2 b : ℝ) : ℂ)))).add
        ((Tempered.entry1 i).mul (Tempered.const ((∑ b : Fin 3, m 1 b * m 2 b : ℝ) : ℂ))))).add
    ((Tempered.const (Complex.I * (2 * Real.pi * a : ℝ))).mul (Tempered.ell i))
  refine h.congr fun x ρ => ?_
  simp only [cvec, alpha, beta, qv_entries]
  push_cast
  ring

private theorem Tempered.entries_atom (ib : Fin 2 × Fin 3) :
    Tempered fun (x : Arr) (ρ : ℝ) => ((entries m x ρ ib.1 ib.2 : ℝ) : ℂ) := by
  have h := (Tempered.rho.mul ((Tempered.entry0 ib.1).mul (Tempered.const ((m 0 ib.2 : ℝ) : ℂ)))).add
    ((Tempered.entry1 ib.1).mul (Tempered.const ((m 1 ib.2 : ℝ) : ℂ)))
  refine h.congr fun x ρ => ?_
  rw [entries_apply]
  push_cast
  ring

private def Mom (T : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ) (a : ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    (x : Arr) (ρ : ℝ) : ℂ :=
  MvPolynomial.eval (fun i => cvec m a (entries m x ρ) x i) (T (Pfix m (entries m x ρ) p))

private theorem Tempered.mom (T : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ) (a : ℝ)
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) : Tempered (Mom m T a p) := by
  have h := Tempered.moment T (cv := fun i x ρ => cvec m a (entries m x ρ) x i) (fun i => Tempered.cvec_entries m a i)
    (fun ib x ρ => ((entries m x ρ ib.1 ib.2 : ℝ) : ℂ)) (fun ib => Tempered.entries_atom m ib)
    (fun ib => ((m 2 ib.2 : ℝ) : ℂ)) p 0
  refine h.congr fun x ρ => ?_
  simp [Mom, Pfix]

end Atoms
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

section Bounds

variable (m : Matrix (Fin 3) (Fin 3) ℝ)

private def kconst
    : ℝ := (∑ b : Fin 3, m 0 b * m 1 b) - (∑ b : Fin 3, m 0 b * m 2 b) * (∑ b : Fin 3, m 1 b * m 2 b) / nm2 m

private theorem Bfun_eq (x : Arr) : Bfun m x = (x 0 0 * x 0 1 + x 1 0 * x 1 1) * kconst m := rfl

private theorem Aconst_mul_nm2 (hm : m.det ≠ 0) :
    Aconst m * nm2 m = (m 0 0 * m 2 1 - m 0 1 * m 2 0) ^ 2 + (m 0 0 * m 2 2 - m 0 2 * m 2 0) ^ 2
      + (m 0 1 * m 2 2 - m 0 2 * m 2 1) ^ 2 := by
  have hn : nm2 m ≠ 0 := (nm2_pos m hm).ne'
  unfold Aconst
  simp only [nm2, Fin.sum_univ_three] at hn ⊢
  field_simp
  ring

private theorem Aconst_pos (hm : m.det ≠ 0) : 0 < Aconst m := by
  have hn := nm2_pos m hm
  have hL := Aconst_mul_nm2 m hm
  have hdet : m.det = m 0 0 * m 1 1 * m 2 2 - m 0 0 * m 1 2 * m 2 1 - m 0 1 * m 1 0 * m 2 2 + m 0 1 * m 1 2 * m 2 0
      + m 0 2 * m 1 0 * m 2 1 - m 0 2 * m 1 1 * m 2 0 := Matrix.det_fin_three m
  have hpos : 0 < (m 0 0 * m 2 1 - m 0 1 * m 2 0) ^ 2 + (m 0 0 * m 2 2 - m 0 2 * m 2 0) ^ 2
      + (m 0 1 * m 2 2 - m 0 2 * m 2 1) ^ 2 := by
    rcases (show (0 : ℝ) ≤ (m 0 0 * m 2 1 - m 0 1 * m 2 0) ^ 2 + (m 0 0 * m 2 2 - m 0 2 * m 2 0) ^ 2
        + (m 0 1 * m 2 2 - m 0 2 * m 2 1) ^ 2 by positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hm
      have h1 : m 0 0 * m 2 1 - m 0 1 * m 2 0 = 0 := by
        nlinarith [sq_nonneg (m 0 0 * m 2 1 - m 0 1 * m 2 0), sq_nonneg (m 0 0 * m 2 2 - m 0 2 * m 2 0),
          sq_nonneg (m 0 1 * m 2 2 - m 0 2 * m 2 1)]
      have h2 : m 0 0 * m 2 2 - m 0 2 * m 2 0 = 0 := by
        nlinarith [sq_nonneg (m 0 0 * m 2 1 - m 0 1 * m 2 0), sq_nonneg (m 0 0 * m 2 2 - m 0 2 * m 2 0),
          sq_nonneg (m 0 1 * m 2 2 - m 0 2 * m 2 1)]
      have h3 : m 0 1 * m 2 2 - m 0 2 * m 2 1 = 0 := by
        nlinarith [sq_nonneg (m 0 0 * m 2 1 - m 0 1 * m 2 0), sq_nonneg (m 0 0 * m 2 2 - m 0 2 * m 2 0),
          sq_nonneg (m 0 1 * m 2 2 - m 0 2 * m 2 1)]
      rw [hdet]
      linear_combination (-(m 1 2)) * h1 + m 1 1 * h2 + (-(m 1 0)) * h3
  have hprod : 0 < Aconst m * nm2 m := by
    rw [hL]
    exact hpos
  by_contra hcon
  have hcon' := not_lt.1 hcon
  nlinarith [mul_le_mul_of_nonneg_right hcon' hn.le]

private theorem gram_identity (hm : m.det ≠ 0) : (Aconst m * Cconst m - kconst m ^ 2) * nm2 m = m.det ^ 2 := by
  have hn : nm2 m ≠ 0 := (nm2_pos m hm).ne'
  rw [Matrix.det_fin_three]
  unfold Aconst Cconst kconst
  simp only [nm2, Fin.sum_univ_three] at hn ⊢
  field_simp
  ring

private def delta : ℝ := Cconst m - kconst m ^ 2 / Aconst m

private theorem delta_pos (hm : m.det ≠ 0) : 0 < delta m := by
  have hA := Aconst_pos m hm
  have hn := nm2_pos m hm
  have hG := gram_identity m hm
  have hd : 0 < m.det ^ 2 := by positivity
  have h1 : 0 < Aconst m * Cconst m - kconst m ^ 2 := by
    by_contra hcon
    have hcon' := not_lt.1 hcon
    nlinarith [mul_le_mul_of_nonneg_right hcon' hn.le]
  unfold delta
  rw [sub_pos, div_lt_iff₀ hA]
  linarith

private theorem kconst_sq_div_Aconst : kconst m ^ 2 / Aconst m = Cconst m - delta m := by
  unfold delta; ring

private theorem inner_sq_le {x : Arr} (hx : x 0 0 ^ 2 + x 1 0 ^ 2 = 1) :
    (x 0 0 * x 0 1 + x 1 0 * x 1 1) ^ 2 ≤ x 0 1 ^ 2 + x 1 1 ^ 2 := by
  nlinarith [sq_nonneg (x 0 0 * x 1 1 - x 1 0 * x 0 1)]

private theorem abs_inner_le {x : Arr} (hx : x 0 0 ^ 2 + x 1 0 ^ 2 = 1) :
    |x 0 0 * x 0 1 + x 1 0 * x 1 1| ≤ 1 + (x 0 1 ^ 2 + x 1 1 ^ 2) := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x 0 0 + x 0 1), sq_nonneg (x 1 0 + x 1 1), sq_nonneg (x 0 0 - x 0 1),
    sq_nonneg (x 1 0 - x 1 1)]

private theorem ell_sq_sum {x : Arr} (hx : x 0 0 ^ 2 + x 1 0 ^ 2 = 1) (hdet : x.det ≠ 0) :
    ell x 0 ^ 2 + ell x 1 ^ 2 = (x.det ^ 2)⁻¹ := by
  simp only [ell, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  linear_combination hx

private theorem exists_poly_le_exp {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ M ≤ K * Real.exp (ε * s) := by
  refine ⟨2 ^ M * (1 + (M.factorial : ℝ) / ε ^ M), by positivity, fun s hs => ?_⟩
  have hexp1 : (1 : ℝ) ≤ Real.exp (ε * s) := Real.one_le_exp (by positivity)
  have hpow : s ^ M ≤ (M.factorial : ℝ) / ε ^ M * Real.exp (ε * s) := by
    have h := Real.pow_div_factorial_le_exp (ε * s) (by positivity) M
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    have hεM : 0 < ε ^ M := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hεM]
    nlinarith [h]
  have h1s : (1 + s) ^ M ≤ 2 ^ M * (1 + s ^ M) := by
    have hmax : 1 + s ≤ 2 * max 1 s := by
      have := le_max_left 1 s; have := le_max_right 1 s; linarith
    have hmaxpow : max 1 s ^ M ≤ 1 + s ^ M := by
      rcases le_total 1 s with h | h
      · rw [max_eq_right h]; linarith [pow_nonneg (zero_le_one.trans h) M]
      · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hs M]
    calc (1 + s) ^ M ≤ (2 * max 1 s) ^ M := pow_le_pow_left₀ (by positivity) hmax M
      _ = 2 ^ M * max 1 s ^ M := mul_pow 2 _ M
      _ ≤ 2 ^ M * (1 + s ^ M) := mul_le_mul_of_nonneg_left hmaxpow (by positivity)
  calc (1 + s) ^ M ≤ 2 ^ M * (1 + s ^ M) := h1s
    _ ≤ 2 ^ M * (Real.exp (ε * s) + (M.factorial : ℝ) / ε ^ M * Real.exp (ε * s)) :=
        mul_le_mul_of_nonneg_left (add_le_add hexp1 hpow) (by positivity)
    _ = 2 ^ M * (1 + (M.factorial : ℝ) / ε ^ M) * Real.exp (ε * s) := by ring

end Bounds
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end RadialProfile
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace RadialProfile

section Main

variable (m : Matrix (Fin 3) (Fin 3) ℝ)

private def fy
    (a : ℝ) (x : Arr) (R : Matrix (Fin 2) (Fin 3) ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (y : Fin 2 → ℝ) : ℂ :=
  MvPolynomial.eval (fun ib : Fin 2 × Fin 3 => ((shifted m R y ib.1 ib.2 : ℝ) : ℂ)) p * gaussian3 (shifted m R y) *
    Complex.exp ((2 * Real.pi * Complex.I) * ((a * ∑ i : Fin 2, ell x i * y i : ℝ) : ℂ))

private theorem continuous_fy (a : ℝ) (x : Arr) (R : Matrix (Fin 2) (Fin 3) ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    Continuous (fy m a x R p) := by
  unfold fy
  have h1 : Continuous fun y : Fin 2 → ℝ =>
      MvPolynomial.eval (fun ib : Fin 2 × Fin 3 => ((shifted m R y ib.1 ib.2 : ℝ) : ℂ)) p := by
    refine (MvPolynomial.continuous_eval (p := p)).comp ?_
    refine continuous_pi fun ib => Complex.continuous_ofReal.comp ?_
    simp only [shifted, Matrix.of_apply]
    fun_prop
  have h2 : Continuous fun y : Fin 2 → ℝ => gaussian3 (shifted m R y) := by
    unfold gaussian3 shifted
    simp only [Matrix.of_apply]
    fun_prop
  have h3 : Continuous fun y : Fin 2 → ℝ =>
      Complex.exp ((2 * Real.pi * Complex.I) * ((a * ∑ i : Fin 2, ell x i * y i : ℝ) : ℂ)) := by
    fun_prop
  exact (h1.mul h2).mul h3

private theorem integrand_eq
    (a : ℝ) {x : Arr} (hx : x.det ≠ 0) (ρ : ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (v : Fin 2 → ℝ) :
    (MvPolynomial.eval (fun ib : Fin 2 × Fin 3 =>
        ((((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])
          ib.1 ib.2 : ℝ) : ℂ)) p *
      gaussian3 ((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])) *
    Complex.exp ((2 * Real.pi * Complex.I) * ((a * (-(v 1)) : ℝ) : ℂ))
      = fy m a x (entries m x ρ) p ((x * diagOne ρ).mulVec v) := by
  unfold fy entries
  rw [array_eq, ell_dot_mulVec hx]

private theorem integral_eq (T : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ)
    (hT : ∀ (P : MvPolynomial (Fin 2) ℂ) (c : Fin 2 → ℂ),
      ∫ y : Fin 2 → ℝ, MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P *
          Complex.exp (-(bb m : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, c i * ((y i : ℝ) : ℂ))
        = MvPolynomial.eval c (T P) * Complex.exp ((∑ i, c i ^ 2) / (4 * (bb m : ℂ))))
    (a : ℝ) {x : Arr} (hx : x.det ≠ 0) {ρ : ℝ} (hρ : ρ ≠ 0) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    ∫ v : Fin 2 → ℝ, fy m a x (entries m x ρ) p ((x * diagOne ρ).mulVec v)
      = ((|x.det * ρ|⁻¹ : ℝ) : ℂ) *
          (Mom m T a p x ρ * Complex.exp ((∑ i, cvec m a (entries m x ρ) x i ^ 2) / (4 * (bb m : ℂ))) *
            Complex.exp (-((Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2 : ℝ) : ℂ))) := by
  have hdet : (x * diagOne ρ).det ≠ 0 := by
    rw [det_x_diagOne]
    exact mul_ne_zero hx hρ
  rw [ArrayGaussian.integral_comp_mulVec hdet (continuous_fy m a x _ p).aestronglyMeasurable, det_x_diagOne]
  congr 1
  have hfy : ∀ y : Fin 2 → ℝ, fy m a x (entries m x ρ) p y
      = (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (Pfix m (entries m x ρ) p) *
          Complex.exp (-(bb m : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, cvec m a (entries m x ρ) x i * ((y i : ℝ) : ℂ))) *
        Complex.exp (-((Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2 : ℝ) : ℂ)) := by
    intro y
    unfold fy
    rw [eval_shifted, mul_assoc, exp_factor]
    ring
  calc ∫ y : Fin 2 → ℝ, fy m a x (entries m x ρ) p y
      = ∫ y : Fin 2 → ℝ, (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (Pfix m (entries m x ρ) p) *
          Complex.exp (-(bb m : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, cvec m a (entries m x ρ) x i * ((y i : ℝ) : ℂ))) *
            Complex.exp (-((Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2 : ℝ) : ℂ)) :=
        integral_congr_ae (Filter.Eventually.of_forall hfy)
    _ = (∫ y : Fin 2 → ℝ, MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (Pfix m (entries m x ρ) p) *
          Complex.exp (-(bb m : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, cvec m a (entries m x ρ) x i * ((y i : ℝ) : ℂ))) *
            Complex.exp (-((Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2 : ℝ) : ℂ)) :=
        integral_mul_const _ _
    _ = _ := by
        rw [hT (Pfix m (entries m x ρ) p) (cvec m a (entries m x ρ) x)]
        rfl

private def Efun (a : ℝ) (x : Arr) : ℂ := ((|x.det|⁻¹ : ℝ) : ℂ) * Complex.exp (Rfree m a x)

private theorem continuousOn_Efun (hm : m.det ≠ 0) (a : ℝ) : ContinuousOn (Efun m a) {x : Arr | x.det ≠ 0} := by
  intro x hx
  have hx' : x.det ≠ 0 := hx
  have hn : nm2 m ≠ 0 := (nm2_pos m hm).ne'
  apply ContinuousAt.continuousWithinAt
  have hdet : ContinuousAt (fun x : Arr => x.det) x := continuous_det.continuousAt
  have h1 : ContinuousAt (fun x : Arr => |x.det|⁻¹) x := hdet.abs.inv₀ (abs_ne_zero.2 hx')
  have h2 : ContinuousAt (fun x : Arr => REfree m a x) x := by
    unfold REfree ell
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    fun_prop (disch := assumption)
  have he0 : ContinuousAt (fun x : Arr => x 1 0 / x.det) x := (continuous_entry 1 0).continuousAt.div hdet hx'
  have he1 : ContinuousAt (fun x : Arr => -(x 0 0) / x.det) x := (continuous_entry 0 0).continuousAt.neg.div hdet hx'
  have h3 : ContinuousAt (fun x : Arr => IMfree m a x) x := by
    unfold IMfree ell
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ((continuousAt_const.mul (((continuous_entry 0 1).continuousAt.mul he0).add
      ((continuous_entry 1 1).continuousAt.mul he1))).div_const _).neg
  have h1' : ContinuousAt (fun x : Arr => ((|x.det|⁻¹ : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp h1
  have h2' : ContinuousAt (fun x : Arr => ((REfree m a x : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp h2
  have h3' : ContinuousAt (fun x : Arr => ((IMfree m a x : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp h3
  have hR : ContinuousAt (fun x : Arr => Rfree m a x) x := by
    unfold Rfree
    exact h2'.add (continuousAt_const.mul h3')
  unfold Efun
  exact h1'.mul (Complex.continuous_exp.continuousAt.comp hR)

private theorem continuous_Bfun : Continuous (Bfun m) := by
  unfold Bfun
  exact (((continuous_entry 0 0).mul (continuous_entry 0 1)).add
    ((continuous_entry 1 0).mul (continuous_entry 1 1))).mul continuous_const

private theorem norm_Efun (a : ℝ) (x : Arr) : ‖Efun m a x‖ = |x.det|⁻¹ * Real.exp (REfree m a x) := by
  unfold Efun
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_exp]
  congr 2
  simp [Rfree]

private theorem REfree_eq (a : ℝ) {x : Arr} (hx : x 0 0 ^ 2 + x 1 0 ^ 2 = 1) (hdet : x.det ≠ 0) :
    REfree m a x = -(Real.pi * Cconst m * (x 0 1 ^ 2 + x 1 1 ^ 2)) - Real.pi * a ^ 2 / nm2 m * (x.det ^ 2)⁻¹ := by
  unfold REfree
  rw [ell_sq_sum hx hdet]
  ring

private theorem abs_det_inv_le (x : Arr) : |x.det|⁻¹ ≤ 1 + (x.det ^ 2)⁻¹ := by
  have h := abs_inv_det_le_gauge x
  have h1 : |x.det⁻¹| ≤ 1 + (x.det ^ 2)⁻¹ := by
    have hsq : |x.det⁻¹| ^ 2 = (x.det ^ 2)⁻¹ := by rw [sq_abs, inv_pow]
    nlinarith [abs_nonneg x.det⁻¹, hsq]
  rwa [abs_inv] at h1

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end RadialProfile
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace RadialProfile

private theorem exists_radial_profile
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0)
    (a : ℝ) (ha : a ≠ 0) :
    ∃ (n : ℕ) (A' : ℝ) (c : Matrix (Fin 2) (Fin 2) ℝ → Fin (n + 1) → ℂ) (B' : Matrix (Fin 2) (Fin 2) ℝ → ℝ),
      0 < A' ∧
      ContinuousOn c {x | x.det ≠ 0} ∧
      ContinuousOn B' {x | x.det ≠ 0} ∧
      (∀ x : Matrix (Fin 2) (Fin 2) ℝ, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 → ∀ ρ : ℝ, ρ ≠ 0 →
        ∫ v : Fin 2 → ℝ,
            (MvPolynomial.eval (fun ib : Fin 2 × Fin 3 =>
                ((((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])
                  ib.1 ib.2 : ℝ) : ℂ)) p *
              gaussian3 ((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])) *
            Complex.exp ((2 * Real.pi * Complex.I) * ((a * (-(v 1)) : ℝ) : ℂ)) =
          (((|ρ| : ℝ) : ℂ))⁻¹ * (∑ j : Fin (n + 1), c x j * (ρ : ℂ) ^ (j : ℕ)) *
            Complex.exp (-(Real.pi * ((A' : ℂ) * (ρ : ℂ) ^ 2 + 2 * (B' x : ℂ) * (ρ : ℂ))))) ∧
      (∃ (K κ : ℝ) (N₀ : ℕ), 0 < κ ∧
        ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 →
          |B' x| ≤ K * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ∧
          ∀ j : Fin (n + 1),
            ‖c x j‖ * Real.exp (Real.pi * B' x ^ 2 / A') ≤
              K * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N₀ * Real.exp (-(κ * (x 0 1 ^ 2 + x 1 1 ^ 2))) *
                Real.exp (-(κ / x.det ^ 2))) := by
  obtain ⟨T, hT⟩ := GaussianMoments.exists_moment_map (bb m) (bb_pos m hm)
  have hT' : ∀ (P : MvPolynomial (Fin 2) ℂ) (c : Fin 2 → ℂ),
      ∫ y : Fin 2 → ℝ, MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P *
          Complex.exp (-(bb m : ℂ) * ∑ i, ((y i : ℝ) : ℂ) ^ 2 + ∑ i, c i * ((y i : ℝ) : ℂ))
        = MvPolynomial.eval c (T P) * Complex.exp ((∑ i, c i ^ 2) / (4 * (bb m : ℂ))) :=
    fun P c => (hT P c).2
  obtain ⟨n, c, K₀, N, hc_cont, hc_eq, hc_bound⟩ := (Tempered.mom m T a p).unpack (Efun m a) (continuousOn_Efun m hm a)
  have hκ₁ : 0 < Real.pi * a ^ 2 / nm2 m := by
    have := nm2_pos m hm
    positivity
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_poly_le_exp (half_pos hκ₁) (N + 1)
  refine ⟨n, Aconst m, c, Bfun m, Aconst_pos m hm, hc_cont, (continuous_Bfun m).continuousOn, ?_, ?_⟩
  · intro x hx hdet ρ hρ
    simp only [integrand_eq m a hdet ρ p]
    rw [integral_eq m T hT' a hdet hρ p, ← hc_eq x ρ]
    have hexp : Complex.exp ((∑ i, cvec m a (entries m x ρ) x i ^ 2) / (4 * (bb m : ℂ))) *
          Complex.exp (-((Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, entries m x ρ i b ^ 2 : ℝ) : ℂ))
        = Complex.exp (Rfree m a x) *
            Complex.exp (-(Real.pi * ((Aconst m : ℂ) * (ρ : ℂ) ^ 2 + 2 * (Bfun m x : ℂ) * (ρ : ℂ)))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [add_comm, exponent_eq m hm a x ρ, hx, one_mul, sub_eq_add_neg]
    rw [mul_assoc (Mom m T a p x ρ), hexp]
    unfold Efun
    rw [abs_mul, mul_inv]
    push_cast
    ring
  · have hδ := delta_pos m hm
    have hA := Aconst_pos m hm
    refine ⟨|kconst m| + max K₀ 0 * K₂, min (Real.pi * delta m) (Real.pi * a ^ 2 / nm2 m / 2), N,
      lt_min (by positivity) (half_pos hκ₁), ?_⟩
    intro x hx hdet
    have hW : 0 ≤ x 0 1 ^ 2 + x 1 1 ^ 2 := by positivity
    have hs : 0 ≤ (x.det ^ 2)⁻¹ := by positivity
    have hKK : 0 ≤ max K₀ 0 * K₂ := mul_nonneg (le_max_right _ _) hK₂0
    refine ⟨?_, ?_⟩
    · rw [Bfun_eq, abs_mul]
      calc |x 0 0 * x 0 1 + x 1 0 * x 1 1| * |kconst m|
          ≤ (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) * |kconst m| :=
            mul_le_mul_of_nonneg_right (abs_inner_le hx) (abs_nonneg _)
        _ ≤ (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) * (|kconst m| + max K₀ 0 * K₂) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hKK) (by positivity)
        _ = (|kconst m| + max K₀ 0 * K₂) * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) := mul_comm _ _
    · intro j
      set κ : ℝ := min (Real.pi * delta m) (Real.pi * a ^ 2 / nm2 m / 2) with hκ
      have hκ1 : κ ≤ Real.pi * delta m := min_le_left _ _
      have hκ2 : κ ≤ Real.pi * a ^ 2 / nm2 m / 2 := min_le_right _ _
      have hc1 : ‖c x j‖ ≤ (|x.det|⁻¹ * Real.exp (REfree m a x)) * (max K₀ 0 * gauge x ^ N) := by
        refine (hc_bound x hx hdet j).trans ?_
        rw [norm_Efun]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) (gauge_pow_nonneg x N))
          (by positivity)
      have hB : Real.pi * Bfun m x ^ 2 / Aconst m ≤ Real.pi * (Cconst m - delta m) * (x 0 1 ^ 2 + x 1 1 ^ 2) := by
        rw [Bfun_eq, mul_pow, ← kconst_sq_div_Aconst m]
        have h1 := inner_sq_le hx
        have hk : 0 ≤ kconst m ^ 2 / Aconst m := by positivity
        calc Real.pi * ((x 0 0 * x 0 1 + x 1 0 * x 1 1) ^ 2 * kconst m ^ 2) / Aconst m
            = Real.pi * (kconst m ^ 2 / Aconst m) * (x 0 0 * x 0 1 + x 1 0 * x 1 1) ^ 2 := by
              field_simp
          _ ≤ Real.pi * (kconst m ^ 2 / Aconst m) * (x 0 1 ^ 2 + x 1 1 ^ 2) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
      have hgauge : gauge x ^ N = (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N * (1 + (x.det ^ 2)⁻¹) ^ N := by
        unfold gauge
        rw [mul_pow]
      have hbr : |x.det|⁻¹ * (1 + (x.det ^ 2)⁻¹) ^ N
          ≤ K₂ * Real.exp (Real.pi * a ^ 2 / nm2 m / 2 * (x.det ^ 2)⁻¹) := by
        calc |x.det|⁻¹ * (1 + (x.det ^ 2)⁻¹) ^ N
            ≤ (1 + (x.det ^ 2)⁻¹) * (1 + (x.det ^ 2)⁻¹) ^ N :=
              mul_le_mul_of_nonneg_right (abs_det_inv_le x) (by positivity)
          _ = (1 + (x.det ^ 2)⁻¹) ^ (N + 1) := by ring
          _ ≤ K₂ * Real.exp (Real.pi * a ^ 2 / nm2 m / 2 * (x.det ^ 2)⁻¹) := hK₂ _ hs
      have hRE := REfree_eq m a hx hdet
      have hexpo : Real.pi * a ^ 2 / nm2 m / 2 * (x.det ^ 2)⁻¹ + (REfree m a x
            + Real.pi * (Cconst m - delta m) * (x 0 1 ^ 2 + x 1 1 ^ 2))
          ≤ -(κ * (x 0 1 ^ 2 + x 1 1 ^ 2)) + -(κ * (x.det ^ 2)⁻¹) := by
        rw [hRE]
        have e1 : κ * (x 0 1 ^ 2 + x 1 1 ^ 2) ≤ Real.pi * delta m * (x 0 1 ^ 2 + x 1 1 ^ 2) :=
          mul_le_mul_of_nonneg_right hκ1 hW
        have e2 : κ * (x.det ^ 2)⁻¹ ≤ Real.pi * a ^ 2 / nm2 m / 2 * (x.det ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hκ2 hs
        nlinarith [e1, e2]
      calc ‖c x j‖ * Real.exp (Real.pi * Bfun m x ^ 2 / Aconst m)
          ≤ ((|x.det|⁻¹ * Real.exp (REfree m a x)) * (max K₀ 0 * gauge x ^ N)) *
              Real.exp (Real.pi * (Cconst m - delta m) * (x 0 1 ^ 2 + x 1 1 ^ 2)) :=
            mul_le_mul hc1 (Real.exp_le_exp.2 hB) (Real.exp_pos _).le
              (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
                (mul_nonneg (le_max_right _ _) (gauge_pow_nonneg x N)))
        _ = (max K₀ 0 * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N) * (|x.det|⁻¹ * (1 + (x.det ^ 2)⁻¹) ^ N) *
              Real.exp (REfree m a x + Real.pi * (Cconst m - delta m) * (x 0 1 ^ 2 + x 1 1 ^ 2)) := by
            rw [hgauge, Real.exp_add]
            ring
        _ ≤ (max K₀ 0 * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N) *
              (K₂ * Real.exp (Real.pi * a ^ 2 / nm2 m / 2 * (x.det ^ 2)⁻¹)) *
              Real.exp (REfree m a x + Real.pi * (Cconst m - delta m) * (x 0 1 ^ 2 + x 1 1 ^ 2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbr (by positivity)) (Real.exp_pos _).le
        _ = (max K₀ 0 * K₂) * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N *
              Real.exp (Real.pi * a ^ 2 / nm2 m / 2 * (x.det ^ 2)⁻¹ + (REfree m a x
                + Real.pi * (Cconst m - delta m) * (x 0 1 ^ 2 + x 1 1 ^ 2))) := by
            simp only [Real.exp_add]
            ring
        _ ≤ (|kconst m| + max K₀ 0 * K₂) * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N *
              Real.exp (-(κ * (x 0 1 ^ 2 + x 1 1 ^ 2)) + -(κ * (x.det ^ 2)⁻¹)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) (by positivity))
              (Real.exp_le_exp.2 hexpo) (Real.exp_pos _).le (by positivity)
        _ = (|kconst m| + max K₀ 0 * K₂) * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N *
              Real.exp (-(κ * (x 0 1 ^ 2 + x 1 1 ^ 2))) * Real.exp (-(κ / x.det ^ 2)) := by
            rw [Real.exp_add, div_eq_mul_inv]
            ring

end RadialProfile
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

section
open MeasureTheory Set

namespace ChartMajorant

open AssemblyBridges

private noncomputable def chartMeasure : Measure ((ℝ × ℝ) × ℝ) :=
  (volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).restrict (Ioo 0 Real.pi))

private theorem det_eq (θ : ℝ) (w : ℝ × ℝ) : (unitArray θ w).det = Real.cos θ * w.2 - w.1 * Real.sin θ := by
  rw [unitArray, Matrix.det_fin_two_of]

private theorem abs_det_le (θ : ℝ) (w : ℝ × ℝ) : |(unitArray θ w).det| ≤ |w.1| + |w.2| := by
  rw [det_eq]
  have h1 : |Real.cos θ * w.2| ≤ |w.2| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)
  have h2 : |w.1 * Real.sin θ| ≤ |w.1| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one θ)
  calc |Real.cos θ * w.2 - w.1 * Real.sin θ| ≤ |Real.cos θ * w.2| + |w.1 * Real.sin θ| := abs_sub _ _
    _ ≤ |w.1| + |w.2| := by linarith

private theorem inv_eq (θ : ℝ) (w : ℝ × ℝ) :
    (unitArray θ w)⁻¹ = (unitArray θ w).det⁻¹ • !![w.2, -w.1; -Real.sin θ, Real.cos θ] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  congr 1
  rw [unitArray, Matrix.adjugate_fin_two_of]

private theorem abs_det_inv_inv (θ : ℝ) (w : ℝ × ℝ) : |((unitArray θ w)⁻¹).det|⁻¹ = |(unitArray θ w).det| := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv, inv_inv]

private theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]

private theorem bracket_le (θ : ℝ) (w : ℝ × ℝ) :
    1 + |(unitArray θ w)⁻¹ 0 0| + |(unitArray θ w)⁻¹ 0 1| + |(unitArray θ w)⁻¹ 1 0| + |(unitArray θ w)⁻¹ 1 1| +
        |((unitArray θ w)⁻¹).det|⁻¹ ≤
      4 * (1 + (w.1 ^ 2 + w.2 ^ 2)) * (1 + |(unitArray θ w).det|⁻¹) := by
  set d := (unitArray θ w).det with hd_def
  have he : 0 ≤ |d|⁻¹ := inv_nonneg.2 (abs_nonneg d)
  have hdS : |d| ≤ |w.1| + |w.2| := abs_det_le θ w
  have e00 : (unitArray θ w)⁻¹ 0 0 = d⁻¹ * w.2 := by
    rw [inv_eq]
    rfl
  have e01 : (unitArray θ w)⁻¹ 0 1 = d⁻¹ * -w.1 := by
    rw [inv_eq]
    rfl
  have e10 : (unitArray θ w)⁻¹ 1 0 = d⁻¹ * -Real.sin θ := by
    rw [inv_eq]
    rfl
  have e11 : (unitArray θ w)⁻¹ 1 1 = d⁻¹ * Real.cos θ := by
    rw [inv_eq]
    rfl
  have h00 : |(unitArray θ w)⁻¹ 0 0| = |w.2| * |d|⁻¹ := by
    rw [e00, abs_mul, abs_inv, mul_comm]
  have h01 : |(unitArray θ w)⁻¹ 0 1| = |w.1| * |d|⁻¹ := by
    rw [e01, abs_mul, abs_inv, abs_neg, mul_comm]
  have h10 : |(unitArray θ w)⁻¹ 1 0| = |Real.sin θ| * |d|⁻¹ := by
    rw [e10, abs_mul, abs_inv, abs_neg, mul_comm]
  have h11 : |(unitArray θ w)⁻¹ 1 1| = |Real.cos θ| * |d|⁻¹ := by
    rw [e11, abs_mul, abs_inv, mul_comm]
  rw [h00, h01, h10, h11, abs_det_inv_inv]
  have hs1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hw1 : |w.1| ≤ 1 + w.1 ^ 2 := abs_le_one_add_sq w.1
  have hw2 : |w.2| ≤ 1 + w.2 ^ 2 := abs_le_one_add_sq w.2
  have hS : |w.1| + |w.2| + 2 ≤ 4 * (1 + (w.1 ^ 2 + w.2 ^ 2)) := by nlinarith [sq_nonneg w.1, sq_nonneg w.2]
  nlinarith [mul_nonneg he (sub_nonneg.2 hs1), mul_nonneg he (sub_nonneg.2 hc1), mul_nonneg he (sub_nonneg.2 hS),
    abs_nonneg w.1, abs_nonneg w.2]

private theorem pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (m : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v ^ m * Real.exp (-(c * v)) ≤ (m.factorial : ℝ) / c ^ m := by
  have h := Real.pow_div_factorial_le_exp (c * v) (mul_nonneg hc.le hv) m
  rw [mul_pow] at h
  have hm : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have hcm : (0 : ℝ) < c ^ m := pow_pos hc m
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hcm]
  rw [div_le_iff₀ hm] at h
  linarith

private theorem det_factor_le {κ : ℝ} (hκ : 0 < κ) (N : ℕ) (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d Q : ℝ), d ≠ 0 → 0 ≤ Q → |d| ≤ 2 * (1 + Q) →
      Real.exp (-(κ / d ^ 2)) * (1 + |d|⁻¹) ^ N * |d| ^ α ≤ C * (1 + Q) ^ ⌈α⌉₊ := by
  set a : ℕ := ⌈α⌉₊ with ha_def
  set b : ℕ := ⌈-α⌉₊ with hb_def
  set K : ℝ := ((N + b).factorial : ℝ) / κ ^ (N + b) with hK_def
  have hK : 0 ≤ K := div_nonneg (Nat.cast_nonneg _) (pow_pos hκ _).le
  refine ⟨2 ^ N * (K + 2 ^ a), by positivity, fun d Q hd hQ hdQ => ?_⟩
  have hdpos : 0 < |d| := abs_pos.2 hd
  have hQ1 : (1 : ℝ) ≤ (1 + Q) ^ a := one_le_pow₀ (by linarith)
  have hexp_eq : Real.exp (-(κ / d ^ 2)) = Real.exp (-(κ * (|d|⁻¹) ^ 2)) := by
    congr 2
    rw [inv_pow, sq_abs, div_eq_mul_inv]
  rcases le_or_gt |d| 1 with hle | hgt
  ·
    set e : ℝ := |d|⁻¹ with he_def
    have he1 : 1 ≤ e := one_le_inv_iff₀.2 ⟨hdpos, hle⟩
    have he0 : 0 ≤ e := by linarith
    have h1 : (1 + e) ^ N ≤ 2 ^ N * e ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) N
    have h2 : |d| ^ α ≤ e ^ b := by
      have hd_eq : |d| = e⁻¹ := by rw [he_def, inv_inv]
      rw [hd_eq, Real.inv_rpow he0, ← Real.rpow_neg he0, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le he1 (Nat.le_ceil (-α))
    have h3 : e ^ (N + b) * Real.exp (-(κ * e ^ 2)) ≤ K := by
      have h4 : e ^ (N + b) ≤ (e ^ 2) ^ (N + b) := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ he1 (by omega)
      calc e ^ (N + b) * Real.exp (-(κ * e ^ 2)) ≤ (e ^ 2) ^ (N + b) * Real.exp (-(κ * e ^ 2)) :=
            mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
        _ ≤ K := pow_mul_exp_neg_le hκ (N + b) (sq_nonneg e)
    have hα0 : 0 ≤ |d| ^ α := Real.rpow_nonneg (abs_nonneg d) α
    calc Real.exp (-(κ / d ^ 2)) * (1 + e) ^ N * |d| ^ α
        ≤ Real.exp (-(κ * e ^ 2)) * (2 ^ N * e ^ N) * e ^ b := by
          rw [hexp_eq]
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)) h2 hα0 (by positivity)
      _ = 2 ^ N * (e ^ (N + b) * Real.exp (-(κ * e ^ 2))) := by ring
      _ ≤ 2 ^ N * K := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2 ^ N * (K + 2 ^ a) * (1 + Q) ^ a := by
          have : (2 : ℝ) ^ N * K ≤ 2 ^ N * (K + 2 ^ a) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
          calc (2 : ℝ) ^ N * K ≤ 2 ^ N * (K + 2 ^ a) := this
            _ = 2 ^ N * (K + 2 ^ a) * 1 := (mul_one _).symm
            _ ≤ 2 ^ N * (K + 2 ^ a) * (1 + Q) ^ a := mul_le_mul_of_nonneg_left hQ1 (by positivity)
  ·
    have hinv1 : |d|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hgt.le
    have h1 : (1 + |d|⁻¹) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have h2 : |d| ^ α ≤ 2 ^ a * (1 + Q) ^ a := by
      calc |d| ^ α ≤ |d| ^ (a : ℝ) := Real.rpow_le_rpow_of_exponent_le hgt.le (Nat.le_ceil α)
        _ = |d| ^ a := Real.rpow_natCast _ _
        _ ≤ (2 * (1 + Q)) ^ a := pow_le_pow_left₀ (abs_nonneg d) hdQ a
        _ = 2 ^ a * (1 + Q) ^ a := mul_pow _ _ _
    have hexp1 : Real.exp (-(κ / d ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
    calc Real.exp (-(κ / d ^ 2)) * (1 + |d|⁻¹) ^ N * |d| ^ α ≤ 1 * 2 ^ N * (2 ^ a * (1 + Q) ^ a) :=
          mul_le_mul (mul_le_mul hexp1 h1 (by positivity) zero_le_one) h2 (Real.rpow_nonneg (abs_nonneg d) α)
            (by positivity)
      _ = 2 ^ N * 2 ^ a * (1 + Q) ^ a := by ring
      _ ≤ 2 ^ N * (K + 2 ^ a) * (1 + Q) ^ a := by
          have : (2 : ℝ) ^ N * 2 ^ a ≤ 2 ^ N * (K + 2 ^ a) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)

private theorem integrable_gaussian_chart {κ : ℝ} (hκ : 0 < κ) (c : ℝ) :
    Integrable (fun r : (ℝ × ℝ) × ℝ => c * Real.exp (-(κ / 2 * r.1.1 ^ 2)) * Real.exp (-(κ / 2 * r.1.2 ^ 2)))
      chartMeasure := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo 0 Real.pi)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hg : Integrable (fun x : ℝ => Real.exp (-(κ / 2) * x ^ 2)) := integrable_exp_neg_mul_sq (by positivity)
  have hw : Integrable
      (fun w : ℝ × ℝ => (c * Real.exp (-(κ / 2) * w.1 ^ 2)) * Real.exp (-(κ / 2) * w.2 ^ 2))
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact (hg.const_mul c).mul_prod hg
  have h := hw.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
    ((volume : Measure ℝ).restrict (Ioo 0 Real.pi)))
  refine (h.congr (Filter.Eventually.of_forall fun r => ?_))
  simp only [mul_one, neg_mul]

private theorem exists_integrable_majorant {κ : ℝ} (hκ : 0 < κ) (N₀ N : ℕ) (α : ℝ) :
    ∃ G : (ℝ × ℝ) × ℝ → ℝ, Integrable G chartMeasure ∧
      ∀ r : (ℝ × ℝ) × ℝ, (unitArray r.2 r.1).det ≠ 0 →
        (1 + (r.1.1 ^ 2 + r.1.2 ^ 2)) ^ N₀ * Real.exp (-(κ * (r.1.1 ^ 2 + r.1.2 ^ 2))) *
            Real.exp (-(κ / (unitArray r.2 r.1).det ^ 2)) *
          (1 + |(unitArray r.2 r.1)⁻¹ 0 0| + |(unitArray r.2 r.1)⁻¹ 0 1| + |(unitArray r.2 r.1)⁻¹ 1 0| +
              |(unitArray r.2 r.1)⁻¹ 1 1| + |((unitArray r.2 r.1)⁻¹).det|⁻¹) ^ N *
          |(unitArray r.2 r.1).det| ^ α ≤ G r := by
  obtain ⟨C, hC, hdet⟩ := det_factor_le hκ N α
  set m : ℕ := N₀ + N + ⌈α⌉₊ with hm_def
  set K₂ : ℝ := (m.factorial : ℝ) / (κ / 2) ^ m with hK₂_def
  have hK₂ : 0 ≤ K₂ := div_nonneg (Nat.cast_nonneg _) (by positivity)
  refine ⟨fun r => (4 ^ N * C * (Real.exp (κ / 2) * K₂)) * Real.exp (-(κ / 2 * r.1.1 ^ 2)) *
    Real.exp (-(κ / 2 * r.1.2 ^ 2)), integrable_gaussian_chart hκ _, fun r hd => ?_⟩
  set Q : ℝ := r.1.1 ^ 2 + r.1.2 ^ 2 with hQ_def
  have hQ : 0 ≤ Q := by positivity
  have hdQ : |(unitArray r.2 r.1).det| ≤ 2 * (1 + Q) := by
    have h := abs_det_le r.2 r.1
    have h1 := abs_le_one_add_sq r.1.1
    have h2 := abs_le_one_add_sq r.1.2
    rw [hQ_def]
    linarith
  have hbr := bracket_le r.2 r.1
  have hbrN : (1 + |(unitArray r.2 r.1)⁻¹ 0 0| + |(unitArray r.2 r.1)⁻¹ 0 1| + |(unitArray r.2 r.1)⁻¹ 1 0| +
        |(unitArray r.2 r.1)⁻¹ 1 1| + |((unitArray r.2 r.1)⁻¹).det|⁻¹) ^ N ≤
      4 ^ N * (1 + Q) ^ N * (1 + |(unitArray r.2 r.1).det|⁻¹) ^ N := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbr N
  have hD := hdet (unitArray r.2 r.1).det Q hd hQ hdQ
  have habs : (1 + Q) ^ m * Real.exp (-(κ * Q)) ≤ Real.exp (κ / 2) * K₂ * Real.exp (-(κ / 2 * Q)) := by
    have h := pow_mul_exp_neg_le (half_pos hκ) m (by linarith : (0 : ℝ) ≤ 1 + Q)
    have hsplit : Real.exp (-(κ * Q)) =
        Real.exp (κ / 2) * Real.exp (-(κ / 2 * (1 + Q))) * Real.exp (-(κ / 2 * Q)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    calc (1 + Q) ^ m * (Real.exp (κ / 2) * Real.exp (-(κ / 2 * (1 + Q))) * Real.exp (-(κ / 2 * Q)))
        = Real.exp (κ / 2) * ((1 + Q) ^ m * Real.exp (-(κ / 2 * (1 + Q)))) * Real.exp (-(κ / 2 * Q)) := by ring
      _ ≤ Real.exp (κ / 2) * K₂ * Real.exp (-(κ / 2 * Q)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hgauss : Real.exp (-(κ / 2 * Q)) = Real.exp (-(κ / 2 * r.1.1 ^ 2)) * Real.exp (-(κ / 2 * r.1.2 ^ 2)) := by
    rw [← Real.exp_add, hQ_def]
    congr 1
    ring
  have hα0 : 0 ≤ |(unitArray r.2 r.1).det| ^ α := Real.rpow_nonneg (abs_nonneg _) α
  calc (1 + Q) ^ N₀ * Real.exp (-(κ * Q)) * Real.exp (-(κ / (unitArray r.2 r.1).det ^ 2)) *
          (1 + |(unitArray r.2 r.1)⁻¹ 0 0| + |(unitArray r.2 r.1)⁻¹ 0 1| + |(unitArray r.2 r.1)⁻¹ 1 0| +
              |(unitArray r.2 r.1)⁻¹ 1 1| + |((unitArray r.2 r.1)⁻¹).det|⁻¹) ^ N *
          |(unitArray r.2 r.1).det| ^ α
      ≤ (1 + Q) ^ N₀ * Real.exp (-(κ * Q)) * Real.exp (-(κ / (unitArray r.2 r.1).det ^ 2)) *
          (4 ^ N * (1 + Q) ^ N * (1 + |(unitArray r.2 r.1).det|⁻¹) ^ N) * |(unitArray r.2 r.1).det| ^ α := by
        gcongr
    _ = 4 ^ N * ((1 + Q) ^ (N₀ + N) * Real.exp (-(κ * Q))) *
          (Real.exp (-(κ / (unitArray r.2 r.1).det ^ 2)) * (1 + |(unitArray r.2 r.1).det|⁻¹) ^ N *
            |(unitArray r.2 r.1).det| ^ α) := by
        rw [pow_add]
        ring
    _ ≤ 4 ^ N * ((1 + Q) ^ (N₀ + N) * Real.exp (-(κ * Q))) * (C * (1 + Q) ^ ⌈α⌉₊) := by
        gcongr
    _ = 4 ^ N * C * ((1 + Q) ^ m * Real.exp (-(κ * Q))) := by
        rw [hm_def, pow_add, pow_add]
        ring
    _ ≤ 4 ^ N * C * (Real.exp (κ / 2) * K₂ * Real.exp (-(κ / 2 * Q))) := by
        gcongr
    _ = 4 ^ N * C * (Real.exp (κ / 2) * K₂) * Real.exp (-(κ / 2 * r.1.1 ^ 2)) * Real.exp (-(κ / 2 * r.1.2 ^ 2)) := by
        rw [hgauss]
        ring

end ChartMajorant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace ChartMajorant

open AssemblyBridges

private theorem volume_setOf_det_eq_zero_fixed (θ : ℝ) :
    (volume : Measure (ℝ × ℝ)) {w : ℝ × ℝ | (unitArray θ w).det = 0} = 0 := by
  by_cases hc : Real.cos θ = 0
  · have hs : Real.sin θ ≠ 0 := by
      intro hs
      have h := Real.sin_sq_add_cos_sq θ
      rw [hs, hc] at h
      norm_num at h
    have hsub : {w : ℝ × ℝ | (unitArray θ w).det = 0} ⊆ ({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      intro w hw
      have hw' : (unitArray θ w).det = 0 := hw
      rw [det_eq, hc, zero_mul, zero_sub, neg_eq_zero] at hw'
      refine ⟨?_, trivial⟩
      show w.1 = 0
      exact (mul_eq_zero.1 hw').resolve_right hs
    refine measure_mono_null hsub ?_
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  · have hsub : {w : ℝ × ℝ | (unitArray θ w).det = 0} ⊆ {p : ℝ × ℝ | Real.cos θ * p.2 = Real.sin θ * p.1} := by
      intro w hw
      have hw' : (unitArray θ w).det = 0 := hw
      rw [det_eq, sub_eq_zero] at hw'
      show Real.cos θ * w.2 = Real.sin θ * w.1
      rw [hw']
      ring
    exact measure_mono_null hsub (SingularArrays.volume_setOf_line_eq_zero (Real.cos θ) (Real.sin θ) hc)

private theorem ae_det_unitArray_ne_zero : ∀ᵐ r ∂chartMeasure, (unitArray r.2 r.1).det ≠ 0 := by
  have hcont : Continuous fun r : (ℝ × ℝ) × ℝ => (unitArray r.2 r.1).det := by
    simp only [det_eq]
    fun_prop
  have hmeas : MeasurableSet {r : (ℝ × ℝ) × ℝ | (unitArray r.2 r.1).det = 0} :=
    hcont.measurable (measurableSet_singleton (0 : ℝ))
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [chartMeasure, Measure.prod_apply_symm hmeas]
  refine (lintegral_congr fun θ => ?_).trans lintegral_zero
  exact volume_setOf_det_eq_zero_fixed θ

end ChartMajorant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

section
open MeasureTheory

namespace AbsoluteTate

section Majorant

open MeasureTheory Set Filter Topology
p2m_open_scoped "Nat Set.Nat Filter.Nat"

private theorem add_pow_le_two_pow_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (K : ℕ) :
    (x + y) ^ K ≤ 2 ^ K * (x ^ K + y ^ K) := by
  have h1 : x + y ≤ 2 * max x y := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : max x y ^ K ≤ x ^ K + y ^ K := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg hx K)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hy K)
  calc (x + y) ^ K ≤ (2 * max x y) ^ K := pow_le_pow_left₀ (by positivity) h1 K
    _ = 2 ^ K * max x y ^ K := mul_pow _ _ _
    _ ≤ 2 ^ K * (x ^ K + y ^ K) := by gcongr

private theorem pow_mul_exp_le_gaussians (K : ℕ) {A : ℝ} (hA : 0 < A) (c ρ : ℝ) :
    |ρ| ^ K * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) ≤
      2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) +
        2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2)) := by
  set u := ρ + c with hu
  have hb : 0 < Real.pi * A := by positivity
  have hρu : |ρ| ≤ |u| + |c| := by
    calc |ρ| = |u - c| := by rw [hu]; ring_nf
      _ ≤ |u| + |c| := abs_sub _ _
  have h1 : |ρ| ^ K ≤ 2 ^ K * (|u| ^ K + |c| ^ K) :=
    (pow_le_pow_left₀ (abs_nonneg ρ) hρu K).trans (add_pow_le_two_pow_mul (abs_nonneg u) (abs_nonneg c) K)
  have h2 : |u| ^ K ≤ 1 + |u| ^ (2 * K) := by
    rcases le_or_gt |u| 1 with hle | hgt
    · exact (pow_le_one₀ (abs_nonneg u) hle).trans (le_add_of_nonneg_right (by positivity))
    · exact (pow_le_pow_right₀ hgt.le (by omega)).trans (le_add_of_nonneg_left zero_le_one)
  have h3 : |u| ^ (2 * K) ≤ (K ! : ℝ) * (2 / (Real.pi * A)) ^ K * Real.exp (Real.pi * A / 2 * u ^ 2) := by
    have hx : 0 ≤ Real.pi * A / 2 * u ^ 2 := by positivity
    have hpf := Real.pow_div_factorial_le_exp (x := Real.pi * A / 2 * u ^ 2) hx K
    have hid : |u| ^ (2 * K) = (Real.pi * A / 2 * u ^ 2) ^ K * (2 / (Real.pi * A)) ^ K := by
      rw [pow_mul, sq_abs, ← mul_pow]
      congr 1
      field_simp
    rw [hid]
    have : (Real.pi * A / 2 * u ^ 2) ^ K ≤ (K ! : ℝ) * Real.exp (Real.pi * A / 2 * u ^ 2) := by
      rw [div_le_iff₀ (by positivity)] at hpf
      linarith
    calc (Real.pi * A / 2 * u ^ 2) ^ K * (2 / (Real.pi * A)) ^ K
        ≤ ((K ! : ℝ) * Real.exp (Real.pi * A / 2 * u ^ 2)) * (2 / (Real.pi * A)) ^ K :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (K ! : ℝ) * (2 / (Real.pi * A)) ^ K * Real.exp (Real.pi * A / 2 * u ^ 2) := by ring
  have hexp : Real.exp (Real.pi * A / 2 * u ^ 2) * Real.exp (-(Real.pi * A * u ^ 2)) =
      Real.exp (-(Real.pi * A / 2 * u ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hE0 : 0 ≤ Real.exp (-(Real.pi * A * u ^ 2)) := (Real.exp_pos _).le
  calc |ρ| ^ K * Real.exp (-(Real.pi * A * u ^ 2))
      ≤ 2 ^ K * (|u| ^ K + |c| ^ K) * Real.exp (-(Real.pi * A * u ^ 2)) := mul_le_mul_of_nonneg_right h1 hE0
    _ ≤ 2 ^ K * ((1 + (K ! : ℝ) * (2 / (Real.pi * A)) ^ K * Real.exp (Real.pi * A / 2 * u ^ 2)) + |c| ^ K) *
          Real.exp (-(Real.pi * A * u ^ 2)) := by
        gcongr
        exact h2.trans (by linarith)
    _ = 2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * u ^ 2)) +
          2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) *
            (Real.exp (Real.pi * A / 2 * u ^ 2) * Real.exp (-(Real.pi * A * u ^ 2))) := by ring
    _ = _ := by rw [hexp]

private theorem integral_exp_neg_mul_sq_add (b c : ℝ) :
    ∫ ρ : ℝ, Real.exp (-(b * (ρ + c) ^ 2)) = Real.sqrt (Real.pi / b) := by
  have h := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
    (fun t : ℝ => Real.exp (-(b * t ^ 2))) c
  rw [h, ← integral_gaussian b]
  congr 1; funext t; ring_nf

private theorem integrable_exp_neg_mul_sq_add {b : ℝ} (hb : 0 < b) (c : ℝ) :
    MeasureTheory.Integrable (fun ρ : ℝ => Real.exp (-(b * (ρ + c) ^ 2))) := by
  have h := (integrable_exp_neg_mul_sq hb).comp_add_right c
  refine h.congr (Filter.Eventually.of_forall (fun ρ => ?_))
  beta_reduce
  ring_nf

private theorem one_le_maxA {A : ℝ} (hA : 0 < A) : 1 ≤ max A A⁻¹ := by
  rcases le_or_gt 1 A with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right (one_le_inv₀ hA |>.mpr h.le)

private theorem inv_le_maxA {A : ℝ} : A⁻¹ ≤ max A A⁻¹ := le_max_right _ _

private theorem sqrt_le_of_one_le {x y : ℝ} (hy : 1 ≤ y) (hxy : x ≤ y) : Real.sqrt x ≤ y :=
  Real.sqrt_le_iff.mpr ⟨by linarith, hxy.trans (by nlinarith)⟩

private theorem integrable_sing {e : ℝ} (he : -1 < e) :
    Integrable (fun ρ : ℝ => Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e) := by
  have hf : IntegrableOn (fun t : ℝ => t ^ e * Real.exp (-1 * t ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq one_pos he
  have hIoi : IntegrableOn (fun t : ℝ => |t| ^ e * Real.exp (-1 * |t| ^ 2)) (Ioi 0) := by
    refine hf.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp ht)]
  have hIic : IntegrableOn (fun t : ℝ => |t| ^ e * Real.exp (-1 * |t| ^ 2)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  have h := hIic.union hIoi
  rw [Iic_union_Ioi, integrableOn_univ] at h
  refine h.congr (Eventually.of_forall fun ρ => ?_)
  simp only [sq_abs]
  ring_nf

private theorem sing_integral_nonneg (e : ℝ) : 0 ≤ ∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e :=
  integral_nonneg (fun ρ => by positivity)

private theorem pow_mul_rpow_mul_exp_le {n : ℕ} (j : Fin (n + 1)) (σ : ℝ) {A : ℝ} (hA : 0 < A) (c : ℝ) {ρ : ℝ}
    (hρ : ρ ≠ 0) :
    |ρ| ^ (j : ℕ) * |ρ| ^ (σ - 1) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) ≤
      Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (σ - 1)) +
        |ρ| ^ (n + ⌈σ⌉₊) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by
  have habs : 0 < |ρ| := abs_pos.mpr hρ
  have hE : Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := mul_nonneg (mul_nonneg Real.pi_pos.le hA.le) (sq_nonneg (ρ + c)); linarith)
  have hE0 : 0 ≤ Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := (Real.exp_pos _).le
  rcases le_or_gt |ρ| 1 with h1 | h1
  · have hj : |ρ| ^ (j : ℕ) ≤ 1 := pow_le_one₀ habs.le h1
    have hg : 1 ≤ Real.exp 1 * Real.exp (-(1 * ρ ^ 2)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have : ρ ^ 2 ≤ 1 := by
        have := sq_abs ρ
        nlinarith [habs]
      linarith
    have hpos2 : 0 ≤ |ρ| ^ (n + ⌈σ⌉₊) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by positivity
    calc |ρ| ^ (j : ℕ) * |ρ| ^ (σ - 1) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2))
        ≤ 1 * |ρ| ^ (σ - 1) * 1 := by
          gcongr
      _ = |ρ| ^ (σ - 1) := by ring
      _ ≤ (Real.exp 1 * Real.exp (-(1 * ρ ^ 2))) * |ρ| ^ (σ - 1) :=
          le_mul_of_one_le_left (Real.rpow_nonneg habs.le _) hg
      _ = Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (σ - 1)) := by ring
      _ ≤ _ := le_add_of_nonneg_right hpos2
  · have hj : |ρ| ^ (j : ℕ) ≤ |ρ| ^ n := pow_le_pow_right₀ h1.le (Nat.lt_succ_iff.mp j.2)
    have hr : |ρ| ^ (σ - 1) ≤ |ρ| ^ (⌈σ⌉₊ : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith [Nat.le_ceil σ])
    have hpos1 : 0 ≤ Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (σ - 1)) := by positivity
    calc |ρ| ^ (j : ℕ) * |ρ| ^ (σ - 1) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2))
        ≤ |ρ| ^ n * |ρ| ^ (⌈σ⌉₊ : ℕ) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by
          gcongr
      _ = |ρ| ^ (n + ⌈σ⌉₊) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by rw [pow_add]
      _ ≤ _ := le_add_of_nonneg_left hpos1

private noncomputable def majZ (K : ℕ) (e A c : ℝ) (ρ : ℝ) : ℝ :=
  Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e) +
    2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) +
      2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2))

private theorem integrable_majZ (K : ℕ) {e : ℝ} (he : -1 < e) {A : ℝ} (hA : 0 < A) (c : ℝ) :
    Integrable (majZ K e A c) := by
  unfold majZ
  exact (((integrable_sing he).const_mul _).add
    ((integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _)).add
    ((integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _)

private theorem integral_majZ (K : ℕ) {e : ℝ} (he : -1 < e) {A : ℝ} (hA : 0 < A) (c : ℝ) :
    ∫ ρ : ℝ, majZ K e A c ρ =
      Real.exp 1 * (∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e) +
        2 ^ K * (1 + |c| ^ K) * Real.sqrt (Real.pi / (Real.pi * A)) +
          2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2)) := by
  have i1 : Integrable (fun ρ : ℝ => Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e)) :=
    (integrable_sing he).const_mul _
  have i2 : Integrable (fun ρ : ℝ => 2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2))) :=
    (integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _
  have i3 : Integrable (fun ρ : ℝ =>
      2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2))) :=
    (integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _
  have e1 : ∫ ρ : ℝ, Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e) =
      Real.exp 1 * ∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e :=
    integral_const_mul (Real.exp 1) (fun ρ : ℝ => Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e)
  have e2 : ∫ ρ : ℝ, 2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) =
      2 ^ K * (1 + |c| ^ K) * ∫ ρ : ℝ, Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) :=
    integral_const_mul (2 ^ K * (1 + |c| ^ K)) (fun ρ : ℝ => Real.exp (-(Real.pi * A * (ρ + c) ^ 2)))
  have e3 : ∫ ρ : ℝ, 2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2)) =
      2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * ∫ ρ : ℝ, Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2)) :=
    integral_const_mul (2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K))
      (fun ρ : ℝ => Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2)))
  have i12 : Integrable (fun ρ : ℝ => Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e) +
      2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2))) := i1.add i2
  unfold majZ
  rw [integral_add i12 i3, integral_add i1 i2, e1, e2, e3, integral_exp_neg_mul_sq_add _ c,
    integral_exp_neg_mul_sq_add _ c]

private theorem nonneg_majZ (K : ℕ) (e : ℝ) {A : ℝ} (hA : 0 < A) (c ρ : ℝ) : 0 ≤ majZ K e A c ρ := by
  unfold majZ; positivity

private theorem integral_majZ_le (K : ℕ) {e : ℝ} (he : -1 < e) {A : ℝ} (hA : 0 < A) (B : ℝ) :
    ∫ ρ : ℝ, majZ K e A (B / A) ρ ≤
      (Real.exp 1 * (∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e) + 2 ^ (K + 1) +
          2 ^ (2 * K + 1) * (K ! : ℝ)) *
        max A A⁻¹ ^ (K + 1) * (1 + |B|) ^ (K + 1) := by
  rw [integral_majZ K he hA]
  set m := max A A⁻¹ with hm
  set β' := 1 + |B| with hβ'
  have hm1 : 1 ≤ m := one_le_maxA hA
  have hβ1 : 1 ≤ β' := by rw [hβ']; linarith [abs_nonneg B]
  have hm0 : 0 ≤ m := by linarith
  have hβ0 : 0 ≤ β' := by linarith
  have hmN : 1 ≤ m ^ (K + 1) := one_le_pow₀ hm1
  have hβN : 1 ≤ β' ^ (K + 1) := one_le_pow₀ hβ1
  have hc₁ := sing_integral_nonneg e
  set c₁ := ∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ e with hc₁def
  have h1 : Real.exp 1 * c₁ ≤ Real.exp 1 * c₁ * (m ^ (K + 1) * β' ^ (K + 1)) :=
    le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hmN hβN)
  have hcBA : |B / A| ≤ β' * m := by
    rw [abs_div, abs_of_pos hA, div_eq_mul_inv]
    have h1' : |B| ≤ β' := by rw [hβ']; linarith
    have h2' : A⁻¹ ≤ m := inv_le_maxA
    exact mul_le_mul h1' h2' (inv_pos.mpr hA).le hβ0
  have hcK : 1 + |B / A| ^ K ≤ 2 * (β' ^ K * m ^ K) := by
    have : |B / A| ^ K ≤ (β' * m) ^ K := pow_le_pow_left₀ (abs_nonneg _) hcBA K
    rw [mul_pow] at this
    have hone : 1 ≤ β' ^ K * m ^ K := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hβ1) (one_le_pow₀ hm1)
    linarith
  have hsq1 : Real.sqrt (Real.pi / (Real.pi * A)) ≤ m := by
    have : Real.pi / (Real.pi * A) = A⁻¹ := by field_simp
    rw [this]
    exact sqrt_le_of_one_le hm1 inv_le_maxA
  have hpow : (2 / (Real.pi * A)) ^ K ≤ (2 * m) ^ K := by
    refine pow_le_pow_left₀ (by positivity) ?_ K
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc 2 / (Real.pi * A) ≤ 2 / (1 * A) := by
          gcongr
      _ = 2 * A⁻¹ := by ring
      _ ≤ 2 * m := by gcongr; exact inv_le_maxA
  have hsq2 : Real.sqrt (Real.pi / (Real.pi * A / 2)) ≤ 2 * m := by
    have : Real.pi / (Real.pi * A / 2) = 2 * A⁻¹ := by field_simp
    rw [this]
    exact sqrt_le_of_one_le (by linarith) (by gcongr; exact inv_le_maxA)
  have h2 : 2 ^ K * (1 + |B / A| ^ K) * Real.sqrt (Real.pi / (Real.pi * A)) ≤
      2 ^ (K + 1) * (m ^ (K + 1) * β' ^ (K + 1)) := by
    calc 2 ^ K * (1 + |B / A| ^ K) * Real.sqrt (Real.pi / (Real.pi * A))
        ≤ 2 ^ K * (2 * (β' ^ K * m ^ K)) * m := by
          gcongr
      _ = 2 ^ (K + 1) * (m ^ (K + 1) * β' ^ K) := by ring
      _ ≤ 2 ^ (K + 1) * (m ^ (K + 1) * β' ^ (K + 1)) := by
          gcongr
          all_goals first | exact hβ1 | omega
  have h3 : 2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2)) ≤
      2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * β' ^ (K + 1)) := by
    calc 2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2))
        ≤ 2 ^ K * ((K ! : ℝ) * (2 * m) ^ K) * (2 * m) := by
          gcongr
      _ = 2 ^ (2 * K + 1) * (K ! : ℝ) * m ^ (K + 1) := by rw [mul_pow]; ring
      _ = 2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * 1) := by ring
      _ ≤ 2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * β' ^ (K + 1)) := by
          gcongr
  calc Real.exp 1 * c₁ + 2 ^ K * (1 + |B / A| ^ K) * Real.sqrt (Real.pi / (Real.pi * A)) +
        2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2))
      ≤ Real.exp 1 * c₁ * (m ^ (K + 1) * β' ^ (K + 1)) + 2 ^ (K + 1) * (m ^ (K + 1) * β' ^ (K + 1)) +
          2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * β' ^ (K + 1)) := add_le_add (add_le_add h1 h2) h3
    _ = (Real.exp 1 * c₁ + 2 ^ (K + 1) + 2 ^ (2 * K + 1) * (K ! : ℝ)) * m ^ (K + 1) * β' ^ (K + 1) := by ring

end Majorant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

section Integrand

open MeasureTheory
open scoped Nat

private theorem measurable_sign' : Measurable Real.sign := by
  have : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 := by
    funext r; rfl
  rw [this]
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

private noncomputable def integrand (n δ : ℕ) (c : Fin (n + 1) → ℂ) (A B : ℝ) (z : ℂ) (ρ : ℝ) : ℂ :=
  (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) * (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) *
    (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)

private theorem measurable_integrand (n δ : ℕ) (c : Fin (n + 1) → ℂ) (A B : ℝ) (z : ℂ) :
    Measurable (integrand n δ c A B z) := by
  unfold integrand
  have hsum : Measurable fun ρ : ℝ => ∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ) :=
    Finset.measurable_sum _ (fun j _ => (Complex.measurable_ofReal.pow_const (j : ℕ)).const_mul (c j))
  have hinner : Measurable fun ρ : ℝ => -(Real.pi * (A * ρ ^ 2 + 2 * B * ρ)) := by fun_prop
  have hexp : Measurable fun ρ : ℝ => (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp hinner)
  exact ((hsum.mul hexp).mul ((Complex.measurable_ofReal.comp measurable_sign').pow_const δ)).mul
    ((Complex.measurable_ofReal.comp measurable_abs).pow_const (z - 1))

private theorem norm_sum_le' (n : ℕ) (c : Fin (n + 1) → ℂ) (ρ : ℝ) :
    ‖∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)‖ ≤ ∑ j : Fin (n + 1), ‖c j‖ * |ρ| ^ (j : ℕ) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_exp_eq {A : ℝ} (hA : 0 < A) (B ρ : ℝ) :
    ‖(Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ)‖ =
      Real.exp (Real.pi * B ^ 2 / A) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)) := by
  have hA0 : A ≠ 0 := hA.ne'
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  congr 1
  field_simp
  ring

private theorem norm_tail_eq (δ : ℕ) (z : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ‖(Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)‖ = |ρ| ^ (z.re - 1) := by
  have habs : 0 < |ρ| := abs_pos.mpr hρ
  have hsign : ‖(Real.sign ρ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases Real.sign_apply_eq_of_ne_zero ρ hρ with hs | hs <;> rw [hs] <;> norm_num
  rw [norm_mul, norm_pow, hsign, one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos habs, Complex.sub_re,
    Complex.one_re]

private theorem norm_integrand_le (n δ : ℕ) (c : Fin (n + 1) → ℂ) {A : ℝ} (hA : 0 < A) (B : ℝ) (z : ℂ) {ρ : ℝ}
    (hρ : ρ ≠ 0) :
    ‖integrand n δ c A B z ρ‖ ≤
      Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) * majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ := by
  have hsplit : integrand n δ c A B z ρ =
      (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) * (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) *
        ((Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)) := by
    unfold integrand; ring
  rw [hsplit, norm_mul, norm_mul, norm_exp_eq hA, norm_tail_eq δ z hρ]
  have hmono : ∀ j : Fin (n + 1),
      |ρ| ^ (j : ℕ) * |ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)) ≤
        majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ := by
    intro j
    refine (pow_mul_rpow_mul_exp_le j z.re hA (B / A) hρ).trans ?_
    unfold majZ
    have := pow_mul_exp_le_gaussians (n + ⌈z.re⌉₊) hA (B / A) ρ
    linarith
  have hev := norm_sum_le' n c ρ
  have hE0 : 0 ≤ Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)) := (Real.exp_pos _).le
  have hw0 : 0 ≤ |ρ| ^ (z.re - 1) := Real.rpow_nonneg (abs_nonneg ρ) _
  have hP0 : 0 < Real.exp (Real.pi * B ^ 2 / A) := Real.exp_pos _
  calc ‖∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)‖ *
        (Real.exp (Real.pi * B ^ 2 / A) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2))) * |ρ| ^ (z.re - 1)
      = Real.exp (Real.pi * B ^ 2 / A) *
          (‖∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)‖ *
            (|ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)))) := by ring
    _ ≤ Real.exp (Real.pi * B ^ 2 / A) *
          ((∑ j : Fin (n + 1), ‖c j‖ * |ρ| ^ (j : ℕ)) *
            (|ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)))) := by
        gcongr
    _ = Real.exp (Real.pi * B ^ 2 / A) *
          ∑ j : Fin (n + 1), ‖c j‖ *
            (|ρ| ^ (j : ℕ) * |ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2))) := by
        rw [Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ ≤ Real.exp (Real.pi * B ^ 2 / A) *
          ∑ j : Fin (n + 1), ‖c j‖ * majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ := by
        gcongr with j _
        exact hmono j
    _ = Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) * majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ := by
        rw [← Finset.sum_mul]; ring

private theorem integrable_integrand_and_le (n δ : ℕ) {z : ℂ} (hz : 0 < z.re) {A : ℝ} (hA : 0 < A)
    (c : Fin (n + 1) → ℂ) (B : ℝ) :
    Integrable (integrand n δ c A B z) ∧
      ∫ ρ : ℝ, ‖integrand n δ c A B z ρ‖ ≤
        (Real.exp 1 * (∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (z.re - 1)) + 2 ^ (n + ⌈z.re⌉₊ + 1) +
              2 ^ (2 * (n + ⌈z.re⌉₊) + 1) * ((n + ⌈z.re⌉₊) ! : ℝ)) * max A A⁻¹ ^ (n + ⌈z.re⌉₊ + 1) *
            (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ (n + ⌈z.re⌉₊ + 1) * Real.exp (Real.pi * B ^ 2 / A) := by
  have he : -1 < z.re - 1 := by linarith
  have hmaj : Integrable (fun ρ : ℝ =>
      Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) * majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ) :=
    (integrable_majZ (n + ⌈z.re⌉₊) he hA (B / A)).const_mul _
  have hae : ∀ᵐ ρ : ℝ, ‖integrand n δ c A B z ρ‖ ≤
      Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) * majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ρ hρ
    exact norm_integrand_le n δ c hA B z hρ
  have hint : Integrable (integrand n δ c A B z) :=
    hmaj.mono' (measurable_integrand n δ c A B z).aestronglyMeasurable hae
  refine ⟨hint, ?_⟩
  have hpull : ∫ ρ : ℝ,
      Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) * majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ =
        Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) *
          ∫ ρ : ℝ, majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ :=
    integral_const_mul (Real.exp (Real.pi * B ^ 2 / A) * ∑ j : Fin (n + 1), ‖c j‖)
      (majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A))
  have hS0 : 0 ≤ ∑ j : Fin (n + 1), ‖c j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hP0 : 0 ≤ Real.exp (Real.pi * B ^ 2 / A) := (Real.exp_pos _).le
  calc ∫ ρ : ℝ, ‖integrand n δ c A B z ρ‖
      ≤ ∫ ρ : ℝ, Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) *
          majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ := integral_mono_ae hint.norm hmaj hae
    _ = Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) *
          ∫ ρ : ℝ, majZ (n + ⌈z.re⌉₊) (z.re - 1) A (B / A) ρ := hpull
    _ ≤ Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖c j‖) *
          ((Real.exp 1 * (∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (z.re - 1)) + 2 ^ (n + ⌈z.re⌉₊ + 1) +
              2 ^ (2 * (n + ⌈z.re⌉₊) + 1) * ((n + ⌈z.re⌉₊) ! : ℝ)) *
            max A A⁻¹ ^ (n + ⌈z.re⌉₊ + 1) * (1 + |B|) ^ (n + ⌈z.re⌉₊ + 1)) := by
        gcongr
        exact integral_majZ_le (n + ⌈z.re⌉₊) he hA B
    _ = _ := by ring

end Integrand
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

private theorem main (n δ : ℕ) {z : ℂ} (hz : 0 < z.re) {A : ℝ} (hA : 0 < A) :
    ∃ (C : ℝ) (N : ℕ), ∀ (c : Fin (n + 1) → ℂ) (B : ℝ),
      MeasureTheory.Integrable (integrand n δ c A B z) ∧
      ∫ ρ : ℝ, ‖integrand n δ c A B z ρ‖ ≤
        C * (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) :=
  ⟨_, n + ⌈z.re⌉₊ + 1, fun c B => integrable_integrand_and_le n δ hz hA c B⟩

private theorem integrable_and_integral_norm_le (n δ : ℕ) {z : ℂ} (hz : 0 < z.re) {A : ℝ} (hA : 0 < A) :
    ∃ (C : ℝ) (N : ℕ), ∀ (c : Fin (n + 1) → ℂ) (B : ℝ),
      Integrable (fun ρ : ℝ => (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) *
        (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)) ∧
      ∫ ρ : ℝ, ‖(∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) *
          (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)‖ ≤
        C * (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) := by
  exact main n δ hz hA

end AbsoluteTate
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar"

namespace N8Assembly

open MeasureTheory NumberField LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR
open LanglandsTunnell.CubicInduction AssemblyBridges RadialTransport ColumnPolar

private noncomputable def arrayIntegrand (u₃ : ℂ) (a₃ : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ) (a : ℚ)
    (m : Matrix (Fin 3) (Fin 3) ℝ) (s : ℂ) (x : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 psiInf S (Matrix.of x) m * quasiChar (u₃ + 2) a₃ (Matrix.of x).det *
    (((|(Matrix.of x).det| ^ 2)⁻¹ : ℝ) : ℂ) * ZE (diagOne (a : ℝ) * (Matrix.of x)⁻¹) s

private noncomputable def chartData (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ) (a : ℚ)
    (r : (ℝ × ℝ) × ℝ) (s : ℂ) : ℂ :=
  quasiChar (u₃ + 2) a₃ (unitArray r.2 r.1).det * (((|(unitArray r.2 r.1).det| ^ 2)⁻¹ : ℝ) : ℂ) *
    (quasiChar t ē (a : ℝ))⁻¹ * ((|(a : ℝ)| : ℝ) : ℂ) ^ (1 - s) * ZE (unitArray r.2 r.1)⁻¹ s

private noncomputable def tateIntegrand {n : ℕ} (c : Fin (n + 1) → ℂ) (A' B' : ℝ) (δ : ℕ) (z : ℂ) (ρ : ℝ) : ℂ :=
  (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) * (Real.exp (-(Real.pi * (A' * ρ ^ 2 + 2 * B' * ρ))) : ℂ) *
    (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)

private theorem parity_le_one (b : ZMod 2) : parity b ≤ 1 := by
  unfold parity; split_ifs <;> omega

private theorem det_inv_ne_zero {x : Matrix (Fin 2) (Fin 2) ℝ} (hx : x.det ≠ 0) : x⁻¹.det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hx

private theorem ofReal_exp_profile (A' B' ρ : ℝ) :
    (Real.exp (-(Real.pi * (A' * ρ ^ 2 + 2 * B' * ρ))) : ℂ) =
      Complex.exp (-(Real.pi * ((A' : ℂ) * (ρ : ℂ) ^ 2 + 2 * (B' : ℂ) * (ρ : ℂ)))) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

private theorem jacobian_mul_arrayIntegrand_eq (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ)
    (hZE_transport : ∀ (g : Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ) (s : ℂ), A ≠ 0 → g.det ≠ 0 →
      ZE (diagOne A * g) s = (quasiChar t ē A)⁻¹ * ((|A| : ℝ) : ℂ) ^ (1 - s) * ZE g s)
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ) (a : ℚ) (ha : a ≠ 0)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (m : Matrix (Fin 3) (Fin 3) ℝ) {n : ℕ} (A' : ℝ) (c : Matrix (Fin 2) (Fin 2) ℝ → Fin (n + 1) → ℂ)
    (B' : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (hident : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 → ∀ ρ : ℝ, ρ ≠ 0 →
        ∫ v : Fin 2 → ℝ,
            (MvPolynomial.eval (fun ib : Fin 2 × Fin 3 =>
                ((((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])
                  ib.1 ib.2 : ℝ) : ℂ)) p *
              gaussian3 ((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])) *
            Complex.exp ((2 * Real.pi * Complex.I) * (((a : ℝ) * (-(v 1)) : ℝ) : ℂ)) =
          (((|ρ| : ℝ) : ℂ))⁻¹ * (∑ j : Fin (n + 1), c x j * (ρ : ℂ) ^ (j : ℕ)) *
            Complex.exp (-(Real.pi * ((A' : ℂ) * (ρ : ℂ) ^ 2 + 2 * (B' x : ℂ) * (ρ : ℂ)))))
    (r : (ℝ × ℝ) × ℝ) (hr : (unitArray r.2 r.1).det ≠ 0) {ρ : ℝ} (hρ : ρ ≠ 0) (s : ℂ) :
    |ρ| • arrayIntegrand u₃ a₃ ZE
        (fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M) psiInf a m s
        (polarArray (ρ, r.2) r.1) =
      chartData u₃ t a₃ ē ZE a r s *
        tateIntegrand (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (parity (a₃ + ē)) (s + u₃ + t) ρ := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have haρ : (a : ℝ) * ρ⁻¹ ≠ 0 := mul_ne_zero ha' (inv_ne_zero hρ)
  unfold arrayIntegrand chartData tateIntegrand
  rw [Complex.real_smul, of_polarArray, godementInner3_eq p psiInf a hpsiInf, hident _ (unitArray_slice _ _) hr ρ hρ,
    det_mul_diagOne, diagOne_mul_mul_diagOne_inv, hZE_transport _ _ _ haρ (det_inv_ne_zero hr),
    ← ofReal_exp_profile]
  · have hb := rho_bookkeeping u₃ t s a₃ ē (unitArray r.2 r.1).det (a : ℝ) hρ
    rw [quasiChar_eq_sign_pow_mul (s + u₃ + t - 1) (a₃ + ē) ρ] at hb
    linear_combination
      ((∑ j : Fin (n + 1), c (unitArray r.2 r.1) j * (ρ : ℂ) ^ (j : ℕ)) *
          (Real.exp (-(Real.pi * (A' * ρ ^ 2 + 2 * B' (unitArray r.2 r.1) * ρ))) : ℂ) *
          ZE (unitArray r.2 r.1)⁻¹ s) * hb
  · exact hρ

private theorem norm_quasiChar_off (u : ℂ) (b : ZMod 2) {y : ℝ} (hy : y ≠ 0) : ‖quasiChar u b y‖ = |y| ^ u.re := by
  rw [quasiChar_eq_sign_pow_mul, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hy)]
  rcases Real.sign_apply_eq_of_ne_zero y hy with hs | hs <;> simp [hs]

private theorem norm_quasiChar_le (u : ℂ) (b : ZMod 2) (y : ℝ) : ‖quasiChar u b y‖ ≤ |y| ^ u.re := by
  by_cases hy : y = 0
  · subst hy
    unfold quasiChar
    rw [norm_mul]
    have h1 : ‖(if b = 0 then (1 : ℂ) else ((SignType.sign (0 : ℝ) : ℝ) : ℂ))‖ ≤ 1 := by split_ifs <;> simp
    calc ‖((|(0 : ℝ)| : ℝ) : ℂ) ^ u‖ * ‖(if b = 0 then (1 : ℂ) else ((SignType.sign (0 : ℝ) : ℝ) : ℂ))‖
        ≤ ‖((|(0 : ℝ)| : ℝ) : ℂ) ^ u‖ * 1 := by gcongr
      _ = ‖((|(0 : ℝ)| : ℝ) : ℂ) ^ u‖ := mul_one _
      _ ≤ |(0 : ℝ)| ^ u.re := by
          simp only [abs_zero, Complex.ofReal_zero]
          by_cases hu : u = 0
          · simp [hu]
          · rw [Complex.zero_cpow hu]
            simp only [norm_zero]
            exact Real.rpow_nonneg le_rfl _
  · exact (norm_quasiChar_off u b hy).le

private theorem chartData_of_det_eq_zero (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ) (a : ℚ)
    {r : (ℝ × ℝ) × ℝ} (hr : (unitArray r.2 r.1).det = 0) (s : ℂ) : chartData u₃ t a₃ ē ZE a r s = 0 := by
  unfold chartData
  rw [hr]
  simp

private theorem continuousOn_quasiChar (u : ℂ) (b : ZMod 2) : ContinuousOn (quasiChar u b) {y : ℝ | y ≠ 0} := by
  intro y hy
  have hy' : y ≠ 0 := hy
  have hpos : 0 < |y| := abs_pos.mpr hy'
  have h1 : ContinuousAt (fun z : ℝ => ((|z| : ℝ) : ℂ) ^ u) y := by
    have hslit : ((|y| : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hpos
    have hc : Continuous (fun z : ℝ => ((|z| : ℝ) : ℂ)) := Complex.continuous_ofReal.comp continuous_abs
    exact ContinuousAt.comp (x := y) (continuousAt_cpow_const hslit) hc.continuousAt
  have h2 : ContinuousAt (fun z : ℝ => (if b = 0 then (1 : ℂ) else ((SignType.sign z : ℝ) : ℂ))) y := by
    split_ifs
    · exact continuousAt_const
    · rcases lt_or_gt_of_ne hy' with h | h
      · have : (fun z : ℝ => ((SignType.sign z : ℝ) : ℂ)) =ᶠ[nhds y] fun _ => ((SignType.sign y : ℝ) : ℂ) := by
          filter_upwards [Iio_mem_nhds h] with z hz
          rw [sign_neg (Set.mem_Iio.mp hz), sign_neg h]
        exact continuousAt_const.congr this.symm
      · have : (fun z : ℝ => ((SignType.sign z : ℝ) : ℂ)) =ᶠ[nhds y] fun _ => ((SignType.sign y : ℝ) : ℂ) := by
          filter_upwards [Ioi_mem_nhds h] with z hz
          rw [sign_pos (Set.mem_Ioi.mp hz), sign_pos h]
        exact continuousAt_const.congr this.symm
  exact (h1.mul h2).continuousWithinAt

private theorem unitArray_zero_one (θ : ℝ) (w : ℝ × ℝ) : unitArray θ w 0 1 = w.1 := rfl
private theorem unitArray_one_one (θ : ℝ) (w : ℝ × ℝ) : unitArray θ w 1 1 = w.2 := rfl

private theorem abs_rpow_one_sub_re_le {α : ℝ} (hα : 0 < α) (σ₁ σ₂ : ℝ) {s : ℂ} (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) :
    α ^ (1 - s).re ≤ Real.exp ((1 + |σ₁| + |σ₂|) * |Real.log α|) := by
  rw [Real.rpow_def_of_pos hα]
  apply Real.exp_le_exp.mpr
  have hre : |(1 - s).re| ≤ 1 + |σ₁| + |σ₂| := by
    rw [Complex.sub_re, Complex.one_re]
    have h3 : |s.re| ≤ |σ₁| + |σ₂| := by
      rw [abs_le]; constructor <;> [linarith [neg_abs_le σ₁, le_abs_self σ₂, abs_nonneg σ₂, abs_nonneg σ₁];
        linarith [le_abs_self σ₂, abs_nonneg σ₁]]
    calc |1 - s.re| ≤ |(1 : ℝ)| + |s.re| := abs_sub _ _
      _ ≤ 1 + (|σ₁| + |σ₂|) := by rw [abs_one]; linarith
      _ = 1 + |σ₁| + |σ₂| := by ring
  calc Real.log α * (1 - s).re ≤ |Real.log α * (1 - s).re| := le_abs_self _
    _ = |Real.log α| * |(1 - s).re| := abs_mul _ _
    _ ≤ |Real.log α| * (1 + |σ₁| + |σ₂|) := by gcongr
    _ = (1 + |σ₁| + |σ₂|) * |Real.log α| := mul_comm _ _

private theorem norm_chartData
    (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ) {a : ℚ} (ha' : (a : ℝ) ≠ 0)
    {r : (ℝ × ℝ) × ℝ} (hr : (unitArray r.2 r.1).det ≠ 0) (s : ℂ) :
    ‖chartData u₃ t a₃ ē ZE a r s‖ =
      |(unitArray r.2 r.1).det| ^ u₃.re * ‖(quasiChar t ē (a : ℝ))⁻¹‖ * |(a : ℝ)| ^ (1 - s).re *
        ‖ZE (unitArray r.2 r.1)⁻¹ s‖ := by
  have hdpos : 0 < |(unitArray r.2 r.1).det| := abs_pos.mpr hr
  have hapos : 0 < |(a : ℝ)| := abs_pos.mpr ha'
  unfold chartData
  have hinv0 : (0 : ℝ) ≤ (|(unitArray r.2 r.1).det| ^ 2)⁻¹ := by positivity
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_quasiChar_off _ _ hr, Complex.norm_cpow_eq_rpow_re_of_pos hapos,
    Complex.norm_real, Real.norm_of_nonneg hinv0]
  have h2 : |(unitArray r.2 r.1).det| ^ (u₃ + 2).re * (|(unitArray r.2 r.1).det| ^ 2)⁻¹ =
      |(unitArray r.2 r.1).det| ^ u₃.re := by
    have : (u₃ + 2).re = u₃.re + 2 := by simp
    rw [this, Real.rpow_add hdpos, Real.rpow_two]
    field_simp
  rw [h2]

private theorem chart_bound
    (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ) {a : ℚ} (ha' : (a : ℝ) ≠ 0)
    {n : ℕ} {A' : ℝ} (hA' : 0 < A') (c : Matrix (Fin 2) (Fin 2) ℝ → Fin (n + 1) → ℂ)
    (B' : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (E : (Fin (n + 1) → ℂ) → ℝ → ℝ → ℂ → ℂ) (σ₁ σ₂ : ℝ) (C₁ A₁ : ℝ) (N₁ : ℕ)
    (hZ : ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖ZE g s‖ ≤ C₁ * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N₁ * Real.exp (A₁ * |s.im|))
    (C₂ M₂ : ℝ) (N₂ : ℕ)
    (hE : ∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, σ₁ + (u₃ + t).re ≤ z.re → z.re ≤ σ₂ + (u₃ + t).re →
      ‖E c A B z‖ ≤ C₂ * (∑ j : Fin (n + 1), ‖c j‖) * max A A⁻¹ ^ N₂ * (1 + |B|) ^ N₂ *
        Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M₂ * |z.im|))
    (K κ₀ : ℝ) (N₀ : ℕ)
    (hbounds : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 →
      |B' x| ≤ K * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ∧
      ∀ j : Fin (n + 1), ‖c x j‖ * Real.exp (Real.pi * B' x ^ 2 / A') ≤
        K * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N₀ * Real.exp (-(κ₀ * (x 0 1 ^ 2 + x 1 1 ^ 2))) *
          Real.exp (-(κ₀ / x.det ^ 2)))
    (G : (ℝ × ℝ) × ℝ → ℝ)
    (hG : ∀ r : (ℝ × ℝ) × ℝ, (unitArray r.2 r.1).det ≠ 0 →
      (1 + (r.1.1 ^ 2 + r.1.2 ^ 2)) ^ (N₀ + N₂) * Real.exp (-(κ₀ * (r.1.1 ^ 2 + r.1.2 ^ 2))) *
          Real.exp (-(κ₀ / (unitArray r.2 r.1).det ^ 2)) *
        (1 + |(unitArray r.2 r.1)⁻¹ 0 0| + |(unitArray r.2 r.1)⁻¹ 0 1| + |(unitArray r.2 r.1)⁻¹ 1 0| +
            |(unitArray r.2 r.1)⁻¹ 1 1| + |((unitArray r.2 r.1)⁻¹).det|⁻¹) ^ N₁ *
        |(unitArray r.2 r.1).det| ^ u₃.re ≤ G r) :
    ∃ Cb Mb : ℝ, ∀ r : (ℝ × ℝ) × ℝ, (unitArray r.2 r.1).det ≠ 0 → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖chartData u₃ t a₃ ē ZE a r s * E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (s + u₃ + t)‖ ≤
        Cb * |G r| * Real.exp (Mb * |s.im|) := by
  set ca : ℝ := ‖(quasiChar t ē (a : ℝ))⁻¹‖ with hca
  set cb : ℝ := Real.exp ((1 + |σ₁| + |σ₂|) * |Real.log (abs (a : ℝ))|) with hcb
  set c0 : ℝ := Real.exp (|M₂| * |(u₃ + t).im|) with hc0
  refine ⟨ca * cb * |C₁| * |C₂| * ((n : ℝ) + 1) * |K| * max A' A'⁻¹ ^ N₂ * (1 + |K|) ^ N₂ * c0, A₁ + |M₂|, ?_⟩
  intro r hr s hs₁ hs₂
  set x₀ := unitArray r.2 r.1 with hx₀
  set Q : ℝ := r.1.1 ^ 2 + r.1.2 ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨hB, hc⟩ := hbounds x₀ (unitArray_slice _ _) hr
  simp only [hx₀, unitArray_zero_one, unitArray_one_one] at hB hc
  have hapos : 0 < |(a : ℝ)| := abs_pos.mpr ha'
  set br : ℝ := 1 + |x₀⁻¹ 0 0| + |x₀⁻¹ 0 1| + |x₀⁻¹ 1 0| + |x₀⁻¹ 1 1| + |x₀⁻¹.det|⁻¹ with hbr
  have hbr0 : 0 ≤ br := by positivity
  have hZE : ‖ZE x₀⁻¹ s‖ ≤ |C₁| * br ^ N₁ * Real.exp (A₁ * |s.im|) :=
    (hZ x₀⁻¹ (det_inv_ne_zero hr) s hs₁ hs₂).trans (by gcongr; exact le_abs_self C₁)
  have hdata : ‖chartData u₃ t a₃ ē ZE a r s‖ ≤
      |x₀.det| ^ u₃.re * ca * cb * (|C₁| * br ^ N₁ * Real.exp (A₁ * |s.im|)) := by
    rw [norm_chartData u₃ t a₃ ē ZE ha' hr s]
    have h1 := abs_rpow_one_sub_re_le hapos σ₁ σ₂ hs₁ hs₂
    gcongr
  have hz₁ : σ₁ + (u₃ + t).re ≤ (s + u₃ + t).re := by simp only [Complex.add_re]; linarith
  have hz₂ : (s + u₃ + t).re ≤ σ₂ + (u₃ + t).re := by simp only [Complex.add_re]; linarith
  have hexpz : Real.exp (M₂ * |(s + u₃ + t).im|) ≤ c0 * Real.exp (|M₂| * |s.im|) := by
    rw [hc0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have him : |(s + u₃ + t).im| ≤ |s.im| + |(u₃ + t).im| := by
      have : (s + u₃ + t).im = s.im + (u₃ + t).im := by simp only [Complex.add_im]; ring
      rw [this]; exact abs_add_le _ _
    calc M₂ * |(s + u₃ + t).im| ≤ |M₂| * |(s + u₃ + t).im| := by gcongr; exact le_abs_self M₂
      _ ≤ |M₂| * (|s.im| + |(u₃ + t).im|) := by gcongr
      _ = |M₂| * |(u₃ + t).im| + |M₂| * |s.im| := by ring
  have hBK : 1 + |B' x₀| ≤ (1 + |K|) * (1 + Q) := by
    have : |B' x₀| ≤ |K| * (1 + Q) := hB.trans (by gcongr; exact le_abs_self K)
    nlinarith [abs_nonneg K]
  have hsum : (∑ j : Fin (n + 1), ‖c x₀ j‖) * Real.exp (Real.pi * B' x₀ ^ 2 / A') ≤
      ((n : ℝ) + 1) * (|K| * (1 + Q) ^ N₀ * Real.exp (-(κ₀ * Q)) * Real.exp (-(κ₀ / x₀.det ^ 2))) := by
    rw [Finset.sum_mul]
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))), ‖c x₀ j‖ * Real.exp (Real.pi * B' x₀ ^ 2 / A') ≤
        |K| * (1 + Q) ^ N₀ * Real.exp (-(κ₀ * Q)) * Real.exp (-(κ₀ / x₀.det ^ 2)) := fun j _ =>
      (hc j).trans (by gcongr; exact le_abs_self K)
    calc ∑ j : Fin (n + 1), ‖c x₀ j‖ * Real.exp (Real.pi * B' x₀ ^ 2 / A')
        ≤ ∑ _j : Fin (n + 1), |K| * (1 + Q) ^ N₀ * Real.exp (-(κ₀ * Q)) * Real.exp (-(κ₀ / x₀.det ^ 2)) :=
          Finset.sum_le_sum hj
      _ = ((n : ℝ) + 1) * (|K| * (1 + Q) ^ N₀ * Real.exp (-(κ₀ * Q)) * Real.exp (-(κ₀ / x₀.det ^ 2))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hEb : ‖E (c x₀) A' (B' x₀) (s + u₃ + t)‖ ≤
      |C₂| * max A' A'⁻¹ ^ N₂ * ((1 + |K|) ^ N₂ * (1 + Q) ^ N₂) *
        (((n : ℝ) + 1) * (|K| * (1 + Q) ^ N₀ * Real.exp (-(κ₀ * Q)) * Real.exp (-(κ₀ / x₀.det ^ 2)))) *
        (c0 * Real.exp (|M₂| * |s.im|)) := by
    refine (hE (c x₀) A' (B' x₀) hA' (s + u₃ + t) hz₁ hz₂).trans ?_
    have hre : C₂ * (∑ j : Fin (n + 1), ‖c x₀ j‖) * max A' A'⁻¹ ^ N₂ * (1 + |B' x₀|) ^ N₂ *
        Real.exp (Real.pi * B' x₀ ^ 2 / A') * Real.exp (M₂ * |(s + u₃ + t).im|) =
        C₂ * max A' A'⁻¹ ^ N₂ * (1 + |B' x₀|) ^ N₂ *
          ((∑ j : Fin (n + 1), ‖c x₀ j‖) * Real.exp (Real.pi * B' x₀ ^ 2 / A')) *
          Real.exp (M₂ * |(s + u₃ + t).im|) := by ring
    rw [hre, ← mul_pow]
    have hmA : 0 ≤ max A' A'⁻¹ ^ N₂ := by positivity
    have hsum0 : 0 ≤ (∑ j : Fin (n + 1), ‖c x₀ j‖) * Real.exp (Real.pi * B' x₀ ^ 2 / A') := by positivity
    calc C₂ * max A' A'⁻¹ ^ N₂ * (1 + |B' x₀|) ^ N₂ *
          ((∑ j : Fin (n + 1), ‖c x₀ j‖) * Real.exp (Real.pi * B' x₀ ^ 2 / A')) * Real.exp (M₂ * |(s + u₃ + t).im|)
        ≤ |C₂| * max A' A'⁻¹ ^ N₂ * (1 + |B' x₀|) ^ N₂ *
          ((∑ j : Fin (n + 1), ‖c x₀ j‖) * Real.exp (Real.pi * B' x₀ ^ 2 / A')) *
            Real.exp (M₂ * |(s + u₃ + t).im|) := by
          gcongr
          exact le_abs_self C₂
      _ ≤ |C₂| * max A' A'⁻¹ ^ N₂ * ((1 + |K|) * (1 + Q)) ^ N₂ *
          (((n : ℝ) + 1) * (|K| * (1 + Q) ^ N₀ * Real.exp (-(κ₀ * Q)) * Real.exp (-(κ₀ / x₀.det ^ 2)))) *
            (c0 * Real.exp (|M₂| * |s.im|)) := by
          gcongr
  have hsplit : Real.exp ((A₁ + |M₂|) * |s.im|) = Real.exp (A₁ * |s.im|) * Real.exp (|M₂| * |s.im|) := by
    rw [add_mul, Real.exp_add]
  rw [norm_mul, hsplit]
  have hmaj := (hG r hr).trans (le_abs_self _)
  simp only [hx₀] at hmaj ⊢
  calc ‖chartData u₃ t a₃ ē ZE a r s‖ * ‖E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (s + u₃ + t)‖
      ≤ (|(unitArray r.2 r.1).det| ^ u₃.re * ca * cb * (|C₁| * br ^ N₁ * Real.exp (A₁ * |s.im|))) *
        (|C₂| * max A' A'⁻¹ ^ N₂ * ((1 + |K|) ^ N₂ * (1 + Q) ^ N₂) *
          (((n : ℝ) + 1) * (|K| * (1 + Q) ^ N₀ * Real.exp (-(κ₀ * Q)) *
            Real.exp (-(κ₀ / (unitArray r.2 r.1).det ^ 2)))) * (c0 * Real.exp (|M₂| * |s.im|))) :=
        mul_le_mul hdata hEb (norm_nonneg _) (by positivity)
    _ = (ca * cb * |C₁| * |C₂| * ((n : ℝ) + 1) * |K| * max A' A'⁻¹ ^ N₂ * (1 + |K|) ^ N₂ * c0) *
        ((1 + Q) ^ (N₀ + N₂) * Real.exp (-(κ₀ * Q)) * Real.exp (-(κ₀ / (unitArray r.2 r.1).det ^ 2)) * br ^ N₁ *
          |(unitArray r.2 r.1).det| ^ u₃.re) * (Real.exp (A₁ * |s.im|) * Real.exp (|M₂| * |s.im|)) := by
        rw [pow_add]; ring
    _ ≤ (ca * cb * |C₁| * |C₂| * ((n : ℝ) + 1) * |K| * max A' A'⁻¹ ^ N₂ * (1 + |K|) ^ N₂ * c0) * |G r| *
        (Real.exp (A₁ * |s.im|) * Real.exp (|M₂| * |s.im|)) := by
        gcongr

private theorem continuousOn_inv_unitArray :
    ContinuousOn (fun r : (ℝ × ℝ) × ℝ => (unitArray r.2 r.1)⁻¹) {r | (unitArray r.2 r.1).det ≠ 0} := by
  have hdet : Continuous (fun r : (ℝ × ℝ) × ℝ => (unitArray r.2 r.1).det) := continuous_unitArray.matrix_det
  have hadj : Continuous (fun r : (ℝ × ℝ) × ℝ => (unitArray r.2 r.1).adjugate) := continuous_unitArray.matrix_adjugate
  have h1 : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => ((unitArray r.2 r.1).det)⁻¹ • (unitArray r.2 r.1).adjugate)
      {r | (unitArray r.2 r.1).det ≠ 0} :=
    (hdet.continuousOn.inv₀ fun r hr => hr).smul hadj.continuousOn
  refine h1.congr fun r hr => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

private theorem continuousOn_chartIntegrand (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ)
    (hZE_cont : ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => ZE (Matrix.of M) s) {M | (Matrix.of M).det ≠ 0})
    (a : ℚ) {n : ℕ} {A' : ℝ} (hA' : 0 < A') {c : Matrix (Fin 2) (Fin 2) ℝ → Fin (n + 1) → ℂ}
    {B' : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hc_cont : ContinuousOn c {x | x.det ≠ 0})
    (hB'_cont : ContinuousOn B' {x | x.det ≠ 0}) (E : (Fin (n + 1) → ℂ) → ℝ → ℝ → ℂ → ℂ)
    (hE_cont : ∀ z : ℂ, ContinuousOn (fun p : (Fin (n + 1) → ℂ) × ℝ × ℝ => E p.1 p.2.1 p.2.2 z)
      {p : (Fin (n + 1) → ℂ) × ℝ × ℝ | 0 < p.2.1}) (s : ℂ) :
    ContinuousOn (fun r : (ℝ × ℝ) × ℝ =>
        chartData u₃ t a₃ ē ZE a r s * E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (s + u₃ + t))
      {r | (unitArray r.2 r.1).det ≠ 0} := by
  set U : Set ((ℝ × ℝ) × ℝ) := {r | (unitArray r.2 r.1).det ≠ 0} with hU
  have hdet : Continuous (fun r : (ℝ × ℝ) × ℝ => (unitArray r.2 r.1).det) := continuous_unitArray.matrix_det
  have hqc : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => quasiChar (u₃ + 2) a₃ (unitArray r.2 r.1).det) U :=
    (continuousOn_quasiChar _ _).comp hdet.continuousOn fun r hr => hr
  have hinv2 : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => (((|(unitArray r.2 r.1).det| ^ 2)⁻¹ : ℝ) : ℂ)) U := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact ((continuous_abs.comp hdet).pow 2).continuousOn.inv₀ fun r hr => by
      have : (unitArray r.2 r.1).det ≠ 0 := hr
      exact pow_ne_zero 2 (abs_ne_zero.mpr this)
  have hof : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, Matrix.of M = M := fun M => by ext i j; rfl
  have hZEc : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => ZE (unitArray r.2 r.1)⁻¹ s) U := by
    have hmaps : ∀ r ∈ U, (unitArray r.2 r.1)⁻¹ ∈ {M : Fin 2 → Fin 2 → ℝ | (Matrix.of M).det ≠ 0} := by
      intro r hr
      simp only [hof]
      exact det_inv_ne_zero hr
    have := (hZE_cont s).comp continuousOn_inv_unitArray hmaps
    refine this.congr fun r _ => ?_
    simp only [Function.comp_apply, hof]
  have hcU : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => c (unitArray r.2 r.1)) U :=
    hc_cont.comp continuous_unitArray.continuousOn fun r hr => hr
  have hBU : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => B' (unitArray r.2 r.1)) U :=
    hB'_cont.comp continuous_unitArray.continuousOn fun r hr => hr
  have hEc : ContinuousOn
      (fun r : (ℝ × ℝ) × ℝ => E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (s + u₃ + t)) U := by
    have := (hE_cont (s + u₃ + t)).comp (hcU.prodMk (continuousOn_const.prodMk hBU))
      (fun r _ => show (0 : ℝ) < A' from hA')
    exact this
  unfold chartData
  exact ((((hqc.mul hinv2).mul continuousOn_const).mul continuousOn_const).mul hZEc).mul hEc

private theorem ae_ne_zero_volume : ∀ᵐ ρ : ℝ ∂volume, ρ ≠ 0 := by
  rw [ae_iff]
  have : {a : ℝ | ¬ a ≠ 0} = {0} := by ext a; simp
  rw [this, Real.volume_singleton]

private scoped instance sfinite_chartMeasure : SFinite ChartMajorant.chartMeasure := by
  unfold ChartMajorant.chartMeasure; infer_instance

private theorem continuousOn_abs_cpow_const_off (w : ℂ) :
    ContinuousOn (fun ρ : ℝ => ((|ρ| : ℝ) : ℂ) ^ w) {ρ : ℝ | ρ ≠ 0} := by
  intro y hy
  have hpos : 0 < |y| := abs_pos.mpr hy
  have hslit : ((|y| : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hpos
  have hc : Continuous (fun z : ℝ => ((|z| : ℝ) : ℂ)) := Complex.continuous_ofReal.comp continuous_abs
  exact (ContinuousAt.comp (x := y) (continuousAt_cpow_const hslit) hc.continuousAt).continuousWithinAt

private theorem continuousOn_sign_cast_off : ContinuousOn (fun ρ : ℝ => ((Real.sign ρ : ℝ) : ℂ)) {ρ : ℝ | ρ ≠ 0} := by
  intro y hy
  have hy' : y ≠ 0 := hy
  rcases lt_or_gt_of_ne hy' with h | h
  · have : (fun ρ : ℝ => ((Real.sign ρ : ℝ) : ℂ)) =ᶠ[nhds y] fun _ => ((Real.sign y : ℝ) : ℂ) := by
      filter_upwards [Iio_mem_nhds h] with z hz
      rw [Real.sign_of_neg (Set.mem_Iio.mp hz), Real.sign_of_neg h]
    exact (continuousAt_const.congr this.symm).continuousWithinAt
  · have : (fun ρ : ℝ => ((Real.sign ρ : ℝ) : ℂ)) =ᶠ[nhds y] fun _ => ((Real.sign y : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      rw [Real.sign_of_pos (Set.mem_Ioi.mp hz), Real.sign_of_pos h]
    exact (continuousAt_const.congr this.symm).continuousWithinAt

private theorem continuousOn_chartData (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ)
    (hZE_cont : ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => ZE (Matrix.of M) s) {M | (Matrix.of M).det ≠ 0})
    (a : ℚ) (s : ℂ) :
    ContinuousOn (fun r : (ℝ × ℝ) × ℝ => chartData u₃ t a₃ ē ZE a r s) {r | (unitArray r.2 r.1).det ≠ 0} := by
  set U : Set ((ℝ × ℝ) × ℝ) := {r | (unitArray r.2 r.1).det ≠ 0} with hU
  have hdet : Continuous (fun r : (ℝ × ℝ) × ℝ => (unitArray r.2 r.1).det) := continuous_unitArray.matrix_det
  have hqc : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => quasiChar (u₃ + 2) a₃ (unitArray r.2 r.1).det) U :=
    (continuousOn_quasiChar _ _).comp hdet.continuousOn fun r hr => hr
  have hinv2 : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => (((|(unitArray r.2 r.1).det| ^ 2)⁻¹ : ℝ) : ℂ)) U := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact ((continuous_abs.comp hdet).pow 2).continuousOn.inv₀ fun r hr => by
      have : (unitArray r.2 r.1).det ≠ 0 := hr
      exact pow_ne_zero 2 (abs_ne_zero.mpr this)
  have hof : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, Matrix.of M = M := fun M => by ext i j; rfl
  have hZEc : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => ZE (unitArray r.2 r.1)⁻¹ s) U := by
    have hmaps : ∀ r ∈ U, (unitArray r.2 r.1)⁻¹ ∈ {M : Fin 2 → Fin 2 → ℝ | (Matrix.of M).det ≠ 0} := by
      intro r hr
      simp only [hof]
      exact det_inv_ne_zero hr
    have := (hZE_cont s).comp continuousOn_inv_unitArray hmaps
    refine this.congr fun r _ => ?_
    simp only [Function.comp_apply, hof]
  unfold chartData
  exact (((hqc.mul hinv2).mul continuousOn_const).mul continuousOn_const).mul hZEc

private theorem aestronglyMeasurable_chartData (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ)
    (hZE_cont : ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => ZE (Matrix.of M) s) {M | (Matrix.of M).det ≠ 0})
    (a : ℚ) (s : ℂ) :
    AEStronglyMeasurable (fun r : (ℝ × ℝ) × ℝ => chartData u₃ t a₃ ē ZE a r s) ChartMajorant.chartMeasure := by
  set U : Set ((ℝ × ℝ) × ℝ) := {r | (unitArray r.2 r.1).det ≠ 0} with hU
  have hU_meas : MeasurableSet U :=
    (isOpen_ne_fun continuous_unitArray.matrix_det continuous_const).measurableSet
  have hind : (fun r : (ℝ × ℝ) × ℝ => chartData u₃ t a₃ ē ZE a r s) =
      U.indicator (fun r => chartData u₃ t a₃ ē ZE a r s) := by
    funext r
    rw [Set.indicator_apply]
    split_ifs with hr
    · rfl
    · exact chartData_of_det_eq_zero u₃ t a₃ ē ZE a (not_not.mp hr) s
  rw [hind]
  exact (aestronglyMeasurable_indicator_iff hU_meas).2
    ((continuousOn_chartData u₃ t a₃ ē ZE hZE_cont a s).aestronglyMeasurable hU_meas)

private theorem continuousOn_tateIntegrand_prod {n : ℕ} (A' : ℝ) {c : Matrix (Fin 2) (Fin 2) ℝ → Fin (n + 1) → ℂ}
    {B' : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hc_cont : ContinuousOn c {x | x.det ≠ 0})
    (hB'_cont : ContinuousOn B' {x | x.det ≠ 0}) (δ : ℕ) (z : ℂ) :
    ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
        tateIntegrand (c (unitArray q.1.2 q.1.1)) A' (B' (unitArray q.1.2 q.1.1)) δ z q.2)
      ({r : (ℝ × ℝ) × ℝ | (unitArray r.2 r.1).det ≠ 0} ×ˢ {ρ : ℝ | ρ ≠ 0}) := by
  set S := ({r : (ℝ × ℝ) × ℝ | (unitArray r.2 r.1).det ≠ 0} ×ˢ {ρ : ℝ | ρ ≠ 0}) with hS
  have hx : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => unitArray q.1.2 q.1.1) S :=
    (continuous_unitArray.comp continuous_fst).continuousOn
  have hcq : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => c (unitArray q.1.2 q.1.1)) S :=
    hc_cont.comp hx fun q hq => hq.1
  have hBq : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => B' (unitArray q.1.2 q.1.1)) S :=
    hB'_cont.comp hx fun q hq => hq.1
  have hρ : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => (q.2 : ℂ)) S :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  have hsum : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      ∑ j : Fin (n + 1), c (unitArray q.1.2 q.1.1) j * (q.2 : ℂ) ^ (j : ℕ)) S := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact (((continuous_apply j).comp_continuousOn hcq)).mul (hρ.pow _)
  have hexp : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      (Real.exp (-(Real.pi * (A' * q.2 ^ 2 + 2 * B' (unitArray q.1.2 q.1.1) * q.2))) : ℂ)) S := by
    refine Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn ?_)
    have h2 : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => q.2) S := continuous_snd.continuousOn
    exact (continuousOn_const.mul ((continuousOn_const.mul (h2.pow 2)).add ((continuousOn_const.mul hBq).mul h2))).neg
  have hsgn : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => ((Real.sign q.2 : ℝ) : ℂ) ^ δ) S :=
    (continuousOn_sign_cast_off.comp continuous_snd.continuousOn fun q hq => hq.2).pow δ
  have hcpow : ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => ((|q.2| : ℝ) : ℂ) ^ (z - 1)) S :=
    (continuousOn_abs_cpow_const_off (z - 1)).comp continuous_snd.continuousOn fun q hq => hq.2
  unfold tateIntegrand
  exact ((hsum.mul hexp).mul hsgn).mul hcpow

private theorem identity_at (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ)
    (hZE_bound : ∀ σ₁ σ₂ : ℝ, ∃ (C A : ℝ) (N : ℕ), ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖ZE g s‖ ≤ C * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N * Real.exp (A * |s.im|))
    (hZE_cont : ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => ZE (Matrix.of M) s) {M | (Matrix.of M).det ≠ 0})
    (hZE_transport : ∀ (g : Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ) (s : ℂ), A ≠ 0 → g.det ≠ 0 →
      ZE (diagOne A * g) s = (quasiChar t ē A)⁻¹ * ((|A| : ℝ) : ℂ) ^ (1 - s) * ZE g s)
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ) (a : ℚ) (ha : a ≠ 0)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (m : Matrix (Fin 3) (Fin 3) ℝ) (κ : ℝ) {n : ℕ} {A' : ℝ} (hA' : 0 < A')
    (c : Matrix (Fin 2) (Fin 2) ℝ → Fin (n + 1) → ℂ) (B' : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (hc_cont : ContinuousOn c {x | x.det ≠ 0}) (hB'_cont : ContinuousOn B' {x | x.det ≠ 0})
    (hident :
      (∀ x : Matrix (Fin 2) (Fin 2) ℝ, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 → ∀ ρ : ℝ, ρ ≠ 0 →
        ∫ v : Fin 2 → ℝ,
            (MvPolynomial.eval (fun ib : Fin 2 × Fin 3 =>
                ((((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])
                  ib.1 ib.2 : ℝ) : ℂ)) p *
              gaussian3 ((x * diagOne ρ) * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b])) *
            Complex.exp ((2 * Real.pi * Complex.I) * ((a * (-(v 1)) : ℝ) : ℂ)) =
          (((|ρ| : ℝ) : ℂ))⁻¹ * (∑ j : Fin (n + 1), c x j * (ρ : ℂ) ^ (j : ℕ)) *
            Complex.exp (-(Real.pi * ((A' : ℂ) * (ρ : ℂ) ^ 2 + 2 * (B' x : ℂ) * (ρ : ℂ))))))
    (K κ₀ : ℝ) (N₀ : ℕ) (hκ₀ : 0 < κ₀)
    (hbounds :
        ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x 0 0 ^ 2 + x 1 0 ^ 2 = 1 → x.det ≠ 0 →
          |B' x| ≤ K * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ∧
          ∀ j : Fin (n + 1),
            ‖c x j‖ * Real.exp (Real.pi * B' x ^ 2 / A') ≤
              K * (1 + (x 0 1 ^ 2 + x 1 1 ^ 2)) ^ N₀ * Real.exp (-(κ₀ * (x 0 1 ^ 2 + x 1 1 ^ 2))) *
                Real.exp (-(κ₀ / x.det ^ 2)))
    (E : (Fin (n + 1) → ℂ) → ℝ → ℝ → ℂ → ℂ)
    (hE_ident :
      (∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, 0 < z.re →
        ∫ ρ : ℝ, (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) *
            (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) * (Real.sign ρ : ℂ) ^ parity (a₃ + ē) *
            ((|ρ| : ℝ) : ℂ) ^ (z - 1) =
          Complex.Gammaℝ (z + parity (a₃ + ē)) * E c A B z))
    (s : ℂ) (hs : 0 < (s + u₃ + t).re) :
    (κ : ℂ) * (quasiChar (u₃ + 1) a₃ m.det * ∫ x : Fin 2 → Fin 2 → ℝ,
        arrayIntegrand u₃ a₃ ZE
          (fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M)
          psiInf a m s x) =
      Complex.Gammaℝ (s + (u₃ + t + signShift (a₃ + ē))) *
        ((κ : ℂ) * quasiChar (u₃ + 1) a₃ m.det *
          ∫ r : (ℝ × ℝ) × ℝ, chartData u₃ t a₃ ē ZE a r s *
            E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (s + u₃ + t) ∂ChartMajorant.chartMeasure) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  set z : ℂ := s + u₃ + t with hz
  set δ : ℕ := parity (a₃ + ē) with hδ
  set f : (Fin 2 → Fin 2 → ℝ) → ℂ := arrayIntegrand u₃ a₃ ZE
    (fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M) psiInf a m s with hf
  set μ : Measure ((ℝ × ℝ) × ℝ) := ChartMajorant.chartMeasure with hμ
  have hμ' : μ = (volume : Measure (ℝ × ℝ)).prod ((volume : Measure ℝ).restrict (Set.Ioo 0 Real.pi)) := rfl
  set U : Set ((ℝ × ℝ) × ℝ) := {r | (unitArray r.2 r.1).det ≠ 0} with hU
  have hU_open : IsOpen U := isOpen_ne_fun continuous_unitArray.matrix_det continuous_const
  set S : Set (((ℝ × ℝ) × ℝ) × ℝ) := U ×ˢ {ρ : ℝ | ρ ≠ 0} with hS
  have hS_meas : MeasurableSet S := hU_open.measurableSet.prod isOpen_ne.measurableSet
  have hae_U : ∀ᵐ r ∂μ, r ∈ U := ChartMajorant.ae_det_unitArray_ne_zero
  have hae_S : ∀ᵐ q ∂(μ.prod volume), q ∈ S := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem hS_meas]
    filter_upwards [hae_U] with r hr
    filter_upwards [ae_ne_zero_volume] with ρ hρ
    exact ⟨hr, hρ⟩
  obtain ⟨Ca, Na, habs⟩ := AbsoluteTate.integrable_and_integral_norm_le n δ hs hA'
  set H : ((ℝ × ℝ) × ℝ) × ℝ → ℂ := fun q =>
    chartData u₃ t a₃ ē ZE a q.1 s * tateIntegrand (c (unitArray q.1.2 q.1.1)) A' (B' (unitArray q.1.2 q.1.1)) δ z q.2
    with hH
  have hH_cont : ContinuousOn H S :=
    ((continuousOn_chartData u₃ t a₃ ē ZE hZE_cont a s).comp continuous_fst.continuousOn fun q hq => hq.1).mul
      (continuousOn_tateIntegrand_prod A' hc_cont hB'_cont δ z)
  have hH_meas : AEStronglyMeasurable H (μ.prod volume) := by
    have := hH_cont.aestronglyMeasurable (μ := μ.prod volume) hS_meas
    rwa [Measure.restrict_eq_self_of_ae_mem hae_S] at this
  have hpt : ∀ q : ((ℝ × ℝ) × ℝ) × ℝ, q ∈ S → |q.2| • f (polarArray (q.2, q.1.2) q.1.1) = H q := fun q hq =>
    jacobian_mul_arrayIntegrand_eq u₃ t a₃ ē ZE hZE_transport p psiInf a ha hpsiInf m A' c B' hident q.1 hq.1 hq.2 s
  have hH_int : Integrable H (μ.prod volume) := by
    rw [integrable_prod_iff hH_meas]
    refine ⟨ae_of_all _ fun r => ?_, ?_⟩
    · show Integrable (fun ρ : ℝ => chartData u₃ t a₃ ē ZE a r s *
        tateIntegrand (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) δ z ρ) volume
      exact ((habs (c (unitArray r.2 r.1)) (B' (unitArray r.2 r.1))).1.const_mul _)
    ·
      set Ef : (Fin (n + 1) → ℂ) → ℝ → ℝ → ℂ → ℂ := fun c A B _ =>
        ((|Ca| * (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ Na * Real.exp (Real.pi * B ^ 2 / A) : ℝ) : ℂ) with hEf
      obtain ⟨C₁, A₁, N₁, hZ⟩ := hZE_bound s.re s.re
      have hEfb : ∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, s.re + (u₃ + t).re ≤ z.re →
          z.re ≤ s.re + (u₃ + t).re →
          ‖Ef c A B z‖ ≤ |Ca| * (∑ j : Fin (n + 1), ‖c j‖) * max A A⁻¹ ^ Na * (1 + |B|) ^ Na *
            Real.exp (Real.pi * B ^ 2 / A) * Real.exp (0 * |z.im|) := by
        intro c A B hA z _ _
        have hmax : (1 : ℝ) ≤ max A A⁻¹ := by
          rcases le_or_gt 1 A with h | h
          · exact le_max_of_le_left h
          · exact le_max_of_le_right ((one_le_inv₀ hA).mpr h.le)
        have h1 : (1 : ℝ) ≤ max A A⁻¹ ^ Na := one_le_pow₀ hmax
        have h0 : (0 : ℝ) ≤ |Ca| * (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ Na * Real.exp (Real.pi * B ^ 2 / A) := by
          positivity
        simp only [hEf, zero_mul, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_of_nonneg h0]
        calc |Ca| * (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ Na * Real.exp (Real.pi * B ^ 2 / A)
            = |Ca| * (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ Na * Real.exp (Real.pi * B ^ 2 / A) * 1 :=
              (mul_one _).symm
          _ ≤ |Ca| * (∑ j : Fin (n + 1), ‖c j‖) * (1 + |B|) ^ Na * Real.exp (Real.pi * B ^ 2 / A) *
              max A A⁻¹ ^ Na := by
              gcongr
          _ = |Ca| * (∑ j : Fin (n + 1), ‖c j‖) * max A A⁻¹ ^ Na * (1 + |B|) ^ Na *
              Real.exp (Real.pi * B ^ 2 / A) := by ring
      obtain ⟨G, hG_int, hG⟩ := ChartMajorant.exists_integrable_majorant hκ₀ (N₀ + Na) N₁ u₃.re
      obtain ⟨Cb, Mb, hCb⟩ :=
        chart_bound u₃ t a₃ ē ZE ha' hA' c B' Ef s.re s.re C₁ A₁ N₁ hZ |Ca| 0 Na hEfb K κ₀ N₀ hbounds G hG
      have hnorm_eq : ∀ r : (ℝ × ℝ) × ℝ, ∫ ρ : ℝ, ‖H (r, ρ)‖ =
          ‖chartData u₃ t a₃ ē ZE a r s‖ *
            ∫ ρ : ℝ, ‖tateIntegrand (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) δ z ρ‖ := by
        intro r
        simp only [hH, norm_mul]
        exact integral_const_mul _ _
      refine Integrable.mono' ((hG_int.abs.const_mul |Cb|).mul_const (Real.exp (Mb * |s.im|)))
        hH_meas.norm.integral_prod_right' (ae_of_all _ fun r => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnorm_eq r]
      by_cases hr : (unitArray r.2 r.1).det ≠ 0
      · have h2 := (habs (c (unitArray r.2 r.1)) (B' (unitArray r.2 r.1))).2
        have h3 : ‖chartData u₃ t a₃ ē ZE a r s‖ *
            ∫ ρ : ℝ, ‖tateIntegrand (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) δ z ρ‖ ≤
            ‖chartData u₃ t a₃ ē ZE a r s * Ef (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) s‖ := by
          rw [norm_mul]
          gcongr
          have h0 : (0 : ℝ) ≤ |Ca| * (∑ j : Fin (n + 1), ‖c (unitArray r.2 r.1) j‖) *
              (1 + |B' (unitArray r.2 r.1)|) ^ Na * Real.exp (Real.pi * B' (unitArray r.2 r.1) ^ 2 / A') := by
            positivity
          simp only [hEf, Complex.norm_real, Real.norm_of_nonneg h0]
          unfold tateIntegrand
          refine h2.trans ?_
          gcongr
          exact le_abs_self Ca
        refine h3.trans ((hCb r hr s le_rfl le_rfl).trans ?_)
        gcongr
        exact le_abs_self Cb
      · have hr' : (unitArray r.2 r.1).det = 0 := not_not.mp hr
        rw [chartData_of_det_eq_zero u₃ t a₃ ē ZE a hr' s, norm_zero, zero_mul]
        positivity
  have hg_int : Integrable (fun q : ((ℝ × ℝ) × ℝ) × ℝ => |q.2| • f (polarArray (q.2, q.1.2) q.1.1)) (μ.prod volume) :=
    hH_int.congr (by filter_upwards [hae_S] with q hq using (hpt q hq).symm)
  have hf_int : Integrable f := by
    rw [ColumnPolar.integrable_iff_integrable_polarArray_prod f]
    exact hg_int
  have hdock : ∫ x, f x = ∫ r : (ℝ × ℝ) × ℝ, (∫ ρ : ℝ, |ρ| • f (polarArray (ρ, r.2) r.1)) ∂μ :=
    ColumnPolar.integral_eq_integral_prod_integral_polarArray f hf_int
  have hinner : ∀ r : (ℝ × ℝ) × ℝ, (unitArray r.2 r.1).det ≠ 0 →
      ∫ ρ : ℝ, |ρ| • f (polarArray (ρ, r.2) r.1) =
        Complex.Gammaℝ (z + δ) *
          (chartData u₃ t a₃ ē ZE a r s * E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) z) := by
    intro r hr
    have h1 : (fun ρ : ℝ => |ρ| • f (polarArray (ρ, r.2) r.1)) =ᵐ[volume] fun ρ =>
        chartData u₃ t a₃ ē ZE a r s * tateIntegrand (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) δ z ρ := by
      filter_upwards [ae_ne_zero_volume] with ρ hρ
      exact hpt (r, ρ) ⟨hr, hρ⟩
    have h2 : ∫ ρ : ℝ, chartData u₃ t a₃ ē ZE a r s *
        tateIntegrand (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) δ z ρ =
        chartData u₃ t a₃ ē ZE a r s *
          ∫ ρ : ℝ, tateIntegrand (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) δ z ρ :=
      integral_const_mul _ _
    have h3 := hE_ident (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) hA' z hs
    rw [integral_congr_ae h1, h2]
    unfold tateIntegrand
    rw [h3]
    ring
  have hinner_ae : (fun r : (ℝ × ℝ) × ℝ => ∫ ρ : ℝ, |ρ| • f (polarArray (ρ, r.2) r.1)) =ᵐ[μ] fun r =>
      Complex.Gammaℝ (z + δ) *
        (chartData u₃ t a₃ ē ZE a r s * E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) z) := by
    filter_upwards [hae_U] with r hr using hinner r hr
  have hΓ : (z + (δ : ℂ)) = s + (u₃ + t + signShift (a₃ + ē)) := by
    rw [hz, hδ, parity_cast]; ring
  have h4 : ∫ r : (ℝ × ℝ) × ℝ, Complex.Gammaℝ (z + δ) *
      (chartData u₃ t a₃ ē ZE a r s * E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) z) ∂μ =
      Complex.Gammaℝ (z + δ) * ∫ r : (ℝ × ℝ) × ℝ,
        chartData u₃ t a₃ ē ZE a r s * E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) z ∂μ :=
    integral_const_mul _ _
  rw [hdock, integral_congr_ae hinner_ae, h4, hΓ]
  ring

private theorem core (u₃ t : ℂ) (a₃ ē : ZMod 2) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ → ℂ)
    (hZE_entire : ∀ g : Matrix (Fin 2) (Fin 2) ℝ, Differentiable ℂ (ZE g))
    (hZE_bound : ∀ σ₁ σ₂ : ℝ, ∃ (C A : ℝ) (N : ℕ), ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖ZE g s‖ ≤ C * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N * Real.exp (A * |s.im|))
    (hZE_cont : ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => ZE (Matrix.of M) s) {M | (Matrix.of M).det ≠ 0})
    (hZE_transport : ∀ (g : Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ) (s : ℂ), A ≠ 0 → g.det ≠ 0 →
      ZE (diagOne A * g) s = (quasiChar t ē A)⁻¹ * ((|A| : ℝ) : ℂ) ^ (1 - s) * ZE g s)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) (κ : ℝ) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
      ∀ s : ℂ, 0 < (s + u₃ + t).re →
        (κ : ℂ) * (quasiChar (u₃ + 1) a₃ m.det * ∫ x : Fin 2 → Fin 2 → ℝ, arrayIntegrand u₃ a₃ ZE S psiInf a m s x) =
          Complex.Gammaℝ (s + (u₃ + t + signShift (a₃ + ē))) * P s := by
  obtain ⟨p, rfl⟩ := hS
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  obtain ⟨n, A', c, B', hA', hc_cont, hB'_cont, hident, K, κ₀, N₀, hκ₀, hbounds⟩ :=
    RadialProfile.exists_radial_profile p m hm (a : ℝ) ha'
  obtain ⟨E, hE_ent, hE_ident, hE_bound, hE_cont⟩ :=
    exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul n (parity (a₃ + ē)) (parity_le_one _)
  set F : (ℝ × ℝ) × ℝ → ℂ → ℂ := fun r s =>
    chartData u₃ t a₃ ē ZE a r s * E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (s + u₃ + t) with hF
  set U : Set ((ℝ × ℝ) × ℝ) := {r | (unitArray r.2 r.1).det ≠ 0} with hU
  have hU_meas : MeasurableSet U :=
    (isOpen_ne_fun continuous_unitArray.matrix_det continuous_const).measurableSet
  have hF_zero : ∀ r, r ∉ U → ∀ s, F r s = 0 := by
    intro r hr s
    have hr' : (unitArray r.2 r.1).det = 0 := not_not.mp hr
    simp only [hF, chartData_of_det_eq_zero u₃ t a₃ ē ZE a hr', zero_mul]
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun r => F r s) ChartMajorant.chartMeasure := by
    intro s
    have hind : (fun r => F r s) = U.indicator (fun r => F r s) := by
      funext r
      rw [Set.indicator_apply]
      split_ifs with hr
      · rfl
      · exact hF_zero r hr s
    rw [hind]
    exact (aestronglyMeasurable_indicator_iff hU_meas).2
      ((continuousOn_chartIntegrand u₃ t a₃ ē ZE hZE_cont a hA' hc_cont hB'_cont E hE_cont s).aestronglyMeasurable
        hU_meas)
  have hent : ∀ᵐ r ∂ChartMajorant.chartMeasure, Differentiable ℂ (F r) := by
    refine ae_of_all _ fun r => ?_
    have hb : ((|(a : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr ha')
    have hcpow : Differentiable ℂ (fun s : ℂ => ((|(a : ℝ)| : ℝ) : ℂ) ^ (1 - s)) :=
      ((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow (Or.inl hb)
    have hEd : Differentiable ℂ
        (fun s : ℂ => E (c (unitArray r.2 r.1)) A' (B' (unitArray r.2 r.1)) (s + u₃ + t)) :=
      (hE_ent _ _ _).comp ((differentiable_id.add_const u₃).add_const t)
    simp only [hF]
    unfold chartData
    exact (((((differentiable_const _).mul (differentiable_const _)).mul (differentiable_const _)).mul hcpow).mul
      (hZE_entire _)).mul hEd
  have hdom : ∀ σ₁ σ₂ : ℝ, ∃ g : (ℝ × ℝ) × ℝ → ℝ, Integrable g ChartMajorant.chartMeasure ∧ ∃ M : ℝ,
      ∀ᵐ r ∂ChartMajorant.chartMeasure, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖F r s‖ ≤ g r * Real.exp (M * |s.im|) := by
    intro σ₁ σ₂
    obtain ⟨C₁, A₁, N₁, hZ⟩ := hZE_bound σ₁ σ₂
    obtain ⟨C₂, M₂, N₂, hE⟩ := hE_bound (σ₁ + (u₃ + t).re) (σ₂ + (u₃ + t).re)
    obtain ⟨G, hG_int, hG⟩ := ChartMajorant.exists_integrable_majorant hκ₀ (N₀ + N₂) N₁ u₃.re
    obtain ⟨Cb, Mb, hCb⟩ :=
      chart_bound u₃ t a₃ ē ZE ha' hA' c B' E σ₁ σ₂ C₁ A₁ N₁ hZ C₂ M₂ N₂ hE K κ₀ N₀ hbounds G hG
    refine ⟨fun r => |Cb| * |G r|, (hG_int.abs.const_mul |Cb|), Mb, ae_of_all _ fun r s hs₁ hs₂ => ?_⟩
    by_cases hr : (unitArray r.2 r.1).det ≠ 0
    · calc ‖F r s‖ ≤ Cb * |G r| * Real.exp (Mb * |s.im|) := hCb r hr s hs₁ hs₂
        _ ≤ |Cb| * |G r| * Real.exp (Mb * |s.im|) := by
          gcongr
          exact le_abs_self Cb
    · rw [hF_zero r hr s, norm_zero]
      positivity
  obtain ⟨hdiff, hstrip⟩ :=
    StripHolomorphy.differentiable_integral_and_strip_bound (μ := ChartMajorant.chartMeasure) F hmeas hent hdom
  refine ⟨fun s => (κ : ℂ) * quasiChar (u₃ + 1) a₃ m.det * ∫ r, F r s ∂ChartMajorant.chartMeasure, ?_, ?_, ?_⟩
  · exact (differentiable_const _).mul hdiff
  · intro σ₁ σ₂
    obtain ⟨C, A, hCA⟩ := hstrip σ₁ σ₂
    refine ⟨‖(κ : ℂ) * quasiChar (u₃ + 1) a₃ m.det‖ * C, A, fun s hs₁ hs₂ => ?_⟩
    rw [norm_mul, mul_assoc]
    gcongr
    exact hCA s hs₁ hs₂
  · intro s hs
    exact identity_at u₃ t a₃ ē ZE hZE_bound hZE_cont hZE_transport p psiInf a ha hpsiInf m κ hA' c B' hc_cont
      hB'_cont hident K κ₀ N₀ hκ₀ hbounds E hE_ident s hs

end N8Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.N8Assembly"

section MainTheorem

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

private theorem det_realMat_ne_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (StandardKernel.realMat g).det ≠ 0 := by
  have hu : IsUnit (StandardKernel.realMat g) := (StandardKernel.realGL g).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

open LanglandsTunnell.CubicInduction in
open NumberField AutomorphicForm LanglandsTunnell.Converse in

theorem solution
    (u₃ : ℂ) (a₃ : ZMod 2)
    (P₂ : RealArchParam)
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (κ : ℝ)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℂ) (e : ℤ) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
      ∀ s : ℂ, max c₀ (-(u₃).re) - t.re < s.re → D.zeta_abscissa < s.re + t.re →
        (κ : ℂ) *
          (ArchR.quasiChar (u₃ + 1) a₃ (StandardKernel.realMat gInf).det *
            ∫ x : Fin 2 → Fin 2 → ℝ,
              godementInner3 psiInf S (Matrix.of x) (StandardKernel.realMat gInf) *
                ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of x).det *
                  (((|(Matrix.of x).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                D.zetaEntire (ArchR.diagOne (a : ℝ) * (Matrix.of x)⁻¹) t (e : ZMod 2) s) =
          Complex.Gammaℝ (s + (u₃ + t + LanglandsTunnell.signShift (a₃ + (e : ZMod 2)))) * P s := by
  have _hc₀ := hc₀
  obtain ⟨hbnd, hcont⟩ := D.exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn t (e : ZMod 2)
  have hcont' : ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => D.zetaEntire (Matrix.of M) t (e : ZMod 2) s)
      {M | (Matrix.of M).det ≠ 0} := fun s => hcont s
  obtain ⟨P, h1, h2, h3⟩ := N8Assembly.core u₃ t a₃ (e : ZMod 2) (fun g s => D.zetaEntire g t (e : ZMod 2) s)
    (fun g => D.zetaEntire_differentiable g t (e : ZMod 2)) hbnd hcont'
    (fun g A s hA hg => D.zetaEntire_diagOne_mul g A t (e : ZMod 2) s hA hg) S hS a ha psiInf hpsiInf
    (StandardKernel.realMat gInf) (det_realMat_ne_zero gInf) κ
  refine ⟨P, h1, h2, fun s hs₁ _ => ?_⟩
  have hs : 0 < (s + u₃ + t).re := by
    have hmax := le_max_right c₀ (-(u₃).re)
    simp only [Complex.add_re]
    linarith
  have := h3 s hs
  unfold N8Assembly.arrayIntegrand at this
  exact this

end MainTheorem
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.ColumnPolar P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.N8Assembly"

end S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul (solution)
