-- Prove2me | solution 1 for OAI.InvariantIsing.tensor_envelope_pressure_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:14:07.063629+00:00
-- url     : https://prove2.me/submissions/7aff8908-30ab-4c6d-b0a3-befbe1c26123

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_tensorNamespacedMeanPressure_perturbation_cost

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434
/-- Mathlib d13f23b's `ProbabilityTheory.hasLaw_map` (InvariantIsing, q258). -/
theorem _root_.ProbabilityTheory.hasLaw_map {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {P : MeasureTheory.Measure Ω} {X : Ω → 𝓧} (hX : AEMeasurable X P) :
    ProbabilityTheory.HasLaw X (P.map X) P where
  aemeasurable := hX
  map_eq := rfl

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PoissonCloud
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson Cloud. -/

noncomputable section



 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

 
namespace IsingPerceptron

lemma poisson_probability_generating (r : ℝ≥0) (q : ℝ) :
    (∫ n : ℕ, q ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (q - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) * q^n) =
        Real.exp (-(r : ℝ)) * ∑' n : ℕ, ((r : ℝ)*q)^n / (n.factorial : ℝ) := by
      rw [← tsum_mul_left]
      congr 1
      ext n
      rw [mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*q) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*q)).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = Real.exp ((r : ℝ)*(q-1)) := by rw [← Real.exp_add]; congr 1; ring

variable {E : Type*} [MeasurableSpace E]

lemma measurable_cloudSum {ψ : E → ℝ} (hψ : Measurable ψ) :
    Measurable (cloudSum ψ) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun y : ℕ → E => ∑ i : Fin n, ψ (y i))
  exact Finset.measurable_sum (Finset.univ : Finset (Fin n))
    (fun i _ => hψ.comp (measurable_pi_apply (i : ℕ)))

lemma iid_finite_laplace (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (n : ℕ) :
    (∫ ω : ℕ → E, Real.exp (-(∑ i : Fin n, ψ (ω i)))
      ∂Measure.infinitePi (fun _ : ℕ => μ)) =
    (∫ x, Real.exp (-ψ x) ∂μ)^n := by
  let X : ℕ → (ℕ → E) → ℝ := fun i ω => Real.exp (-ψ (ω i))
  have hind : iIndepFun X (Measure.infinitePi (fun _ : ℕ => μ)) :=
    iIndepFun_infinitePi (fun _ => hψ.neg.exp)
  have hind' : iIndepFun (fun i : Fin n => X i) (Measure.infinitePi (fun _ : ℕ => μ)) :=
    hind.precomp Fin.val_injective
  have hm (i : Fin n) : AEStronglyMeasurable (X i)
      (Measure.infinitePi (fun _ : ℕ => μ)) :=
    ((hψ.neg.exp).comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable
  have he i : (∫ ω, X i ω ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫ x, Real.exp (-ψ x) ∂μ := by
    have mp := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
    exact mp.hasLaw.integral_comp hψ.neg.exp.aestronglyMeasurable
  have hh := hind'.integral_fun_prod_eq_prod_integral hm
  simpa only [X, ← Real.exp_sum, ← Finset.sum_neg_distrib, he, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hh

 
theorem finitePoissonCloud_laplace (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, Real.exp (-cloudSum ψ p) ∂finitePoissonCloud r μ) =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-ψ x) ∂μ) - 1)) := by
  have hi : Integrable (fun p => Real.exp (-cloudSum ψ p)) (finitePoissonCloud r μ) := by
    apply Integrable.of_bound (measurable_cloudSum hψ |>.neg.exp.aestronglyMeasurable) 1
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => hpos _))
  rw [finitePoissonCloud, integral_prod _ hi]
  simp_rw [cloudSum, iid_finite_laplace μ hψ]
  exact poisson_probability_generating r _

lemma negExp_injective : Function.Injective negExp := by
  intro x y h
  apply EReal.coe_ennreal_injective
  apply neg_injective
  apply EReal.exp_strictMono.injective
  exact (ENNReal.toReal_eq_toReal_iff' (enegExp_ne_top x) (enegExp_ne_top y)).mp h
lemma negExp_ofReal {x : ℝ} (hx : 0 ≤ x) :
    negExp (ENNReal.ofReal x) = Real.exp (-x) := by
  simp [negExp, enegExp, EReal.coe_ennreal_ofReal, max_eq_left hx,
    ← EReal.coe_neg, Real.exp_nonneg]
lemma enegExp_add (x y : ℝ≥0∞) : enegExp (x+y) = enegExp x * enegExp y := by
  by_cases hx : x = ∞
  · simp [hx]
  by_cases hy : y = ∞
  · simp [hy]
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy]
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  simp only [enegExp, EReal.coe_ennreal_ofReal]
  rw [max_eq_left (by positivity), max_eq_left (by positivity), max_eq_left (by positivity)]
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_neg, EReal.exp_coe,
    EReal.exp_coe, EReal.exp_coe, neg_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
lemma negExp_add (x y : ℝ≥0∞) : negExp (x+y) = negExp x * negExp y := by
  simp only [negExp, enegExp_add, ENNReal.toReal_mul]
lemma negExp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    negExp (∑ i ∈ s, f i) = ∏ i ∈ s, negExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, negExp_add, ih]
lemma negExp_nat_mul (n : ℕ) (x : ℝ≥0∞) : negExp (n*x) = negExp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, negExp_add, ih, pow_succ]


lemma finiteCloudMeasure_lintegral (p : ℕ × (ℕ → E)) {ψ : E → ℝ≥0∞}
    (hψ : Measurable ψ) : (∫⁻ x, ψ x ∂finiteCloudMeasure p) = ∑ i : Fin p.1, ψ (p.2 i) := by
  simp [finiteCloudMeasure, lintegral_finsetSum_measure, lintegral_dirac' _ hψ]

variable [Nonempty E]


lemma finiteMeasure_mass_normalize (μ : FiniteMeasure E) :
    (μ : Measure E) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure E) := by
  ext s hs
  simpa using congrArg (fun m : FiniteMeasure E => (m : Measure E) s)
    μ.self_eq_mass_smul_normalize

lemma finitePoissonLaw_laplace (μ : FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂finitePoissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E)) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) (μ.normalize : Measure E) := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) (μ.normalize : Measure E) :=
    (integrable_const 1).sub hi
  have hmeas : Measurable (fun ν : Measure E => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [finitePoissonLaw, integral_map measurable_finiteCloudMeasure.aemeasurable
    hmeas.aestronglyMeasurable]
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace μ.mass _ hψ hpos]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost)]
  rw [smul_eq_mul, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul μ.mass.coe_nonneg,
    negExp_ofReal (mul_nonneg μ.mass.coe_nonneg (integral_nonneg hcost))]
  rw [integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring


omit [Nonempty E] in
lemma laplace_partial_tendsto (P : Measure (ℕ → Measure E)) [IsFiniteMeasure P]
    {a : Measure E → ℝ≥0∞} (ha : Measurable a) :
    Tendsto (fun n => ∫ ω, negExp (∑ i : Fin n, a (ω i)) ∂P)
      atTop (𝓝 (∫ ω, negExp (∑' i, a (ω i)) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    have hm : Measurable (fun ω : ℕ → Measure E => ∑ i : Fin n, a (ω i)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => ha.comp (measurable_pi_apply (i : ℕ)))
    exact (continuous_negExp.measurable.comp hm).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
      exact negExp_le_one _
  · exact ae_of_all _ fun ω => by
      simp_rw [Fin.sum_univ_eq_sum_range (fun i => a (ω i))]
      exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)

lemma poissonProductLaw_laplace_partial (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i) ∂poissonProductLaw μ) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂sfiniteSeq μ i) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind : iIndepFun (fun i (ω : ℕ → Measure E) => negExp (a (ω i))) (poissonProductLaw μ) :=
    iIndepFun_infinitePi (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂poissonProductLaw μ) =
        negExp (∫⁻ x, c x ∂sfiniteSeq μ i) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂poissonComponentLaw μ i :=
        (measurePreserving_eval_infinitePi (poissonComponentLaw μ) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace ⟨sfiniteSeq μ i, inferInstance⟩ hψ hpos
  simpa only [negExp_sum, hei] using hh

 

theorem poissonLaw_laplace (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂poissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂μ) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto (poissonProductLaw μ) ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂sfiniteSeq μ i))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂μ))) := by
    have hsum : (∑' i, ∫⁻ x, c x ∂sfiniteSeq μ i) = ∫⁻ x, c x ∂μ := by
      rw [← lintegral_sum_measure, sum_sfiniteSeq]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂sfiniteSeq μ i)]
    rw [← hsum]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw, integral_map measurable_measureSum.aemeasurable
    heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂poissonProductLaw μ) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a, poissonProductLaw_laplace_partial μ hψ hpos] using hlim) hr


lemma laplace_finite_coordinates_unique {ι : Type*} [Fintype ι]
    (P Q : Measure (ι → ℝ≥0∞)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ k : ι → ℕ,
      (∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂P) =
      ∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂Q) : P = Q := by
  classical
  let g : ι → ((ι → ℝ≥0∞) →ᵇ ℝ) := fun i =>
    negExpBCF.compContinuous ⟨fun x => x i, continuous_apply i⟩
  let ev : MvPolynomial ι ℝ →ₐ[ℝ] ((ι → ℝ≥0∞) →ᵇ ℝ) := MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((ι → ℝ≥0∞) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : ι) (x : ι → ℝ≥0∞) : g i x = negExp (x i) := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by contrapose! hxy; exact funext hxy
    refine ⟨g i, ?_, ?_⟩
    · refine ⟨(g i).toContinuousMap, ?_, rfl⟩
      exact ⟨g i, ⟨MvPolynomial.X i, by simp [ev]⟩, rfl⟩
    · simpa only [hap] using
        (fun h => hi (negExp_injective h))
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k r =>
    have hev (x : ι → ℝ≥0∞) : ev (MvPolynomial.monomial k r) x =
        r * negExp (∑ i, (k i : ℝ≥0∞) * x i) := by
      simp only [ev, MvPolynomial.aeval_monomial]
      rw [negExp_sum]
      simp only [negExp_nat_mul]
      simp [Finsupp.prod_fintype, hap]
    change (∫ x, ev (MvPolynomial.monomial k r) x ∂P) =
      ∫ x, ev (MvPolynomial.monomial k r) x ∂Q
    simp only [hev, integral_const_mul]
    exact congrArg (r * ·) (h fun i => k i)

lemma measure_eq_of_map_eq_comap {E F : Type*} [mE : MeasurableSpace E]
    [mF : MeasurableSpace F] {f : E → F}
    (hf : mE = mF.comap f) {P Q : Measure E} (h : P.map f = Q.map f) : P = Q := by
  have hfm : Measurable f := measurable_iff_comap_le.mpr hf.ge
  ext s hs
  rw [hf] at hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  exact (Measure.map_apply hfm ht).symm.trans ((congrArg (fun μ : Measure F => μ t) h).trans
    (Measure.map_apply hfm ht))

omit [Nonempty E] in
lemma measurable_measureCoordinates : Measurable (measureCoordinates (E := E)) :=
  Measurable.of_eval fun coordinate => Measure.measurable_coe coordinate.2

omit [Nonempty E] in
lemma measureSpace_eq_comap_coordinates :
    (inferInstance : MeasurableSpace (Measure E)) =
      MeasurableSpace.comap measureCoordinates (inferInstance : MeasurableSpace
        ({s : Set E // MeasurableSet s} → ℝ≥0∞)) := by
  apply le_antisymm
  · let m := MeasurableSpace.comap (measureCoordinates (E := E)) inferInstance
    have hc : @Measurable (Measure E) _ m _ measureCoordinates :=
      measurable_iff_comap_le.mpr le_rfl
    have hi : @Measurable (Measure E) (Measure E) m Measure.instMeasurableSpace id := by
      apply @Measure.measurable_of_measurable_coe E (Measure E) _ m id
      intro s hs
      change @Measurable (Measure E) ℝ≥0∞ m _
        (fun ν => measureCoordinates ν ⟨s, hs⟩)
      exact (measurable_pi_apply ⟨s, hs⟩).comp hc
    simpa only [MeasurableSpace.comap_id] using hi.comap_le
  · exact measurable_measureCoordinates.comap_le

omit [Nonempty E] in
 
theorem randomMeasure_laplace_unique (P Q : Measure (Measure E))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ ψ : E → ℝ, Measurable ψ → (∀ x, 0 ≤ ψ x) →
      (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂P) =
      ∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂Q) : P = Q := by
  classical
  apply measure_eq_of_map_eq_comap measureSpace_eq_comap_coordinates
  apply IsProjectiveLimit.unique (P := fun I =>
    (P.map measureCoordinates).map I.restrict) (fun _ => rfl)
  intro I
  change (Q.map measureCoordinates).map I.restrict = (P.map measureCoordinates).map I.restrict
  rw [Measure.map_map I.measurable_restrict
      measurable_measureCoordinates,
    Measure.map_map I.measurable_restrict
      measurable_measureCoordinates]
  let e : Measure E → (I → ℝ≥0∞) := fun ν i => ν i.1.1
  have he : Measurable e := Measurable.of_eval fun coordinate =>
    Measure.measurable_coe coordinate.1.2
  change Q.map e = P.map e
  apply laplace_finite_coordinates_unique
  intro k
  let ψ : E → ℝ := fun x => ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x
  have hposi (i : I) (x : E) : 0 ≤ i.1.1.indicator (fun _ => (k i : ℝ)) x := by
    apply indicator_nonneg
    intro _ _
    positivity
  have hpos (x : E) : 0 ≤ ψ x := Finset.sum_nonneg (fun i _ => hposi i x)
  have hm : Measurable ψ := Finset.measurable_sum _ (fun i _ =>
    measurable_const.indicator i.1.2)
  have hoint (ν : Measure E) :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) = ∑ i : I, (k i : ℝ≥0∞) * e ν i := by
    have ho (x : E) : ENNReal.ofReal (ψ x) =
        ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ≥0∞)) x := by
      change ENNReal.ofReal (∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x) = _
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hposi i x)]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x ∈ i.1.1 <;> simp [hx]
    simp_rw [ho]
    rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator i.1.2)]
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_indicator i.1.2, lintegral_const, Measure.restrict_apply_univ]
  have hcm : Measurable (fun x : I → ℝ≥0∞ => negExp (∑ i, (k i : ℝ≥0∞) * x i)) :=
    continuous_negExp.measurable.comp (Finset.measurable_sum _
      (fun i _ => measurable_const.mul (measurable_pi_apply i)))
  rw [integral_map he.aemeasurable hcm.aestronglyMeasurable,
    integral_map he.aemeasurable hcm.aestronglyMeasurable]
  simpa only [hoint] using (h ψ hm hpos).symm

end IsingPerceptron

 
namespace IsingPerceptron

 

theorem poissonLaw_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : Measure E) [SFinite μ] {T : E → F}
    (hT : Measurable T) [SFinite (μ.map T)] :
    (poissonLaw μ).map (fun ν => ν.map T) = poissonLaw (μ.map T) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun ν : Measure F => negExp (∫⁻ y, ENNReal.ofReal (ψ y) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map (Measure.measurable_map T hT).aemeasurable hm.aestronglyMeasurable]
  simp_rw [lintegral_map hψ.ennreal_ofReal hT]
  rw [poissonLaw_laplace μ (ψ := fun x => ψ (T x)) (hψ.comp hT) (fun x => hpos (T x)),
    poissonLaw_laplace (μ.map T) hψ hpos,
    lintegral_map (by fun_prop) hT]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_LabeledSampling
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled Sampling. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
open Function

lemma measurable_lintegral_pointwiseFinite {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a,b) ∂κ a) := by
  classical
  let F : ℕ → SimpleFunc (A × B) ℝ≥0∞ := SimpleFunc.eapprox f
  have h : ∀ a b, ⨆ n, F n (a,b) = f (a,b) :=
    fun a b => SimpleFunc.iSup_eapprox_apply hf (a,b)
  simp_rw [← h]
  have he (a : A) : (∫⁻ b, ⨆ n, F n (a,b) ∂κ a) =
      ⨆ n, ∫⁻ b, F n (a,b) ∂κ a := by
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [he]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction (motive := fun g =>
    Measurable (fun a => ∫⁻ b, g (a,b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    have hi (a : A) : (∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a) =
        c * κ a (Prod.mk a ⁻¹' t) := by
      simp_rw [← indicator_comp_right (Prod.mk a)]
      rw [lintegral_indicator (ht.preimage measurable_prodMk_left)]
      simp only [Function.comp_apply, lintegral_const, Measure.restrict_apply_univ]
    change Measurable (fun a => ∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a)
    simp_rw [hi]
    exact measurable_const.mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ)
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have ha (a : A) : (∫⁻ b, g₁ (a,b) + g₂ (a,b) ∂κ a) =
        (∫⁻ b, g₁ (a,b) ∂κ a) + ∫⁻ b, g₂ (a,b) ∂κ a :=
      lintegral_add_left (g₁.measurable.comp measurable_prodMk_left) _
    simp_rw [ha]
    exact hm₁.add hm₂


lemma finitePartKernel_finite {E : Type*} [MeasurableSpace E] (ν : Measure E) :
    IsFiniteMeasure (finitePartKernel ν) := by
  by_cases h : ν univ < ∞
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_left h]
    exact ⟨h⟩
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_right h]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma measurable_finitePart_lintegral {E : Type*} [MeasurableSpace E]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun ν : Measure E => ∫⁻ x, F (x,ν) ∂finitePartKernel ν) :=
  measurable_lintegral_pointwiseFinite finitePartKernel finitePartKernel_finite
    (hF.comp measurable_swap)

lemma infinitePi_indep_eval_rest {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    IndepFun (fun ω : ι → E => ω i)
      (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j) (Measure.infinitePi P) := by
  let m : ι → MeasurableSpace (ι → E) := fun j =>
    MeasurableSpace.comap (fun ω => ω j) inferInstance
  have hi : iIndep m (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint (m := m) (fun j => (measurable_pi_apply j).comap_le) hi
    (S := {i}) (T := {j | j ≠ i}) (by simp)
  change Indep (MeasurableSpace.comap (fun ω : ι → E => ω i) inferInstance)
    (MeasurableSpace.comap (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j)
      inferInstance) (Measure.infinitePi P)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_ofPred_eq, m] using h

lemma infinitePi_eval_rest_map {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    (Measure.infinitePi P).map (fun ω : ι → E =>
      (ω i, fun j : {j : ι // j ≠ i} => ω j)) =
      (P i).prod (Measure.infinitePi (fun j : {j : ι // j ≠ i} => P j)) := by
  have hmap := IndepFun.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    (Measurable.of_eval fun j : {j : ι // j ≠ i} =>
      measurable_pi_apply (j : ι)).aemeasurable (infinitePi_indep_eval_rest P i)
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective] at hmap
  exact hmap

lemma measureSum_eq_eval_add_rest {E : Type*} [MeasurableSpace E]
    (ω : ℕ → Measure E) (i : ℕ) :
    Measure.sum ω = ω i + Measure.sum (fun j : {j : ℕ // j ≠ i} => ω j) := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.add_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite i]
  congr 1
  trans ∑' j : ℕ, {j : ℕ | j ≠ i}.indicator (fun j => ω j s) j
  · apply tsum_congr
    intro j
    by_cases h : j = i <;> simp [h]
  · exact (tsum_subtype {j : ℕ | j ≠ i} (fun j => ω j s)).symm

variable {E : Type*} [MeasurableSpace E]

lemma measurable_atomCloud (n : ℕ) : Measurable (atomCloud (E := E) (n := n)) := by
  exact Finset.measurable_sum _ (fun i _ => Measure.measurable_dirac.comp
    (measurable_pi_apply i))

lemma atomCloud_insertNth {n : ℕ} (i : Fin (n+1)) (x : E) (ω : Fin n → E) :
    atomCloud (i.insertNth x ω) = Measure.dirac x + atomCloud ω := by
  classical
  rw [atomCloud, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

lemma atomCloud_lintegral {n : ℕ} (ω : Fin n → E) {f : E → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ x, f x ∂atomCloud ω) = ∑ i, f (ω i) := by
  simp [atomCloud, lintegral_finsetSum_measure, lintegral_dirac' _ hf]

lemma iid_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (i : Fin (n+1)) :
    (∫⁻ ω : Fin (n+1) → E, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  have hm : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
    |>.lintegral_comp (hF.comp ((measurable_pi_apply i).prodMk
      (measurable_atomCloud (n+1))))
  simp only [Function.comp_apply] at h
  have he (p : E × (Fin n → E)) :
      F (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p) i,
        atomCloud ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p)) =
      F (p.1, Measure.dirac p.1 + atomCloud p.2) := by
    change F ((i.insertNth (α := fun _ => E) p.1 p.2) i,
      atomCloud (i.insertNth (α := fun _ => E) p.1 p.2)) = _
    rw [Fin.insertNth_apply_same, atomCloud_insertNth]
  simp_rw [he] at h
  exact h.symm.trans (lintegral_prod _ hm.aemeasurable)

lemma iid_sum_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) :
    (∫⁻ ω : Fin (n+1) → E, ∑ i, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      (n+1 : ℝ≥0∞) * ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [lintegral_finsetSum Finset.univ (f := fun i (ω : Fin (n+1) → E) => F (ω i, atomCloud ω)) (fun i _ =>
    (hF.comp ((measurable_pi_apply i).prodMk (measurable_atomCloud (n+1)))))]
  simp only [iid_point_insertion μ hF n, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma poissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℝ≥0∞) = r * poissonWeight r n := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
  have he : (Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)) * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [poissonWeight, ENNReal.ofReal_mul (by positivity :
      0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)),
    ENNReal.ofReal_add (by positivity : 0 ≤ (n : ℝ)) (by positivity : 0 ≤ (1 : ℝ)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using hh

lemma iid_restrict_lintegral (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ)
    {H : (Fin n → E) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ ω : ℕ → E, H (fun i => ω i) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H ω ∂Measure.pi (fun _ => μ) := by
  have hp : MeasurePreserving (fun ω : ℕ → E => fun i : Fin n => ω i)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
    refine ⟨Measurable.of_eval fun index => measurable_pi_apply (index : ℕ), ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  exact hp.lintegral_comp hH

lemma lintegral_finitePoissonCloud (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {H : Measure E → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H (finiteCloudMeasure p) ∂finitePoissonCloud r μ) =
      ∑' n, poissonWeight r n * ∫⁻ ω : Fin n → E, H (atomCloud ω)
        ∂Measure.pi (fun _ => μ) := by
  rw [finitePoissonCloud, lintegral_prod (fun p => H (finiteCloudMeasure p)) (hH.comp measurable_finiteCloudMeasure).aemeasurable]
  have hi (n : ℕ) :
      (∫⁻ ω : ℕ → E, H (finiteCloudMeasure (n, ω))
        ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H (atomCloud ω) ∂Measure.pi (fun _ => μ) :=
    iid_restrict_lintegral μ n (hH.comp (measurable_atomCloud n))
  simp_rw [hi]
  rw [poissonMeasure, lintegral_sum_measure]
  simp [lintegral_smul_measure, poissonWeight, smul_eq_mul, lintegral_dirac]

 

theorem finitePoissonCloud_insertion (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F)
    :
    (∫⁻ p, ∫⁻ x, F (x, finiteCloudMeasure p) ∂finitePartKernel (finiteCloudMeasure p)
      ∂finitePoissonCloud r μ) =
      r * ∫⁻ x, ∫⁻ p, F (x, Measure.dirac x + finiteCloudMeasure p)
        ∂finitePoissonCloud r μ ∂μ := by
  rw [lintegral_finitePoissonCloud r μ (measurable_finitePart_lintegral hF)]
  have hm (x : E) : Measurable (fun ν : Measure E => F (x, Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  simp_rw [lintegral_finitePoissonCloud r μ (hm _)]
  have hi (n : ℕ) (ω : Fin n → E) : (∫⁻ x, F (x, atomCloud ω) ∂finitePartKernel (atomCloud ω)) =
      ∑ i, F (ω i, atomCloud ω) := by
    have hfin : IsFiniteMeasure (atomCloud ω) := by unfold atomCloud; infer_instance
    have he : finitePartKernel (atomCloud ω) = atomCloud ω :=
      ite_eq_left (measure_lt_top _ _)
    rw [he]
    exact atomCloud_lintegral ω (hF.comp (measurable_id.prodMk measurable_const))
  simp_rw [hi]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero, lintegral_zero, mul_zero, zero_add]
  simp_rw [iid_sum_point_insertion μ hF, ← mul_assoc, poissonWeight_succ]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmj (n : ℕ) : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have hmi (n : ℕ) : Measurable (fun x => ∫⁻ ω : Fin n → E,
      F (x, Measure.dirac x + atomCloud ω) ∂Measure.pi (fun _ => μ)) :=
    (hmj n).lintegral_prod_right
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    rw [lintegral_const_mul _ (hmi n)]
  · intro n
    exact (measurable_const.mul (hmi n)).aemeasurable

lemma measurable_measureSum_countable {ι : Type*} [Countable ι] :
    Measurable (Measure.sum : (ι → Measure E) → Measure E) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

lemma measurable_finitePart_param {A : Type*} [MeasurableSpace A]
    {N : A → Measure E} (hN : Measurable N) {F : A × E → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂finitePartKernel (N a)) := by
  let κ : Kernel A E := ⟨fun a => finitePartKernel (N a),
    finitePartKernel.measurable.comp hN⟩
  exact measurable_lintegral_pointwiseFinite κ
    (fun a => finitePartKernel_finite (N a)) hF

variable [Nonempty E]

lemma finitePoissonLaw_finite (μ : FiniteMeasure E) :
    ∀ᵐ ν ∂finitePoissonLaw μ, ν univ < ∞ := by
  rw [finitePoissonLaw, ae_map_iff measurable_finiteCloudMeasure.aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)]
  exact ae_of_all _ fun p => by
    have : IsFiniteMeasure (finiteCloudMeasure p) := by
      unfold finiteCloudMeasure
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    exact measure_lt_top _ _

lemma finitePoissonLaw_insertion (μ : FiniteMeasure E)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ν, ∫⁻ x, F (x,ν) ∂finitePartKernel ν ∂finitePoissonLaw μ) =
      ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν) ∂finitePoissonLaw μ ∂(μ : Measure E) := by
  have hm (x : E) : Measurable (fun ν : Measure E => F (x,Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  rw [finitePoissonLaw, lintegral_map (measurable_finitePart_lintegral hF)
    measurable_finiteCloudMeasure]
  simp_rw [lintegral_map (hm _) measurable_finiteCloudMeasure]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure, smul_eq_mul]
  exact finitePoissonCloud_insertion μ.mass _ hF

 
lemma poissonComponent_insertion (μ : Measure E) [SFinite μ] (i : ℕ)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂finitePartKernel (ω i)
      ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂sfiniteSeq μ i := by
  let R := {j : ℕ // j ≠ i}
  let P := poissonComponentLaw μ
  let rest : (R → Measure E) → Measure E := Measure.sum
  have hrest : Measurable rest := measurable_measureSum_countable
  let joint := fun ω : ℕ → Measure E => (ω i, fun j : R => ω j)
  have hjoint : Measurable joint := (measurable_pi_apply i).prodMk
    (Measurable.of_eval fun index : R => measurable_pi_apply (index : ℕ))
  have hjlaw : (poissonProductLaw μ).map joint =
      (P i).prod (Measure.infinitePi (fun j : R => P j)) :=
    infinitePi_eval_rest_map P i
  have hI : Measurable (fun p : Measure E × (R → Measure E) =>
      ∫⁻ x, F (x,p.1 + rest p.2) ∂finitePartKernel p.1) := by
    apply measurable_finitePart_param measurable_fst (F := fun p => F (p.2,p.1.1 + rest p.1.2))
    exact hF.comp (measurable_snd.prodMk
      ((measurable_fst.comp measurable_fst).add
        (hrest.comp (measurable_snd.comp measurable_fst))))
  have hR (x : E) : Measurable (fun p : Measure E × (R → Measure E) =>
      F (x,Measure.dirac x + (p.1 + rest p.2))) :=
    hF.comp (measurable_const.prodMk (measurable_const.add
      (measurable_fst.add (hrest.comp measurable_snd))))
  have he (ω : ℕ → Measure E) : Measure.sum ω = (joint ω).1 + rest (joint ω).2 :=
    measureSum_eq_eval_add_rest ω i
  simp_rw [he]
  rw [← lintegral_map hI hjoint, hjlaw,
    lintegral_prod_symm _ hI.aemeasurable]
  simp_rw [← lintegral_map (hR _) hjoint, hjlaw]
  have hFp (ω : R → Measure E) : Measurable (fun p : E × Measure E =>
      F (p.1,p.2 + rest ω)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  have hins (ω : R → Measure E) :
      (∫⁻ ν, ∫⁻ x, F (x,ν + rest ω) ∂finitePartKernel ν ∂P i) =
        ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν + rest ω) ∂P i ∂sfiniteSeq μ i :=
    finitePoissonLaw_insertion ⟨sfiniteSeq μ i, inferInstance⟩ (hFp ω)
  simp_rw [hins]
  have hJ : Measurable (fun p : (R → Measure E) × E =>
      ∫⁻ ν, F (p.2,Measure.dirac p.2 + ν + rest p.1) ∂P i) := by
    have hm : Measurable (fun p : ((R → Measure E) × E) × Measure E =>
        F (p.1.2,Measure.dirac p.1.2 + p.2 + rest p.1.1)) :=
      hF.comp ((measurable_snd.comp measurable_fst).prodMk
        (((Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst)).add
          measurable_snd).add (hrest.comp (measurable_fst.comp measurable_fst))))
    exact hm.lintegral_prod_right
  rw [lintegral_lintegral_swap hJ.aemeasurable]
  congr 1
  funext x
  rw [lintegral_prod_symm _ (hR x).aemeasurable]
  simp only [add_assoc]

lemma poissonProductLaw_finite (μ : Measure E) [SFinite μ] :
    ∀ᵐ ω ∂poissonProductLaw μ, ∀ i, ω i univ < ∞ := by
  rw [ae_all_iff]
  intro i
  have h := finitePoissonLaw_finite (⟨sfiniteSeq μ i, inferInstance⟩ : FiniteMeasure E)
  have he : (poissonProductLaw μ).map (fun ω => ω i) = poissonComponentLaw μ i :=
    Measure.infinitePi_map_eval _ i
  change ∀ᵐ ν ∂poissonComponentLaw μ i, ν univ < ∞ at h
  rw [← he] at h
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)).mp h

 
theorem poissonProductLaw_insertion (μ : Measure E) [SFinite μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂Measure.sum ω ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂μ := by
  have ha : (fun ω : ℕ → Measure E => ∫⁻ x, F (x,Measure.sum ω) ∂Measure.sum ω) =ᵐ[
      poissonProductLaw μ] (fun ω => ∑' i, ∫⁻ x, F (x,Measure.sum ω) ∂finitePartKernel (ω i)) := by
    filter_upwards [poissonProductLaw_finite μ] with ω hω
    rw [lintegral_sum_measure]
    apply tsum_congr
    intro i
    rw [show finitePartKernel (ω i) = ω i from ite_eq_left (hω i)]
  rw [lintegral_congr_ae ha, lintegral_tsum]
  · simp_rw [poissonComponent_insertion μ _ hF]
    rw [← lintegral_sum_measure, sum_sfiniteSeq]
  · intro i
    apply Measurable.aemeasurable
    apply measurable_finitePart_param (measurable_pi_apply i)
      (F := fun p => F (p.2,Measure.sum p.1))
    exact hF.comp (measurable_snd.prodMk (measurable_measureSum.comp measurable_fst))

lemma poissonProductLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ω, Measure.sum ω s ∂poissonProductLaw μ) = μ s := by
  have hF : Measurable (fun p : E × Measure E => s.indicator (fun _ => (1 : ℝ≥0∞)) p.1) :=
    (measurable_const.indicator hs).comp measurable_fst
  have h := poissonProductLaw_insertion μ hF
  simpa only [lintegral_indicator_const hs, one_mul, lintegral_const,
    measure_univ, mul_one] using h

lemma poissonLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ν, ν s ∂poissonLaw μ) = μ s := by
  rw [poissonLaw, lintegral_map (Measure.measurable_coe hs) measurable_measureSum]
  exact poissonProductLaw_mean_count μ hs

end IsingPerceptron


end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MapWithDensityEquiv
attribute [-instance] _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.powerIntensity_nullSingleton _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Map With Density Equiv. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (e : E ≃ᵐ F) (μ : Measure E) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (w ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    _ = ∫⁻ x, w x * f (e x) ∂μ := by
      rw [lintegral_map hf e.measurable]
      exact lintegral_withDensity_eq_lintegral_mul μ hw
        (show Measurable (fun x => f (e x)) from hf.comp e.measurable)
    _ = ∫⁻ x, (w (e.symm x) * f x) ∂μ.map e := by
      simpa only [Pi.mul_apply, Function.comp_apply, e.symm_apply_apply] using
        (lintegral_map (μ := μ) ((hw.comp e.symm.measurable).mul hf) e.measurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _
      (hw.comp e.symm.measurable) hf).symm

lemma measurable_powerIntensityDensity (b : ℝ) : Measurable (powerIntensityDensity b) := by
  unfold powerIntensityDensity
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · fun_prop
  · fun_prop

lemma powerIntensityDensity_scale {b c : ℝ} (hc : 0 < c) (x : ℝ) :
    ENNReal.ofReal c⁻¹ * powerIntensityDensity b (c⁻¹ * x) =
      ENNReal.ofReal (c ^ b) * powerIntensityDensity b x := by
  have hpos : 0 < c⁻¹ * x ↔ 0 < x := mul_pos_iff_of_pos_left (inv_pos.mpr hc)
  unfold powerIntensityDensity
  by_cases hx : 0 < x
  · simp only [ite_eq_left hx, ite_eq_left (hpos.mpr hx)]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le b)]
    congr 1
    rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hx.le,
      Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
    have he : c⁻¹ * c ^ (-(-1-b)) = c ^ b := by
      rw [show -(-1-b) = b + 1 by ring, Real.rpow_add hc]
      simp only [Real.rpow_one]
      field_simp
    calc
       c⁻¹ * (b * (c ^ (-(-1-b)) * x ^ (-1-b))) =
           b * (c⁻¹ * c ^ (-(-1-b))) * x ^ (-1-b) := by ring
       _ = c ^ b * (b * x ^ (-1-b)) := by rw [he]; ring
  · simp only [ite_eq_right hx, ite_eq_right (fun h => hx (hpos.mp h)), ENNReal.ofReal_zero,
      mul_zero]

theorem map_powerIntensity_mul {b c : ℝ} (hc : 0 < c) :
    (powerIntensity b).map (fun x => c*x) =
      ENNReal.ofReal (c ^ b) • powerIntensity b := by
  let e := MeasurableEquiv.mulLeft₀ c hc.ne'
  have hm := map_withDensity_equiv e volume (measurable_powerIntensityDensity b)
  change (volume.withDensity (powerIntensityDensity b)).map e = _
  rw [hm]
  change (volume.map (fun x => c*x)).withDensity
    (fun x => powerIntensityDensity b (c⁻¹*x)) = _
  unfold powerIntensity
  rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc),
    withDensity_smul_measure, ← withDensity_smul (ENNReal.ofReal c⁻¹)
      (show Measurable (fun x => powerIntensityDensity b (c⁻¹*x)) from
        (measurable_powerIntensityDensity b).comp (measurable_const_mul c⁻¹)),
    ← withDensity_smul (ENNReal.ofReal (c^b)) (measurable_powerIntensityDensity b)]
  congr 1
  funext x
  exact powerIntensityDensity_scale hc x

lemma poissonLaw_congr {E : Type*} [MeasurableSpace E] [Nonempty E]
    {μ ν : Measure E} [SFinite μ] [SFinite ν] (h : μ = ν) : poissonLaw μ = poissonLaw ν := by
  subst ν
  rfl

open Set

lemma integrable_power_min {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (fun x : ℝ => min 1 (max x 0)) (powerIntensity b) := by
  rw [powerIntensity, integrable_withDensity_iff (measurable_powerIntensityDensity b)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn (fun x : ℝ => x ^ (-b)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have hj : IntegrableOn (fun x : ℝ => x ^ (-1-b)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have H₁ : Integrable ((Ioc (0:ℝ) 1).indicator (fun x => b * x ^ (-b))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hi.const_mul b)
  have H₂ : Integrable ((Ioi (1:ℝ)).indicator (fun x => b * x ^ (-1-b))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hj.const_mul b)
  have H := H₁.add H₂
  apply H.congr
  apply ae_of_all
  intro x
  symm
  simp only [Pi.add_apply]
  by_cases hx : 0 < x
  · simp only [powerIntensityDensity, ite_eq_left hx,
      ENNReal.toReal_ofReal (mul_nonneg hb.le (Real.rpow_nonneg hx.le _)), max_eq_left hx.le]
    by_cases hx1 : x ≤ 1
    · rw [min_eq_right hx1, indicator_of_mem (show x ∈ Ioc (0:ℝ) 1 from ⟨hx,hx1⟩),
        indicator_of_notMem (show x ∉ Ioi (1:ℝ) from not_lt.mpr hx1), add_zero]
      have hp : x * x ^ (-1-b) = x ^ (-b) := by
        calc
          x * x ^ (-1-b) = x ^ (1 + (-1-b)) := by rw [Real.rpow_add hx, Real.rpow_one]
          _ = x ^ (-b) := by congr 1; ring
      nlinarith [hp]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge hx1)), one_mul,
        indicator_of_notMem (show x ∉ Ioc (0:ℝ) 1 from fun h => hx1 h.2),
        indicator_of_mem (show x ∈ Ioi (1:ℝ) from lt_of_not_ge hx1), zero_add]
  · simp [powerIntensityDensity, hx, max_eq_right (le_of_not_gt hx),
      indicator_of_notMem (show x ∉ Ioi (1:ℝ) from fun h => hx (lt_trans zero_lt_one h))]

lemma measurable_stableLaplaceCost : Measurable stableLaplaceCost := by
  unfold stableLaplaceCost
  fun_prop

lemma stableLaplaceCost_nonneg (x : ℝ) : 0 ≤ stableLaplaceCost x := by
  unfold stableLaplaceCost
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _)))

lemma stableLaplaceCost_le_min (x : ℝ) : stableLaplaceCost x ≤ min 1 (max x 0) := by
  unfold stableLaplaceCost
  exact le_min (by linarith [Real.exp_pos (-max x 0)])
    (by linarith [Real.add_one_le_exp (-max x 0)])

lemma integrable_stableLaplaceCost {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable stableLaplaceCost (powerIntensity b) := by
  apply (integrable_power_min hb hb1).mono' measurable_stableLaplaceCost.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (stableLaplaceCost_nonneg x)]
    exact stableLaplaceCost_le_min x

lemma stableLaplaceConstant_lt_top {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b < ∞ := by
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ stableLaplaceCost_nonneg)).mp
    (integrable_stableLaplaceCost hb hb1).hasFiniteIntegral

lemma stableLaplaceConstant_pos {b : ℝ} (hb : 0 < b) : 0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant powerIntensity
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_powerIntensityDensity b)
    measurable_stableLaplaceCost.ennreal_ofReal]
  apply (lintegral_pos_iff_support ((measurable_powerIntensityDensity b).mul
    measurable_stableLaplaceCost.ennreal_ofReal)).mpr
  have hs : Function.support (powerIntensityDensity b * (fun x => ENNReal.ofReal (stableLaplaceCost x))) =
      Ioi (0:ℝ) := by
    ext x
    by_cases hx : 0 < x
    · have hp : 0 < b * x ^ (-1-b) := mul_pos hb (Real.rpow_pos_of_pos hx _)
      have hc : 0 < 1 - Real.exp (-x) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
      simp [Function.mem_support, powerIntensityDensity, stableLaplaceCost, hx,
        max_eq_left hx.le, ne_of_gt (ENNReal.ofReal_pos.mpr hp), ne_of_gt (ENNReal.ofReal_pos.mpr hc)]
    · simp [Function.mem_support, powerIntensityDensity, hx]
  rw [hs]
  simp

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_negExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) : Integrable (fun ω => negExp (X ω)) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_negExp.measurable.comp hX).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖negExp (X ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
    exact negExp_le_one _

lemma measure_zero_of_integral_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : ℕ → Ω → ℝ} (hfi : ∀ n, Integrable (f n) P)
    (hfpos : ∀ n ω, 0 ≤ f n ω) (hb : ∀ n ω, ω ∈ A → 1 ≤ f n ω)
    (ht : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 0)) : P A = 0 := by
  apply (measureReal_eq_zero_iff (μ := P) (s := A)).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto' ht
  intro n
  rw [← integral_indicator_one hA]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hA) (hfi n)
  intro ω
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω, Pi.one_apply] using hb n ω hω
  · simpa only [indicator_of_notMem hω] using hfpos n ω

theorem stable_laplace_finite_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) {C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hl : ∀ t : ℝ, 0 < t →
      (∫ ω, negExp (ENNReal.ofReal t * X ω) ∂P) = Real.exp (-C * t ^ b)) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  have hi (t : ℝ) : Integrable (fun ω => negExp (ENNReal.ofReal t * X ω)) P :=
    integrable_negExp P (measurable_const.mul hX)
  have hfinite : P {ω | X ω = ∞} = 0 := by
    let t : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
    have htpos (n : ℕ) : 0 < t n := by dsimp [t] <;> positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton ∞))
      (f := fun n ω => 1 - negExp (ENNReal.ofReal (t n) * X ω))
    · intro n
      exact (integrable_const 1).sub (hi (t n))
    · intro n ω
      exact sub_nonneg.mpr (negExp_le_one _)
    · intro n ω hω
      change X ω = ∞ at hω
      simp [hω, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (htpos n)))]
    · have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun n => (t n)^b) atTop (𝓝 0) := by
        simpa only [Function.comp_def, Real.zero_rpow hb.ne'] using (Real.continuous_rpow_const hb.le).continuousAt.tendsto.comp ht
      have he : Tendsto (fun n => 1 - Real.exp (-C * (t n)^b)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, mul_zero, Real.exp_zero, sub_self] using
          (tendsto_const_nhds (x := (1:ℝ))).sub (Real.continuous_exp.continuousAt.tendsto.comp (hr.const_mul (-C)))
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      ext n
      rw [integral_sub (integrable_const 1) (hi (t n)), hl _ (htpos n), integral_const]
      simp
  have hpositive : P {ω | X ω = 0} = 0 := by
    let t : ℕ → ℝ := fun n => (n:ℝ)+1
    have htpos (n : ℕ) : 0 < t n := by dsimp [t] <;> positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton 0))
      (f := fun n ω => negExp (ENNReal.ofReal (t n) * X ω))
    · exact fun n => hi (t n)
    · exact fun _ _ => negExp_nonneg _
    · intro n ω hω
      change X ω = 0 at hω
      simp [hω]
    · have ht : Tendsto t atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have hr := (tendsto_rpow_atTop hb).comp ht
      have he := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hC hr))
      simpa only [hl _ (htpos _), Function.comp_def, neg_mul] using he
  have hf : ∀ᵐ ω ∂P, X ω ≠ ∞ := by simpa only [ae_iff, not_not] using hfinite
  have hp : ∀ᵐ ω ∂P, X ω ≠ 0 := by simpa only [ae_iff, not_not] using hpositive
  filter_upwards [hf, hp] with ω hf hp
  exact ⟨pos_iff_ne_zero.mpr hp, lt_top_iff_ne_top.mpr hf⟩

lemma stableLaplaceCost_scale (t x : ℝ) (ht : 0 ≤ t) :
    stableLaplaceCost (t*x) = 1-Real.exp (-t * max x 0) := by
  have hm : max (t*x) 0 = t * max x 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg x 0 ht).symm
  rw [stableLaplaceCost, hm]
  congr 2
  ring

lemma powerIntensity_laplace_scale {b t : ℝ} (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-t * max x 0)) ∂powerIntensity b) =
    ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  simp_rw [← stableLaplaceCost_scale t _ ht.le]
  rw [← lintegral_map measurable_stableLaplaceCost.ennreal_ofReal
    (measurable_const_mul t), map_powerIntensity_mul ht, lintegral_smul_measure]
  rfl

lemma integrable_exp_neg_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (-t * X ω)) P := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hω)

lemma measureReal_mul_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : Ω → ℝ} (hf : Integrable f P) (hfpos : 0 ≤ᵐ[P] f) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, ω ∈ A → c ≤ f ω) : P.real A * c ≤ ∫ ω, f ω ∂P := by
  rw [← smul_eq_mul, ← integral_indicator_const c hA]
  apply integral_mono_ae ((integrable_const c).indicator hA) hf
  filter_upwards [hfpos, hc] with ω hp hb
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω] using hb hω
  · simpa only [indicator_of_notMem hω, Pi.zero_apply] using hp

lemma stable_laplace_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < X ω} ≤ ENNReal.ofReal (C / (1-Real.exp (-1)) * s^(-b)) := by
  have hc : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hi := integrable_exp_neg_mul P hX hpos (inv_nonneg.mpr hs.le)
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX)
    ((integrable_const 1).sub hi) (by
      filter_upwards [hpos] with ω hω
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [inv_nonneg.mpr hs.le])))
    (1-Real.exp (-1)) (by
      filter_upwards [] with ω hω
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      have hmul : 1 < s⁻¹ * X ω := by
        rw [← div_eq_inv_mul, lt_div_iff₀ hs]
        simpa using hω
      linarith)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) hi, integral_const, hl _ (inv_pos.mpr hs)] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  have hbnd : P.real {ω | s < X ω} ≤ C / (1-Real.exp (-1)) * s^(-b) := by
    have he := Real.add_one_le_exp (-C * (s⁻¹)^b)
    have hp : (s⁻¹)^b = s^(-b) := by rw [Real.inv_rpow hs.le, Real.rpow_neg hs.le]
    rw [hp] at h he
    apply (le_of_mul_le_mul_right _ hc)
    calc
      _ ≤ 1-Real.exp (-C * s^(-b)) := h
      _ ≤ C * s^(-b) := by linarith
      _ = (C / (1-Real.exp (-1)) * s^(-b)) * (1-Real.exp (-1)) := by field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma stable_laplace_inverse_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < (X ω)⁻¹} ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-C*s^b)) := by
  have hi := integrable_exp_neg_mul P hX (hpos.mono fun _ h => h.le) hs.le
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX.inv) hi
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (Real.exp (-1)) (by
      filter_upwards [hpos] with ω hp hω
      apply Real.exp_le_exp.mpr
      have hmul : s * X ω < 1 := by
        simpa only [mul_one] using (lt_inv_mul_iff₀' hp).mp (show s < (X ω)⁻¹ * 1 by simpa using hω)
      linarith)
  rw [hl _ hs] at h
  have hbnd : P.real {ω | s < (X ω)⁻¹} ≤ Real.exp 1 * Real.exp (-C*s^b) := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos (-1))
    calc
      _ ≤ Real.exp (-C*s^b) := h
      _ = (Real.exp 1 * Real.exp (-C*s^b)) * Real.exp (-1) := by
        rw [mul_comm (Real.exp 1), mul_assoc, ← Real.exp_add]
        simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma integrable_rpow_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K b r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hrb : r < b)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < X ω} ≤ ENNReal.ofReal (K*t^(-b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  let B : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator (fun u => u^(r-1)) t +
    (Ioi (1:ℝ)).indicator (fun u => K*u^(r-b-1)) t
  have h₁ : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have h₂ : IntegrableOn (fun t : ℝ => K*t^(r-b-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul K
  have hB : Integrable B (volume.restrict (Ioi 0)) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr h₁).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr h₂)).restrict
  have hBpos : ∀ t, 0 ≤ B t := by
    intro t
    apply add_nonneg
    · exact (indicator_nonneg (s := Ioc (0:ℝ) 1) (fun u hu => Real.rpow_nonneg hu.1.le (r-1))) t
    · exact (indicator_nonneg (s := Ioi (1:ℝ)) (fun u hu => mul_nonneg hK (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hu)) (r-b-1)))) t
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hBpos)).mp hB.hasFiniteIntegral
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases ht1 : t ≤ 1
  · have hb : B t = t^(r-1) := by
      simp only [B, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht0,ht1⟩),
        indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr ht1), add_zero]
    rw [hb]
    exact mul_le_of_le_one_left' prob_le_one
  · have hb : B t = K*t^(r-b-1) := by
      simp only [B, indicator_of_notMem (show t ∉ Ioc (0:ℝ) 1 from fun h => ht1 h.2),
        indicator_of_mem (show t ∈ Ioi (1:ℝ) from lt_of_not_ge ht1), zero_add]
    rw [hb]
    calc
      _ ≤ ENNReal.ofReal (K*t^(-b)) * ENNReal.ofReal (t^(r-1)) :=
        mul_le_mul_of_nonneg_right (htail t ht0) zero_le
      _ = ENNReal.ofReal (K*t^(r-b-1)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg ht0.le _)),
          mul_assoc, ← Real.rpow_add ht0]
        rw [show -b + (r-1) = r-b-1 by ring]

lemma integrable_rpow_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K C b r : ℝ} (hK : 0 ≤ K) (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (htail : ∀ t : ℝ, 0 < t →
      P {ω | t < X ω} ≤ ENNReal.ofReal (K*Real.exp (-C*t^b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  have hi : IntegrableOn (fun t : ℝ => K * (t^(r-1) * Real.exp (-C*t^b))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hb hC).const_mul K
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ K * (t^(r-1) * Real.exp (-C*t^b)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
  apply lt_of_le_of_lt _ ((hasFiniteIntegral_iff_ofReal hnonneg).mp hi.hasFiniteIntegral)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  calc
    _ ≤ ENNReal.ofReal (K*Real.exp (-C*t^b)) * ENNReal.ofReal (t^(r-1)) :=
      mul_le_mul_of_nonneg_right (htail t ht) zero_le
    _ = ENNReal.ofReal (K*(t^(r-1)*Real.exp (-C*t^b))) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_nonneg _))]
      congr 1
      ring

lemma stable_positive_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hrb : r < b)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => X ω ^ r) P := by
  apply integrable_rpow_of_power_tail P hX hpos (K := C/(1-Real.exp (-1)))
    (div_nonneg hC.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))) hr hrb
  exact fun _ ht => stable_laplace_upper_tail P hX hpos hl ht

lemma stable_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b r : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => (X ω)⁻¹ ^ r) P := by
  apply integrable_rpow_of_exp_tail P hX.inv (hpos.mono fun _ h => (inv_pos.mpr h).le)
    (Real.exp_nonneg 1) hC hb hr
  exact fun _ ht => stable_laplace_inverse_tail P hX hpos hl ht

lemma negExp_eq_exp_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : negExp x = Real.exp (-x.toReal) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hx, negExp_ofReal ENNReal.toReal_nonneg]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MarkedPartitionNumerator
attribute [-instance] _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Partition Numerator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable {E : Type*} [MeasurableSpace E] [Nonempty E]

lemma poissonLaw_ae_intensity (μ : Measure E) [SFinite μ] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ ν ∂poissonLaw μ, ∀ᵐ x ∂ν, p x := by
  have he : (∫⁻ ν, ν {x | ¬ p x} ∂poissonLaw μ) = 0 := by
    exact (poissonLaw_mean_count μ (show MeasurableSet {x | ¬p x} from hp.compl)).trans (ae_iff.mp h)
  have hz := (lintegral_eq_zero_iff (Measure.measurable_coe hp.compl)).mp he
  filter_upwards [hz] with ν hν
  exact ae_iff.mpr hν

lemma weightedPoissonTotal_real_eq_ae (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞) {t : ℝ} (ht : 0 ≤ t) :
    (fun ν => ∫⁻ p : ℝ × E, ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal) ∂ν) =ᵐ[
      poissonLaw ((powerIntensity b).prod μ)]
      (fun ν => ENNReal.ofReal t * weightedPoissonTotal a ν) := by
  have hprod : ∀ᵐ p : ℝ × E ∂(powerIntensity b).prod μ, a p.2 < ∞ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt (ha.comp measurable_snd) measurable_const)).mpr
      (ae_of_all _ fun _ => hfin)
  filter_upwards [poissonLaw_ae_intensity ((powerIntensity b).prod μ)
    (measurableSet_lt (ha.comp measurable_snd) measurable_const) hprod] with ν hν
  rw [weightedPoissonTotal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hν] with p hp
  change a p.2 < ∞ at hp
  rw [ENNReal.ofReal_mul (mul_nonneg ht (le_max_right _ _)), ENNReal.ofReal_mul ht,
    ENNReal.ofReal_toReal hp.ne, mul_assoc]

omit [Nonempty E] in
lemma weightedPower_laplace_cost (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (1-Real.exp (-(t * max p.1 0 * (a p.2).toReal)))
      ∂(powerIntensity b).prod μ) =
      ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b := by
  rw [lintegral_prod_symm _ (by fun_prop)]
  have he : (fun y => ∫⁻ x, ENNReal.ofReal
      (1-Real.exp (-(t * max x 0 * (a y).toReal))) ∂powerIntensity b) =ᵐ[μ]
      (fun y => ENNReal.ofReal (t^b) * ENNReal.ofReal ((a y).toReal^b) * stableLaplaceConstant b) := by
    filter_upwards [hpos] with y hy
    have hmul (x : ℝ) : t * max x 0 * (a y).toReal = (t*(a y).toReal)*max x 0 := by ring
    simp_rw [hmul]
    have hs := powerIntensity_laplace_scale (b := b) (mul_pos ht hy)
    simp only [neg_mul] at hs ⊢
    rw [hs, Real.mul_rpow ht.le hy.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [lintegral_congr_ae he, lintegral_mul_const _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]

lemma weightedPoissonTotal_laplace (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {t : ℝ} (ht : 0 < t) :
    (∫ ν, negExp (ENNReal.ofReal t * weightedPoissonTotal a ν)
      ∂poissonLaw ((powerIntensity b).prod μ)) =
      negExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b) := by
  have h := poissonLaw_laplace ((powerIntensity b).prod μ)
    (ψ := fun p => t * max p.1 0 * (a p.2).toReal) (by fun_prop)
    (fun p => mul_nonneg (mul_nonneg ht.le (le_max_right _ _)) ENNReal.toReal_nonneg)
  rw [weightedPower_laplace_cost b μ ha hpos ht] at h
  rw [← h]
  apply integral_congr_ae
  exact ((weightedPoissonTotal_real_eq_ae b μ ha hfin ht.le).fun_comp negExp).symm

end IsingPerceptron

namespace IsingPerceptron

end IsingPerceptron

namespace IsingPerceptron

lemma rawCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) :
    (rawCascadeLaw (n+1) b : Measure (RawTree (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod
        (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))) := rfl

lemma HasStableTotal.finite_positive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  obtain ⟨C, hC, hl⟩ := h
  exact stable_laplace_finite_positive P hX hC hb hl

lemma HasStableTotal.real_laplace {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      (∫ ω, Real.exp (-t * (X ω).toReal) ∂P) = Real.exp (-C*t^b) := by
  have hf := h.finite_positive hX hb
  obtain ⟨C, hC, hl⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [← hl t ht]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, neg_mul]

lemma HasStableTotal.positive_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) (hrb : r < b) : Integrable (fun ω => (X ω).toReal^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  exact stable_positive_moment P hX.ennreal_toReal
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) hC hr hrb hl

lemma HasStableTotal.negative_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) : Integrable (fun ω => ((X ω).toReal)⁻¹^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  apply stable_negative_moment P hX.ennreal_toReal _ hC hb hr hl
  filter_upwards [h.finite_positive hX hb] with ω hω
  exact ENNReal.toReal_pos hω.1.ne' hω.2.ne

lemma weightedPoissonTotal_stable {E : Type*} [MeasurableSpace E] [Nonempty E]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) :
    HasStableTotal (poissonLaw ((powerIntensity b).prod μ)) (weightedPoissonTotal a) b := by
  let A := ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ
  have hA : A < ∞ := by
    exact hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
      |>.mp hpay.hasFiniteIntegral
  have hApos : 0 < A := by
    apply (lintegral_pos_iff_support (ha.ennreal_toReal.pow_const b |>.ennreal_ofReal)).mpr
    have he : (Function.support (fun y => ENNReal.ofReal ((a y).toReal^b))) =ᵐ[μ] Set.univ := by
      filter_upwards [hpos] with y hy
      apply propext
      change (ENNReal.ofReal ((a y).toReal^b) ≠ 0) ↔ True
      exact iff_true_intro (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hy _)))
    rw [measure_congr he, measure_univ]
    exact zero_lt_one
  let C := A * stableLaplaceConstant b
  have hC : C < ∞ := ENNReal.mul_lt_top hA (stableLaplaceConstant_lt_top hb hb1)
  have hCp : 0 < C := ENNReal.mul_pos hApos.ne' (stableLaplaceConstant_pos hb).ne'
  refine ⟨C.toReal, ENNReal.toReal_pos hCp.ne' hC.ne, fun t ht => ?_⟩
  rw [weightedPoissonTotal_laplace b μ ha hfin hpos ht, mul_assoc]
  change negExp (ENNReal.ofReal (t^b) * C) = _
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _)]
  congr 1
  ring

lemma CascadeExponents.tail {n : ℕ} {b : ℕ → ℝ} (h : CascadeExponents (n+1) b) :
    CascadeExponents n (fun i => b (i+1)) := by
  exact ⟨fun i hi => h.1 (i+1) (by omega), fun i j hij hj => h.2 (i+1) (j+1) (by omega) (by omega)⟩

theorem rawCascade_total_moments (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    (∀ᵐ T ∂(rawCascadeLaw n b : Measure (RawTree n)),
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) ∧
    (∀ r : ℝ, 0 < r → (∀ i < n, r < b i) →
      Integrable (fun T => (rawTreeTotal n T).toReal^r) (rawCascadeLaw n b : Measure (RawTree n))) ∧
    (∀ r : ℝ, 0 < r → Integrable (fun T => ((rawTreeTotal n T).toReal)⁻¹^r)
      (rawCascadeLaw n b : Measure (RawTree n))) := by
  induction n generalizing b with
  | zero =>
    refine ⟨ae_of_all _ (fun _ => by simp [rawTreeTotal]), ?_, ?_⟩
    · intro r _ _
      simp [rawTreeTotal]
    · intro r _
      simp [rawTreeTotal]
  | succ n ih =>
    have hi := ih (fun i => b (i+1)) hb.tail
    have hb0 := hb.1 0 (by omega)
    have hpos : ∀ᵐ T ∂(rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n)),
        0 < (rawTreeTotal n T).toReal := by
      filter_upwards [hi.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    have hm := hi.2.1 (b 0) hb0.1 (fun i hi => hb.2 0 (i+1) (by omega) (by omega))
    have hs : HasStableTotal (rawCascadeLaw (n+1) b : Measure (RawTree (n+1)))
        (rawTreeTotal (n+1)) (b 0) :=
      weightedPoissonTotal_stable hb0.1 hb0.2 _ (measurable_rawTreeTotal n)
        (hi.1.mono fun _ h => h.2) hpos hm
    exact ⟨hs.finite_positive (measurable_rawTreeTotal _) hb0.1,
      fun r hr hrb => hs.positive_moment (measurable_rawTreeTotal _) hb0.1 hr (hrb 0 (by omega)),
      fun r hr => hs.negative_moment (measurable_rawTreeTotal _) hb0.1 hr⟩

open scoped ProbabilityTheory

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_WeightedPartitionNumeratorIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafKernel_markov _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Partition Numerator Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable (A : Type) [MeasurableSpace A]

variable [Nonempty A]

lemma noiseCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) := rfl

lemma noiseCascadeLaw_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeForget A n) = rawCascadeLaw n b := by
  induction n generalizing b μ with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw _).map (fun ν => ν.map (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))) = _
    rw [poissonLaw_map _ (T := fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))
      (measurable_fst.prodMk
      ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd)))]
    apply poissonLaw_congr
    have he : (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2)) =
        Prod.map id (fun q : A × NoiseTree A n => noiseTreeForget A n q.2) := rfl
    rw [he, ← Measure.map_prod_map _ _ (f := id)
      (g := fun q : A × NoiseTree A n => noiseTreeForget A n q.2) measurable_id
      ((measurable_noiseTreeForget A n).comp measurable_snd), Measure.map_id]
    congr 1
    change (((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))).map
        (noiseTreeForget A n ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_noiseTreeForget A n) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, ih]

omit [Nonempty A] in
lemma noiseTreeTotal_succ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseTreeTotal A (n+1) ν = ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 ∂ν := by
  change (∫⁻ p, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2
    ∂ν.map (fun p => (p.1,noiseTreeForget A n p.2.2))) = _
  rw [lintegral_map]
  · rfl
  · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
      ((measurable_rawTreeTotal n).comp measurable_snd)
  · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseTreeKeep
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Tree Keep. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma measurable_measure_ae {E : Type*} [MeasurableSpace E] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) : MeasurableSet {ν : Measure E | ∀ᵐ x ∂ν, p x} := by
  simp only [ae_iff]
  exact measurableSet_eq_fun (Measure.measurable_coe hp.compl) measurable_const

lemma normalizeMass_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (ν : Measure E) {f : E → F} (hf : Measurable f)
    (hν : 0 < ν univ ∧ ν univ < ∞) :
    (normalizeMass ν).map f = normalizeMass (ν.map f) := by
  have ht : ν.map f univ = ν univ := by rw [Measure.map_apply hf MeasurableSet.univ]; rfl
  rw [normalizeMass, ite_eq_left hν, normalizeMass, ht, ite_eq_left hν,
    Measure.map_smul]

variable (A : Type) [MeasurableSpace A] [Nonempty A]

omit [Nonempty A] in
lemma measurableSet_GoodNoiseTree (n : ℕ) : MeasurableSet {ν | GoodNoiseTree A n ν} := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    exact ((measurableSet_lt measurable_const (measurable_noiseTreeTotal A (n+1))).inter
      (measurableSet_lt (measurable_noiseTreeTotal A (n+1)) measurable_const)).inter
        (measurable_measure_ae (ih.preimage (measurable_snd.comp measurable_snd)))

lemma noiseCascade_good (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), GoodNoiseTree A n ν := by
  induction n generalizing b μ with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    have htot : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞ := by
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        (measurable_noiseTreeForget A (n+1)).aemeasurable
      rw [noiseCascadeLaw_forget]
      exact (rawCascade_total_moments (n+1) b hb).1
    have hm : MeasurableSet {p : ℝ × (A × NoiseTree A n) | GoodNoiseTree A n p.2.2} :=
      (measurableSet_GoodNoiseTree A n).preimage (by fun_prop)
    have hdesc : ∀ᵐ p ∂(powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)))), GoodNoiseTree A n p.2.2 := by
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      apply ae_of_all
      intro _
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_GoodNoiseTree A n).preimage measurable_snd)).mpr
      exact ae_of_all _ (fun _ => ih (fun j => b (j+1)) hb.tail (fun j => μ (j+1)))
    have hc := poissonLaw_ae_intensity _ hm hdesc
    filter_upwards [htot, hc] with ν ht hd
    exact ⟨ht, hd⟩

omit [Nonempty A] in
lemma noiseChildMass_univ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseChildMass A n ν univ = noiseTreeTotal A (n+1) ν := by
  rw [noiseTreeTotal_succ]
  simp [noiseChildMass, withDensity_apply]

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable (A : Type) [MeasurableSpace A] [Nonempty A]

lemma noiseLeafKernel_succ (n : ℕ) : noiseLeafKernel A (n+1) =
    ((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ noiseLeafKernel A n)) ∘ₖ
      noiseChildKernel A n := rfl

lemma noiseLeafKernel_step (n : ℕ) (ν : NoiseTree A (n+1))
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2 ∂noiseChildKernel A n ν := by
  rw [noiseLeafKernel_succ, Kernel.lintegral_comp _ _ _ hF]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply, lintegral_prod _ hF.aemeasurable,
    lintegral_dirac']
  swap
  · exact hF.lintegral_prod_right'
  rw [Kernel.parallelComp_apply, Kernel.id_apply,
    lintegral_prod _ (show AEMeasurable (fun y : A × NoiseLeaf A n => F (p.1,y)) _ from
      (hF.comp measurable_prodMk_left).aemeasurable),
    lintegral_dirac']
  exact (hF.comp measurable_prodMk_left).lintegral_prod_right'

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [Nonempty A] in
lemma measurable_noiseLeafTerminal (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafTerminal n X u p.1 p.2) := by
  induction n generalizing X u with
  | zero => exact (hX 0).comp measurable_fst
  | succ n ih =>
    exact (ih (fun i => hX (i+1)) (fun i => hu (i+1))).comp
      (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))

lemma noiseChildKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : ℝ × (A × NoiseTree A n) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂noiseChildKernel A n ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 * F p ∂ν := by
  change (∫⁻ p, F p ∂normalizeMass (noiseChildMass A n ν)) = _
  rw [normalizeMass, ite_eq_left (by simpa only [noiseChildMass_univ] using hν),
    lintegral_smul_measure, smul_eq_mul, noiseChildMass_univ, noiseChildMass]
  congr 1
  exact lintegral_withDensity_eq_lintegral_mul ν
    (show Measurable (fun p : ℝ × (A × NoiseTree A n) =>
      ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2) from
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal A n).comp (by fun_prop)))) hF

lemma noiseLeafKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_step A n ν hF]
  apply noiseChildKernel_lintegral n ν hν
  exact (hF.comp (by fun_prop : Measurable (fun p :
      (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
    (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma noiseLeafKernel_unnormalized_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    noiseTreeTotal A (n+1) ν * (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_lintegral n ν hν hF, ← mul_assoc,
    ENNReal.mul_inv_cancel hν.1.ne' hν.2.ne, one_mul]

end IsingPerceptron

namespace IsingPerceptron

lemma normalizeMass_of_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] : normalizeMass ν = ν := by
  simp [normalizeMass, measure_univ]

lemma normalizeMass_smul {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞)
    (hν : 0 < ν univ ∧ ν univ < ∞) : normalizeMass (c • ν) = normalizeMass ν := by
  have ht : 0 < (c • ν) univ ∧ (c • ν) univ < ∞ := by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ⟨ENNReal.mul_pos hc.1.ne' hν.1.ne', ENNReal.mul_lt_top hc.2 hν.2⟩
  rw [normalizeMass, ite_eq_left ht, normalizeMass, ite_eq_left hν,
    Measure.smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc.1.ne') (Or.inl hc.2.ne)]
  congr 1
  calc
    c⁻¹ * (ν univ)⁻¹ * c = (c⁻¹*c)*(ν univ)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc.1.ne' hc.2.ne, one_mul]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_prod_join {ι E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : ι → Measure E) (ν : ι → Measure F)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  refine (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro I
  have hμ : MeasurePreserving I.restrict (Measure.infinitePi μ) (Measure.pi (fun i : I => μ i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict μ⟩
  have hν : MeasurePreserving I.restrict (Measure.infinitePi ν) (Measure.pi (fun i : I => ν i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict ν⟩
  have hp := hμ.prod hν
  have hs := (measurePreserving_arrowProdEquivProdArrow E F I (fun i => μ i) (fun i => ν i)).symm
  rw [Measure.map_map I.measurable_restrict (by fun_prop)]
  exact (hs.comp hp).map_eq

lemma finitePoissonProduct_laplace_partial {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i)
      ∂Measure.infinitePi (fun i => finitePoissonLaw (μ i))) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ i : Measure E)) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind := iIndepFun_infinitePi (P := fun i => finitePoissonLaw (μ i)) (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂Measure.infinitePi (fun j => finitePoissonLaw (μ j))) =
        negExp (∫⁻ x, c x ∂(μ i : Measure E)) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂finitePoissonLaw (μ i) :=
        (measurePreserving_eval_infinitePi (fun j => finitePoissonLaw (μ j)) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace (μ i) hψ hpos
  simpa only [negExp_sum, hei] using hh

theorem finitePoissonProduct_sum_law {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) :
    (Measure.infinitePi (fun n => finitePoissonLaw (μ n))).map Measure.sum =
      poissonLaw (Measure.sum (fun n => (μ n : Measure E))) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  let P := Measure.infinitePi (fun n => finitePoissonLaw (μ n))
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto P ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂(μ i : Measure E)))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂Measure.sum (fun n => (μ n : Measure E))))) := by
    rw [lintegral_sum_measure]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂(μ i : Measure E))]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw_laplace _ hψ hpos,
    integral_map measurable_measureSum.aemeasurable heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂P) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a,P,finitePoissonProduct_laplace_partial μ hψ hpos] using hlim) (by simpa only [lintegral_sum_measure] using hr)

lemma finiteCloud_laplace {E : Type*} [MeasurableSpace E] (r : ℝ≥0)
    (ρ : Measure E) [IsProbabilityMeasure ρ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) ∂finitePoissonCloud r ρ) =
      negExp ((r : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂ρ) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) ρ := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) ρ := (integrable_const 1).sub hi
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace r ρ hψ hpos,
    ← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul r.coe_nonneg,
    negExp_ofReal (mul_nonneg r.coe_nonneg (integral_nonneg hcost)),
    integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring

lemma finiteCloud_mark_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (r : ℝ≥0) (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((finitePoissonCloud r μ).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) = finitePoissonCloud r (μ.prod ν) := by
  have hj : MeasurePreserving (fun p : (ℕ → E) × (ℕ → F) => fun i => (p.1 i,p.2 i))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => ν)))
      (Measure.infinitePi (fun _ : ℕ => μ.prod ν)) :=
    ⟨by fun_prop,infinitePi_prod_join _ _⟩
  have hp := (MeasurePreserving.id (poissonMeasure r)).prod hj
  have ha := measurePreserving_prodAssoc (poissonMeasure r)
    (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => ν))
  exact (hp.comp ha).map_eq

lemma finiteCloud_mark_measure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : FiniteMeasure E) (ν : Measure F) [IsProbabilityMeasure ν] :
    ((finitePoissonCloud μ.mass (μ.normalize : Measure E)).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
      finitePoissonLaw ⟨(μ : Measure E).prod ν,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ := by
  let ξ : FiniteMeasure (E × F) := ⟨(μ : Measure E).prod ν,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  change _ = finitePoissonLaw ξ
  rw [show (fun p : (ℕ × (ℕ → E)) × (ℕ → F) =>
    finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
    finiteCloudMeasure ∘ (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) from rfl,
    ← Measure.map_map measurable_finiteCloudMeasure (by fun_prop),finiteCloud_mark_law]
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun π : Measure (E × F) => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂π)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map measurable_finiteCloudMeasure.aemeasurable hm.aestronglyMeasurable,
    finiteCloud_laplace _ _ hψ hpos,finitePoissonLaw_laplace ξ hψ hpos]
  change _ = negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E).prod ν)
  rw [finiteMeasure_mass_normalize μ,Measure.prod_smul_left,lintegral_smul_measure]
  rfl

lemma measurable_labeledMarkedMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] :
    Measurable (labeledMarkedMeasure (E := E) (F := F)) := by
  apply measurable_measureSum.comp
  apply Measurable.of_eval
  intro n
  apply measurable_finiteCloudMeasure.comp
  fun_prop

theorem labeledMarkedMeasure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : ℕ → FiniteMeasure E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    ((labeledPoissonLaw μ).prod (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => ν)))).map labeledMarkedMeasure =
    poissonLaw ((Measure.sum (fun n => (μ n : Measure E))).prod ν) := by
  let f : (ℕ × (ℕ → E)) × (ℕ → F) → Measure (E × F) :=
    fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))
  have hf : Measurable f := measurable_finiteCloudMeasure.comp (by fun_prop)
  have hjoin : Measurable (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := by
    fun_prop
  have hfpi : Measurable (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) :=
    Measurable.of_eval (fun _ => hf.comp (measurable_pi_apply _))
  have hcomp : (labeledMarkedMeasure (E := E) (F := F)) =
    Measure.sum ∘ (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) ∘
      (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := rfl
  rw [hcomp,← Function.comp_assoc,← Measure.map_map (measurable_measureSum.comp hfpi) hjoin,
    labeledPoissonLaw,infinitePi_prod_join,
    ← Measure.map_map measurable_measureSum hfpi,Measure.infinitePi_map_pi _ (fun _ => hf)]
  simp only [f,finiteCloud_mark_measure_law]
  let η : ℕ → FiniteMeasure (E × F) := fun i => ⟨(μ i : Measure E).prod ν,(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_labeledMarkedMeasure <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  change (Measure.infinitePi (fun i => finitePoissonLaw (η i))).map Measure.sum = _
  rw [finitePoissonProduct_sum_law η]
  have hcongr {P Q : Measure (E × F)} [SFinite P] [SFinite Q] (h : P = Q) :
      poissonLaw P = poissonLaw Q := by subst Q; rfl
  apply hcongr
  exact (Measure.prod_sum_left _ _).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ChildLabel
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedForestCoordinates_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledLeafEncodable _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma intensityComponents_sum {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ] :
    Measure.sum (fun n => (intensityComponents μ n : Measure E)) = μ :=
  sum_sfiniteSeq μ

lemma labeledLeafMass_lintegral (n : ℕ) (ω : LabeledTree n) (F : LabeledLeaf n → ℝ≥0∞) :
    (∫⁻ v, F v ∂labeledLeafMass n ω) = ∑' v, labeledLeafWeight n ω v * F v := by
  rw [labeledLeafMass,lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) 
    (measurable_of_countable _),lintegral_count]
  rfl

lemma finiteCloud_tsum_weight (ω : WeightCloud) (F : ChildLabel → ℝ≥0∞) :
    (∑' a, childLabelWeight ω a * F a) =
      ∑' m, ∑ i : Fin (ω m).1, ENNReal.ofReal (max ((ω m).2 i) 0) * F (m,i) := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro m
  simp only [childLabelWeight,ite_mul,zero_mul]
  rw [tsum_eq_sum (s := Finset.range (ω m).1)]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [i.isLt,ite_true, if_true]
  · intro i hi
    exact ite_eq_right (by simpa using hi)

variable (A : Type) [MeasurableSpace A]

@[fun_prop] lemma measurable_labeledNoiseJoin (n : ℕ) : Measurable (labeledNoiseJoin A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => labeledMarkedMeasure (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))
    apply measurable_labeledMarkedMeasure.comp
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.of_eval
    intro m
    apply Measurable.of_eval
    intro i
    exact (by fun_prop : Measurable (fun p : LabeledTree (n+1) × MarkForest A (n+1) =>
      (p.2 m i).1)).prodMk (ih.comp (by fun_prop))

lemma infinitePi_prod_join2 {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
      (fun p m i => (p.1 m i,p.2 m i)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ.prod ν)) := by
  rw [show (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m i => (p.1 m i,p.2 m i)) =
      (fun q : ℕ → (ℕ → E) × (ℕ → F) => fun m i => ((q m).1 i,(q m).2 i)) ∘
      (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m => (p.1 m,p.2 m)) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join,
    Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : (ℕ → E) × (ℕ → F)) => fun i => (q.1 i,q.2 i))
      (fun _ => by fun_prop)]
  simp_rw [infinitePi_prod_join]

lemma measurePreserving_swap_first_two {E F G : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure F) (ξ : Measure G)
    [SFinite μ] [SFinite ν] [SFinite ξ] :
    MeasurePreserving (fun p : E × (F × G) => (p.2.1,(p.1,p.2.2)))
      (μ.prod (ν.prod ξ)) (ν.prod (μ.prod ξ)) := by
  exact (measurePreserving_prodAssoc ν μ ξ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ξ)).comp
      (measurePreserving_prodAssoc μ ν ξ).symm)

theorem labeledNoiseJoin_law [Nonempty A] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw A n μ)).map (labeledNoiseJoin A n) = noiseCascadeLaw A n b μ := by
  induction n generalizing b μ with
  | zero =>
    change ((Measure.dirac (PUnit.unit : PUnit)).prod (Measure.dirac (PUnit.unit : PUnit))).map
      (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let b' := fun j => b (j+1)
    let μ' := fun j => μ (j+1)
    let L : Measure (LabeledTree n) := labeledCascadeLaw n b'
    let M : Measure (MarkForest A n) := markForestLaw A n μ'
    let R : Measure (NoiseTree A n) := noiseCascadeLaw A n b' μ'
    let W := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))
    have hi : MeasurePreserving (labeledNoiseJoin A n) (L.prod M) R :=
      ⟨measurable_labeledNoiseJoin A n,ih b' μ'⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp
      (measurePreserving_swap_first_two L (μ 0 : Measure A) M)
    have hmap : (L.prod ((μ 0 : Measure A).prod M)).map
        (fun p => (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) = (μ 0 : Measure A).prod R := hp.map_eq
    have hpi : MeasurePreserving
        (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2)))
        ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L))).prod
          (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M))))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := by
      refine ⟨Measurable.of_eval (fun m => Measurable.of_eval (fun i =>
        (by fun_prop : Measurable (fun p : (ℕ → ℕ → LabeledTree n) ×
            (ℕ → ℕ → A × MarkForest A n) => (p.2 m i).1)).prodMk
          ((measurable_labeledNoiseJoin A n).comp (by fun_prop)))),?_⟩
      rw [show (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2))) =
          (fun q : ℕ → ℕ → LabeledTree n × (A × MarkForest A n) => fun m i =>
            ((q m i).2.1,labeledNoiseJoin A n ((q m i).1,(q m i).2.2))) ∘
          (fun p => fun m i => (p.1 m i,p.2 m i)) from rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join2,
        Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → LabeledTree n × (A × MarkForest A n)) => fun i =>
          ((q i).2.1,labeledNoiseJoin A n ((q i).1,(q i).2.2))) (fun _ => by fun_prop)]
      simp_rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (p : LabeledTree n × (A × MarkForest A n)) =>
        (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) (fun _ => hp.measurable),hmap]
    have hfull := ((MeasurePreserving.id W).prod hpi).comp
      (measurePreserving_prodAssoc W _ _)
    change ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
      (labeledMarkedMeasure ∘ (fun p => (p.1.1,fun m i =>
        ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))) = _
    have hfm : Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) := hfull.measurable
    rw [← Measure.map_map measurable_labeledMarkedMeasure hfm]
    have hfe : ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
        (fun p => (p.1.1,fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) =
        W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := hfull.map_eq
    rw [hfe,labeledMarkedMeasure_law,noiseCascadeLaw_succ]
    apply poissonLaw_congr
    rw [intensityComponents_sum]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_option_join {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun p : A × (ι → A) => fun i : Option ι =>
      i.elim p.1 p.2) = Measure.infinitePi (fun i : Option ι => i.elim μ ν) := by
  classical
  let ρ : Option ι → Measure A := fun i => i.elim μ ν
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i => by cases i <;> dsimp [ρ] <;> infer_instance
  change _ = Measure.infinitePi ρ
  refine Measure.eq_infinitePi ρ (fun I t ht => ?_)
  have hm : Measurable (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop
  rw [Measure.map_apply hm (.pi I.countable_toSet (fun i _ => ht i))]
  have he : (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) ⁻¹'
      ((I : Set (Option ι)).pi t) =
      (if none ∈ I then t none else Set.univ) ×ˢ ((I.eraseNone : Set ι).pi (fun i => t (some i))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_eraseNone]
    constructor
    · intro h
      constructor
      · split_ifs with hn
        · exact h none hn
        · trivial
      · intro i hi
        exact h (some i) hi
    · rintro ⟨ha,hb⟩ i hi
      cases i with
      | none => simpa only [ite_eq_left hi,Option.elim_none] using ha
      | some i => exact hb i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ I
  · rw [ite_eq_left hn,← Finset.prod_erase_mul _ _ hn]
    have her : I.erase none = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp
    rw [her,Finset.prod_map,mul_comm]
    rfl
  · rw [ite_eq_right hn,measure_univ,one_mul]
    have her : I = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp [hn]
    rw [her,Finset.prod_map]
    simp only [Finset.eraseNone_map_some]
    rfl

lemma infinitePi_option_split {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i : Option ι => i.elim μ ν)).map
      (fun g => (g none,fun i => g (some i))) = μ.prod (Measure.infinitePi ν) := by
  rw [← infinitePi_option_join μ ν,Measure.map_map (by fun_prop) (by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop)]
  change (μ.prod (Measure.infinitePi ν)).map id = _
  exact Measure.map_id

lemma infinitePi_triple_curry {I J K A : Type*} [MeasurableSpace A]
    (μ : I → J → K → Measure A) [∀ i j k, IsProbabilityMeasure (μ i j k)] :
    (Measure.infinitePi (fun p : I × (J × K) => μ p.1 p.2.1 p.2.2)).map
      (fun g i j k => g (i,j,k)) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun j => Measure.infinitePi (μ i j))) := by
  rw [show (fun g : (I × (J × K)) → A => fun i j k => g (i,j,k)) =
      (fun q : I → (J × K → A) => fun i j k => q i (j,k)) ∘
      (MeasurableEquiv.curry I (J × K) A) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),Measure.infinitePi_map_curry
      (fun (i : I) (p : J × K) => μ i p.1 p.2)]
  rw [Measure.infinitePi_map_pi _ (f := fun (_ : I) (q : J × K → A) => fun j k => q (j,k))
    (fun _ => by fun_prop)]
  simp only [show (fun q : J × K → A => fun j k => q (j,k)) =
    MeasurableEquiv.curry J K A from rfl,Measure.infinitePi_map_curry]

variable (A : Type) [MeasurableSpace A]

theorem markForestOfCoords_law (n : ℕ) (μ : ℕ → ProbabilityMeasure A) :
    (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))).map
      (markForestOfCoords A n) = markForestLaw A n μ := by
  induction n generalizing μ with
  | zero =>
    change (Measure.infinitePi _).map (fun _ => (PUnit.unit : PUnit)) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let μ' := fun j => μ (j+1)
    let ν : ForestVertex n → Measure A := fun v => μ' (forestVertexDepth n v)
    have (i : Option (ForestVertex n)) : IsProbabilityMeasure (i.elim (μ 0 : Measure A) ν) := by
      cases i <;> dsimp <;> infer_instance
    have hi : MeasurePreserving (markForestOfCoords A n) (Measure.infinitePi ν)
        (markForestLaw A n μ') := ⟨measurable_markForestOfCoords A n,ih μ'⟩
    have hs : MeasurePreserving (fun g : Option (ForestVertex n) → A =>
        (g none,fun v => g (some v)))
        (Measure.infinitePi (fun v => v.elim (μ 0 : Measure A) ν))
        ((μ 0 : Measure A).prod (Measure.infinitePi ν)) :=
      ⟨by fun_prop,infinitePi_option_split (μ 0 : Measure A) ν⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp hs
    have hmap : (Measure.infinitePi (fun v : Option (ForestVertex n) =>
        v.elim (μ 0 : Measure A) ν)).map (fun g =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) =
        (μ 0 : Measure A).prod (markForestLaw A n μ') := hp.map_eq
    have hc : (fun v : ForestVertex (n+1) => (μ (forestVertexDepth (n+1) v) : Measure A)) =
        (fun v : ℕ × (ℕ × Option (ForestVertex n)) => v.2.2.elim (μ 0 : Measure A) ν) := by
      funext v
      rcases v with ⟨m,i,v⟩
      cases v <;> rfl
    rw [hc]
    change (Measure.infinitePi (fun v : ℕ × (ℕ × Option (ForestVertex n)) =>
        v.2.2.elim (μ 0 : Measure A) ν)).map
        ((fun q : ℕ → ℕ → Option (ForestVertex n) → A => fun m i =>
          (q m i none,markForestOfCoords A n (fun v => q m i (some v)))) ∘
          (fun g m i v => g (m,i,v))) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_triple_curry
        (fun (_ _ : ℕ) (v : Option (ForestVertex n)) => v.elim (μ 0 : Measure A) ν),
      Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → Option (ForestVertex n) → A) =>
        fun i => (q i none,markForestOfCoords A n (fun v => q i (some v)))) (fun _ => by fun_prop)]
    simp_rw [Measure.infinitePi_map_pi _
        (f := fun (_ : ℕ) (g : Option (ForestVertex n) → A) =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) (fun _ => hp.measurable),hmap]
    rfl

end IsingPerceptron

namespace IsingPerceptron

theorem labeledNoiseCoordinates_law (A : Type) [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))).map
      (fun p => labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      noiseCascadeLaw A n b μ := by
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
    (show MeasurePreserving (markForestOfCoords A n)
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
      (markForestLaw A n μ) from ⟨measurable_markForestOfCoords A n,markForestOfCoords_law A n μ⟩)
  change _ = _
  rw [show (fun p : LabeledTree n × (ForestVertex n → A) =>
      labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      (labeledNoiseJoin A n) ∘ Prod.map id (markForestOfCoords A n) from rfl,
    ← Measure.map_map (measurable_labeledNoiseJoin A n) hp.measurable,hp.map_eq,
    labeledNoiseJoin_law]

lemma labeledMarkedMeasure_lintegral {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F))
    {G : E × F → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G p ∂labeledMarkedMeasure ω) =
      ∑' m, ∑ i : Fin (ω.1 m).1, G ((ω.1 m).2 i,ω.2 m i) := by
  simp only [labeledMarkedMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hG]

lemma labeledMarkedMeasure_ae {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F)) {P : E × F → Prop}
    (hP : MeasurableSet {p | P p}) (h : ∀ᵐ p ∂labeledMarkedMeasure ω, P p) :
    ∀ m (i : Fin (ω.1 m).1), P ((ω.1 m).2 i,ω.2 m i) := by
  intro m i
  have hm := (Measure.ae_sum_iff.mp h) m
  rw [finiteCloudMeasure,← Measure.sum_fintype] at hm
  exact (ae_dirac_iff hP).mp ((Measure.ae_sum_iff.mp hm) i)

variable (A : Type) [MeasurableSpace A] [Nonempty A]

theorem labeledLeafMass_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z))) :
    (labeledLeafMass n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) •
        noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  induction n with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral]
    simp [labeledLeafWeight,labeledNoiseLeaf,noiseTreeTotal,
      rawTreeTotal,noiseLeafKernel,noiseLeafKernelData,Kernel.const_apply]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hgood.1 hF]
    have hinner : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p :
        (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    have hg := labeledMarkedMeasure_ae _
      ((measurableSet_GoodNoiseTree A n).preimage (by fun_prop)) hgood.2
    change (∑' v : ChildLabel × LabeledLeaf n,
      (childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2) *
        F ((ω.1 v.1.1).2 v.1.2,((z v.1.1 v.1.2).1,
          labeledNoiseLeaf A n (ω.2 v.1.1 v.1.2,(z v.1.1 v.1.2).2) v.2))) =
      ∫⁻ p : ℝ × (A × NoiseTree A n), ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂
          labeledMarkedMeasure (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2)))
    have hG : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2)) :=
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (measurable_snd.comp measurable_snd))).mul hinner
    rw [labeledMarkedMeasure_lintegral
      (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2))) hG]
    rw [ENNReal.tsum_prod']
    simp_rw [mul_assoc,ENNReal.tsum_mul_left]
    rw [finiteCloud_tsum_weight]
    apply tsum_congr
    intro m
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have he := ih (ω.2 m i) (z m i).2 (hg m i)
    have hFi : Measurable (fun v : NoiseLeaf A n => F ((ω.1 m).2 i,((z m i).1,v))) := by fun_prop
    have hh := congrArg (fun ν : Measure (NoiseLeaf A n) => ∫⁻ v, F ((ω.1 m).2 i,((z m i).1,v)) ∂ν) he
    rw [lintegral_map' hFi.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul] at hh
    exact hh

theorem labeledLeafLaw_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞) :
    (labeledLeafLaw n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  have hm := labeledLeafMass_noiseMap A n ω z hgood
  have htot : labeledLeafMass n ω Set.univ = noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) := by
    have he := congrArg (fun ν : Measure (NoiseLeaf A n) => ν Set.univ) hm
    simpa only [Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable MeasurableSet.univ,
      Set.preimage_univ,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using he
  rw [labeledLeafLaw,normalizeMass_map _ (measurable_of_countable _) (by simpa only [htot] using ht),
    hm,normalizeMass_smul _ ht (by simp),normalizeMass_of_probability]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

lemma gaussian_pullback_measurePreserving {ι : Type*} (tag : ι → ℕ)
    (ht : Function.Injective tag) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i => g (tag i)) gaussianCoordinates
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp ht).map_fun_eq_infinitePi_map (fun _ => by fun_prop)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma perturbationWeight_sum (N : ℕ) :
    (∑ j : Fin N, perturbationWeight j) = 1-(1/2 : ℝ)^N := by
  rw [Fin.sum_univ_eq_sum_range]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [perturbationWeight,pow_succ]
    ring

lemma perturbationWeight_nonneg (j : ℕ) : 0 ≤ perturbationWeight j := by
  exact pow_nonneg (by norm_num) _

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma labeled_terminal_integral (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    (∫ γ, Real.exp (noiseLeafTerminal n X u s (labeledNoiseLeaf A n (ω,z) γ))
      ∂labeledLeafLaw n ω) =
    ∫ v, Real.exp (noiseLeafTerminal n X u s v)
      ∂noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  rw [← labeledLeafLaw_noiseMap A n ω z hgood ht]
  exact (integral_map (measurable_of_countable _).aemeasurable
    (((measurable_noiseLeafTerminal n hX hu).comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)).symm

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labeledEnergy_terminal (n : ℕ) (ω : LabeledTree n) (z : MarkForest (I → ℝ) n)
    (γ : LabeledLeaf n) (F : (I → ℝ) → ℝ) (H : I → ℝ) :
    noiseLeafTerminal n (fun _ => F) (fun _ p => p.1 + p.2) H
      (labeledNoiseLeaf (I → ℝ) n (ω,z) γ) = F (labeledEnergy n z γ H) := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih => exact ih _ _ _ _

lemma labeledEnergyLog_eq_leaf (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν]
    (H : I → ℝ) (p : LabeledTree n × MarkForest (I → ℝ) n) :
    labeledEnergyLog n ν H p = Real.log (∫ γ,
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H)) ∂labeledLeafLaw n p.1) := by
  have hE : Measurable (fun s : I × LabeledLeaf n => Real.exp (labeledEnergy n p.2 s.2 H s.1)) :=
    measurable_of_countable _
  have hF : Measurable (fun γ : LabeledLeaf n => Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H))) :=
    measurable_of_countable _
  unfold labeledEnergyLog labeledSpinReference
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hE.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hF.aestronglyMeasurable]
  congr 1
  rw [lintegral_prod _ hE.ennreal_ofReal.aemeasurable,
    lintegral_lintegral_swap hE.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro γ
  rw [finiteLogIntegral, Real.exp_log (MeasureTheory.integral_exp_pos Integrable.of_finite)]
  exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma nodeAddress_injective (n : ℕ) : Function.Injective (nodeAddress n) := by
  induction n with
  | zero =>
    intro v w _
    cases v with
    | none => cases w with
      | none => rfl
      | some w => exact w.elim
    | some v => exact v.elim
  | succ n ih =>
    intro v w h
    cases v with
    | none => cases w with
      | none => rfl
      | some w => simp [nodeAddress] at h
    | some v => cases w with
      | none => simp [nodeAddress] at h
      | some w =>
        rcases v with ⟨m,i,v⟩
        rcases w with ⟨m',i',w⟩
        simp only [nodeAddress,List.cons.injEq,Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl⟩,h⟩
        rw [ih h]


lemma nodeAddress_nodeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    nodeAddress n (nodeAt n γ i) = (labeledAddress n γ).take i := by
  induction n with
  | zero => simp [nodeAt,nodeAddress,labeledAddress]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nodeAt,nodeAddress]
    · simp [nodeAt,nodeAddress,labeledAddress,ih]

lemma nodeAddress_length_some (n : ℕ) (v : ForestVertex n) :
    (nodeAddress n (some v)).length = forestVertexDepth n v+1 := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
    rcases v with ⟨m,i,_ | v⟩
    · simp [nodeAddress,forestVertexDepth]
    · simp only [nodeAddress,List.length_cons,ih,forestVertexDepth,Nat.add_assoc]

lemma nodeAddress_nodeAt_length (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    (nodeAddress n (nodeAt n γ i)).length = i := by
  rw [nodeAddress_nodeAt,List.length_take,labeledAddress_length]
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)


lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

lemma labeledEnergy_edge_sum {I : Type} (n : ℕ) (g : ForestVertex n → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n g) γ H x =
      H x + ∑ i : Fin n, g (edgeAt n γ i) x := by
  induction n generalizing H with
  | zero => simp [labeledEnergy]
  | succ n ih =>
    rw [labeledEnergy,markForestOfCoords,ih,Fin.sum_univ_succ]
    simp only [edgeAt,nodeAt_zero,nodeAt_succ,Pi.add_apply]
    ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma tendsto_nat_rpow_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-c)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

lemma perturbationScale_tendsto : Tendsto perturbationScale atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/16:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/16) (by norm_num)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian cascade marking for the actual finite Ising partition function at
a fixed orthogonal rotation. The Haar variable is fixed in this result.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_rotatedFieldTerminal {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : Measurable (rotatedFieldTerminal eig U c) := by
  unfold rotatedFieldTerminal logPartition fieldEnergy
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral-monomial enriched Ising model. Gaussian marks have a
separate variance at every site/tensor coordinate and every cascade level.
The spectral coefficients retain their actual dependence on the rotation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_spinTensorTerminal {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) :
    Measurable (spinTensorTerminal eig U c I degree amplitude) := by
  unfold spinTensorTerminal logPartition spinTensorEnergy
  fun_prop

lemma measurable_spinTensorTerminal_joint {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ) =>
      spinTensorTerminal eig (specialRotation p.1) c I degree amplitude p.2) := by
  have hE (σ : Spin N) : Measurable
      (fun p : SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ) =>
        rotatedEnergy eig (specialRotation p.1) σ + fieldEnergy c σ +
          spinTensorEnergy (specialRotation p.1) I degree amplitude p.2 σ) := by
    apply Measurable.add
    · exact ((Finset.measurable_sum _ fun i _ =>
        (((measurable_specialRotation_eval (spinVector σ) i).comp measurable_fst).pow_const 2).const_mul
          (eig i)).const_mul (1 / 2 : ℝ)).add_const _
    · exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp measurable_snd).mul
          ((measurable_spinTensorFeature I degree amplitude σ i).comp measurable_fst)
  unfold spinTensorTerminal logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log

lemma noiseLeafTerminal_spinTensorTerminal {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (leaf : IsingPerceptron.NoiseLeaf (SpinTensorIndex I degree → ℝ) n) :
    IsingPerceptron.noiseLeafTerminal n (fun _ => spinTensorTerminal eig U c I degree amplitude)
      (fun _ p => p.1 + p.2) z leaf =
      spinTensorTerminal eig U c I degree amplitude (tensorLeafState I degree n z leaf) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => exact ih (z + leaf.2.1) leaf.2.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral tensor model on the countable spin/leaf state space.
The Gaussian energy marks are the actual pushforward of the coordinate
marks, and the tilted ancestor-prefix marginal has its cascade value.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma finiteLogIntegral_uniformSpinPrior {N : ℕ} (H : Spin N → ℝ) :
    IsingPerceptron.finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) H = logPartition H := by
  unfold IsingPerceptron.finiteLogIntegral logPartition
  congr 1
  change (∫ σ, Real.exp (H σ) ∂(PMF.uniformOfFintype (Spin N)).toMeasure) = _
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorGaussianLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat countable Gaussian field has the actual root/forest mark law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNodeTag_injective {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    Function.Injective (fun p : Option (ForestVertex n) × SpinTensorIndex I degree =>
      tensorNodeTag I degree n p.1 p.2) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  have he := Encodable.encode_inj.mp h
  exact Prod.ext (nodeAddress_injective n (congrArg (fun p => p.2.1) he))
    (congrArg (fun p => p.2.2) he)

lemma tensorNodeTag_nodeAt {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (leaf : LabeledLeaf n)
    (level : Fin (n + 1)) (i : SpinTensorIndex I degree) :
    tensorNodeTag I degree n (nodeAt n leaf level) i = treeFeatureTag n leaf (level, i) := by
  unfold tensorNodeTag treeFeatureTag
  rw [nodeAddress_nodeAt_length, nodeAddress_nodeAt]

lemma measurable_tensorStandardGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) : Measurable (tensorStandardGaussianNodes I degree n) := by
  unfold tensorStandardGaussianNodes
  fun_prop

theorem tensorStandardGaussianNodes_law {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    gaussianCoordinates.map (tensorStandardGaussianNodes I degree n) =
      Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1)) := by
  let t := fun p : Option (ForestVertex n) × SpinTensorIndex I degree => tensorNodeTag I degree n p.1 p.2
  have hp := gaussian_pullback_measurePreserving t (tensorNodeTag_injective I degree n)
  change gaussianCoordinates.map
    ((MeasurableEquiv.curry (Option (ForestVertex n)) (SpinTensorIndex I degree) ℝ) ∘
      (fun g => fun p => g (t p))) = _
  rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable, hp.map_eq,
    Measure.infinitePi_map_curry (fun (_ : Option (ForestVertex n)) (_ : SpinTensorIndex I degree) => gaussianReal 0 1)]
  simp only [Measure.infinitePi_eq_pi]

private theorem tensorMarkScale_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (fun z : SpinTensorIndex I degree → ℝ => fun i => (NNReal.sqrt (v i) : ℝ) * z i)
      (Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1))
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ)) := by
  change MeasurePreserving _ _ (Measure.pi (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i)))
  apply measurePreserving_pi
  intro i
  refine ⟨by fun_prop, ?_⟩
  have hs : NNReal.mk ((NNReal.sqrt (v i) : ℝ) ^ 2) (sq_nonneg _) = v i := by
    apply Subtype.ext
    change (NNReal.sqrt (v i) : ℝ) ^ 2 = (v i : ℝ)
    exact_mod_cast NNReal.sq_sqrt (v i)
  simpa only [hs, mul_zero, mul_one] using
    gaussianReal_map_const_mul (μ := 0) (v := 1) (NNReal.sqrt (v i) : ℝ)

lemma measurable_tensorGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (tensorGaussianNodes I degree n v) := by
  unfold tensorGaussianNodes tensorStandardGaussianNodes
  fun_prop

theorem tensorGaussianNodes_measurePreserving {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorGaussianNodes I degree n v) gaussianCoordinates
      (Measure.infinitePi (fun w : Option (ForestVertex n) =>
        (tensorGaussianLaw I degree (v (nodeAddress n w).length) : Measure (SpinTensorIndex I degree → ℝ)))) := by
  have hstd : MeasurePreserving (tensorStandardGaussianNodes I degree n) gaussianCoordinates
      (Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1))) :=
    ⟨measurable_tensorStandardGaussianNodes I degree n, tensorStandardGaussianNodes_law I degree n⟩
  have hscale : MeasurePreserving
      (fun q : Option (ForestVertex n) → SpinTensorIndex I degree → ℝ =>
        fun w i => (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * q w i)
      (Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1)))
      (Measure.infinitePi (fun w : Option (ForestVertex n) =>
        (tensorGaussianLaw I degree (v (nodeAddress n w).length) : Measure (SpinTensorIndex I degree → ℝ)))) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.infinitePi_map_pi (f := fun w (z : SpinTensorIndex I degree → ℝ) =>
      fun i => (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * z i) _ (fun _ => by fun_prop)]
    apply congrArg Measure.infinitePi
    funext w
    exact (tensorMarkScale_measurePreserving I degree (v (nodeAddress n w).length)).map_eq
  exact hscale.comp hstd

/-- The root and all forest coordinates have their independent prescribed
Gaussian laws, including zero variances. -/
theorem tensorGaussianRootForest_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (fun g => (tensorGaussianNodes I degree n v g none,
      fun w => tensorGaussianNodes I degree n v g (some w))) gaussianCoordinates
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (Measure.infinitePi (fun w : ForestVertex n =>
          (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
            Measure (SpinTensorIndex I degree → ℝ))))) := by
  refine ⟨by unfold tensorGaussianNodes tensorStandardGaussianNodes; fun_prop, ?_⟩
  change gaussianCoordinates.map ((fun q : Option (ForestVertex n) → SpinTensorIndex I degree → ℝ =>
      (q none, fun w => q (some w))) ∘ tensorGaussianNodes I degree n v) = _
  rw [← Measure.map_map (by fun_prop) (measurable_tensorGaussianNodes I degree n v),
    (tensorGaussianNodes_measurePreserving I degree n v).map_eq]
  have he := infinitePi_option_split
    (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
    (fun w : ForestVertex n => (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
      Measure (SpinTensorIndex I degree → ℝ)))
  have hc : (fun w : Option (ForestVertex n) => w.elim
      (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
      (fun w => (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
        Measure (SpinTensorIndex I degree → ℝ)))) =
      (fun w => (tensorGaussianLaw I degree (v (nodeAddress n w).length) :
        Measure (SpinTensorIndex I degree → ℝ))) := by
    funext w
    cases w with
    | none => cases n <;> rfl
    | some w => simp only [Option.elim_some, nodeAddress_length_some]
  simpa only [hc] using he

lemma cylinderField_tensorLeaf_nodes {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (σ : Spin N) (leaf : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) (σ, leaf)) g =
      spinTensorEnergy U I degree amplitude (tensorGaussianNodes I degree n v g none) σ +
      ∑ i : Fin n, spinTensorEnergy U I degree amplitude
        (tensorGaussianNodes I degree n v g (some (edgeAt n leaf i))) σ := by
  classical
  have he : cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) (σ, leaf)) g =
      ∑ i : Fin (n + 1), spinTensorEnergy U I degree amplitude
        (tensorGaussianNodes I degree n v g (nodeAt n leaf i)) σ := by
    rw [tensorLeafCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    unfold spinTensorEnergy tensorGaussianNodes tensorStandardGaussianNodes
    rw [nodeAddress_nodeAt_length]
    apply Finset.sum_congr rfl
    intro j _
    rw [tensorNodeTag_nodeAt]
    ring
  rw [he, Fin.sum_univ_succ]
  simp only [nodeAt_zero, nodeAt_succ]

theorem tensorFlatToCoordinates_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToCoordinates I degree n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorCoordinateLaw I degree n b (fun i => v (i + 1)))) := by
  let R := (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
  let T := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := Measure.infinitePi (fun w : ForestVertex n =>
    (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) : Measure (SpinTensorIndex I degree → ℝ)))
  have hswap : MeasurePreserving Prod.swap (T.prod R) (R.prod T) := Measure.measurePreserving_swap
  have hshuffle := (measurePreserving_prodAssoc R T F).comp
    ((hswap.prod (MeasurePreserving.id F)).comp
      ((measurePreserving_prodAssoc T R F).symm MeasurableEquiv.prodAssoc))
  have hprod := (MeasurePreserving.id T).prod (tensorGaussianRootForest_measurePreserving I degree n v)
  convert hshuffle.comp hprod using 1
  all_goals try with_reducible_and_instances rfl
  all_goals rfl

theorem tensorLabeledEnergy_flat_eq {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : LabeledTree n × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) :
    let q := tensorFlatToLabeled U I degree amplitude n v p
    tensorLabeledEnergy eig U c I degree amplitude n q.1 q.2 x =
      rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
        cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) x) p.2 := by
  rw [cylinderField_tensorLeaf_nodes]
  dsimp only [tensorFlatToLabeled, tensorFlatToCoordinates, tensorLabeledEnergy,
    cascadeCoordinateEnergy, tensorSpinBaseEnergy, tensorEnergyCoordinates]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_FullPerturbationCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vanishing cost of both terms of the manuscript perturbation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fullPerturbationCost_tendsto (m : ℕ) :
    Filter.Tendsto (fun N => 2 * m * perturbationScale N + 8 * perturbationScale N ^ 2)
      Filter.atTop (nhds (0 : ℝ)) := by
  simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
    (perturbationScale_tendsto.const_mul (2 * (m : ℝ))).add
      ((perturbationScale_tendsto.pow 2).const_mul 8)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected actual spectral/tree monomial as an independent Gaussian factor. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNamespaceTag_injective {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) : Function.Injective (tensorNamespaceTag I degree) := by
  rintro ⟨i, p, a⟩ ⟨j, q, b⟩ h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      cases he
      rfl
    | inr b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
  | inr a =>
    cases b with
    | inl b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
    | inr b =>
      rcases a with ⟨a, s⟩
      rcases b with ⟨b, t⟩
      have hp := Nat.pair_eq_pair.mp h
      have hab : a = b := Fin.ext (Nat.add_right_cancel hp.1)
      subst b
      have he := Encodable.encode_inj.mp hp.2
      cases he
      rfl

/-- Injective Gaussian reindexing identifies the entire countable
spin/leaf field law with the flat tensor model. -/
theorem tensorNamespacedFields_law {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) :
    gaussianCoordinates.map (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) := by
  let Φ := fun (G : TensorGaussianKey I degree → ℝ) (x : Spin N × LabeledLeaf n) =>
    ∑ i : Fin (n + 1), ∑ a : SpinTensorIndex I degree,
      (NNReal.sqrt (v i a) : ℝ) * spinTensorFeature U I degree amplitude x.1 a *
        G (i, (labeledAddress n x.2).take i, a)
  have hmΦ : Measurable Φ := by
    apply Measurable.of_eval
    intro x
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun a _ =>
      (measurable_pi_apply (i.1, (labeledAddress n x.2).take i, a)).const_mul _
  have he : (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q : TensorGaussianKey I degree => g (Encodable.encode q)) := by
    funext g x
    rw [tensorLeafCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hn : (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q => g (tensorNamespaceTag I degree q)) := by
    funext g x
    rw [tensorNamespacedCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hp := gaussian_pullback_measurePreserving
    (Encodable.encode : TensorGaussianKey I degree → ℕ) Encodable.encode_injective
  have hq := gaussian_pullback_measurePreserving
    (tensorNamespaceTag I degree) (tensorNamespaceTag_injective I degree)
  rw [he, hn, ← Measure.map_map hmΦ hp.measurable, ← Measure.map_map hmΦ hq.measurable,
    hp.map_eq, hq.map_eq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorHaarFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Haar, Gaussian-root, and cascade fluctuations for the actual finite tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma measurable_tensorLeafState {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    Measurable (fun p : (SpinTensorIndex I degree → ℝ) × NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      tensorLeafState I degree n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)

lemma measurable_tensorDisorderPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ) :
    Measurable (tensorDisorderPressure eig c I degree amplitude n) := by
  let Ω := SpecialOrthogonal N × ((SpinTensorIndex I degree → ℝ) ×
    NoiseTree (SpinTensorIndex I degree → ℝ) n)
  have hs : Measurable (fun p : Ω × NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      (p.1.1, tensorLeafState I degree n p.1.2.1 p.2)) :=
    measurable_fst.fst.prodMk ((measurable_tensorLeafState I degree n).comp
      (measurable_fst.snd.fst.prodMk measurable_snd))
  have ht := ((measurable_spinTensorTerminal_joint eig c I degree amplitude).comp hs).exp
  have hi := (ht.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (noiseLeafKernel (SpinTensorIndex I degree → ℝ) n).comap
      (fun p : Ω => p.2.2) measurable_snd.snd)).measurable.log
  have hlog : Measurable (fun p : Ω => tensorCascadeLog eig (specialRotation p.1) c
      I degree amplitude n p.2.1 p.2.2) := by
    simpa only [tensorCascadeLog, noiseLeafTerminal_spinTensorTerminal, Function.comp_apply,
      Kernel.comap_apply] using hi
  exact hlog.const_mul (N : ℝ)⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFlatLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual flat spin/leaf pressure and marked-cascade pressure have the same law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

theorem tensorFlatToNoise_measurePreserving {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToNoise I degree n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)
      (tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0)) := by
  have hp : MeasurePreserving (fun q : TensorCoordinateData I degree n =>
      labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
        (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2))
      (tensorCoordinateLaw I degree n b (fun i => v (i + 1)))
      (tensorCascadeLaw I degree n b (fun i => v (i + 1))) :=
    ⟨by fun_prop, labeledNoiseCoordinates_law (SpinTensorIndex I degree → ℝ) n b
      (fun i => tensorGaussianLaw I degree (v (i + 1)))⟩
  have h := ((MeasurePreserving.id (tensorGaussianLaw I degree (v 0) :
      Measure (SpinTensorIndex I degree → ℝ))).prod hp).comp
    (tensorFlatToCoordinates_measurePreserving I degree n b v)
  convert (config := {transparency := .instances, preTransparency := .instances}) h using 1
  · rfl
  · rfl

private lemma spinTensorEnergy_labeled {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (G : ForestVertex n → SpinTensorIndex I degree → ℝ) (leaf : LabeledLeaf n) (σ : Spin N) :
    spinTensorEnergy U I degree amplitude
      (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n G) leaf z) σ =
      spinTensorEnergy U I degree amplitude z σ +
        ∑ i : Fin n, spinTensorEnergy U I degree amplitude (G (edgeAt n leaf i)) σ := by
  unfold spinTensorEnergy
  simp only [labeledEnergy_edge_sum, add_mul, Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma tensorCoordinateLog_eq_terminal {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (q : TensorCoordinateData I degree n) :
    Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n z
      (tensorEnergyCoordinates U I degree amplitude n q) x)
      ∂tensorLabeledReference N n (tensorEnergyCoordinates U I degree amplitude n q)) =
      Real.log (∫ leaf, Real.exp (spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2) leaf z))
        ∂labeledLeafLaw n q.1) := by
  let H := tensorSpinBaseEnergy eig U c I degree amplitude z
  let G := markForestOfCoords (Spin N → ℝ) n
    (fun w => spinTensorEnergy U I degree amplitude (q.2 w))
  have he (x : Spin N × LabeledLeaf n) : tensorLabeledEnergy eig U c I degree amplitude n z
      (tensorEnergyCoordinates U I degree amplitude n q) x = labeledEnergy n G x.2 H x.1 := by
    rw [labeledEnergy_edge_sum]
    rfl
  simp_rw [he]
  change labeledEnergyLog n (uniformSpinPrior N : Measure (Spin N)) H (q.1, G) = _
  rw [labeledEnergyLog_eq_leaf]
  apply congrArg Real.log
  apply integral_congr_ae
  refine ae_of_all _ fun leaf => ?_
  apply congrArg Real.exp
  rw [finiteLogIntegral_uniformSpinPrior]
  unfold spinTensorTerminal
  congr 1
  funext σ
  rw [spinTensorEnergy_labeled, labeledEnergy_edge_sum]
  change (rotatedEnergy eig U σ + fieldEnergy c σ + spinTensorEnergy U I degree amplitude z σ) + _ = _
  ring

/-- On every good marked tree the coordinate partition is exactly the
actual marked-cascade partition, uniformly in its rotation and root mark. -/
theorem tensorCoordinateLog_eq_noise {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (q : TensorCoordinateData I degree n)
    (hg : GoodNoiseTree (SpinTensorIndex I degree → ℝ) n
      (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
        (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)))
    (ht : 0 < noiseTreeTotal (SpinTensorIndex I degree → ℝ) n
        (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
          (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)) ∧
      noiseTreeTotal (SpinTensorIndex I degree → ℝ) n
        (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
          (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)) < ∞) :
    Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n z
      (tensorEnergyCoordinates U I degree amplitude n q) x)
      ∂tensorLabeledReference N n (tensorEnergyCoordinates U I degree amplitude n q)) =
      tensorCascadeLog eig U c I degree amplitude n z
        (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
          (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)) := by
  rw [tensorCoordinateLog_eq_terminal]
  have he := labeled_terminal_integral n q.1
    (markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2) hg ht
    (X := fun _ => spinTensorTerminal eig U c I degree amplitude) (u := fun _ p => p.1 + p.2)
    (fun _ => measurable_spinTensorTerminal eig U c I degree amplitude)
    (fun _ => measurable_fst.add measurable_snd) z
  simp only [labeledEnergy_terminal] at he
  exact congrArg Real.log he


/-- The good-tree event is independent of the terminal energy, so this
identity holds simultaneously for every rotation on one full-measure set. -/
theorem tensorFlatLog_eq_noise_ae {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (hb : CascadeExponents n b) :
    ∀ᵐ p : LabeledTree n × (ℕ → ℝ)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates,
      ∀ U : Rotation N, tensorFlatLog eig U c I degree amplitude n v p =
        tensorCascadeLog eig U c I degree amplitude n (tensorFlatToNoise I degree n v p).1
          (tensorFlatToNoise I degree n v p).2 := by
  let M := (SpinTensorIndex I degree → ℝ)
  let ν := fun i => tensorGaussianLaw I degree (v (i + 1))
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b (fun i => v (i + 1))) :=
    (noiseCascadeLaw M n b ν).prop
  have hp := tensorFlatToNoise_measurePreserving I degree n b v
  have hg : ∀ᵐ T ∂tensorCascadeLaw I degree n b (fun i => v (i + 1)), GoodNoiseTree M n T :=
    noiseCascade_good M n b hb ν
  have ht : ∀ᵐ T ∂tensorCascadeLaw I degree n b (fun i => v (i + 1)),
      0 < noiseTreeTotal M n T ∧ noiseTreeTotal M n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget M n).aemeasurable
    change ∀ᵐ T : RawTree n ∂(noiseCascadeLaw M n b ν : Measure (NoiseTree M n)).map
      (noiseTreeForget M n), 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  have hproj := measurePreserving_snd (μ := (tensorGaussianLaw I degree (v 0) : Measure M))
    (ν := tensorCascadeLaw I degree n b (fun i => v (i + 1)))
  have hg' := hp.quasiMeasurePreserving.ae (hproj.quasiMeasurePreserving.ae hg)
  have ht' := hp.quasiMeasurePreserving.ae (hproj.quasiMeasurePreserving.ae ht)
  filter_upwards [hg', ht'] with p hgp htp
  intro U
  let q := tensorFlatToCoordinates I degree n v p
  have he : tensorFlatLog eig U c I degree amplitude n v p =
      Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n q.1
        (tensorEnergyCoordinates U I degree amplitude n q.2) x)
        ∂tensorLabeledReference N n (tensorEnergyCoordinates U I degree amplitude n q.2)) := by
    apply congrArg Real.log
    apply integral_congr_ae
    exact ae_of_all _ fun x => congrArg Real.exp
      (tensorLabeledEnergy_flat_eq eig U c I degree amplitude n v p x).symm
  exact he.trans (tensorCoordinateLog_eq_noise eig U c I degree amplitude n q.1 q.2 hgp htp)

theorem tensorFlatToDisorder_measurePreserving {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToDisorder I degree n v)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
      (μ.prod (tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0))) := by
  have hp := ((MeasurePreserving.id μ).prod
    (tensorFlatToNoise_measurePreserving I degree n b v)).comp
    (measurePreserving_prodAssoc μ (labeledCascadeLaw n b : Measure (LabeledTree n)) gaussianCoordinates)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  rfl

/-- Exact almost-everywhere pressure identification with the actual
three-disorder model, suitable for transporting moments and variance. -/
theorem tensorFlatPressure_eq_disorder_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (hb : CascadeExponents n b) :
    (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      (N : ℝ)⁻¹ * tensorFlatLog eig (specialRotation p.1.1) c I degree amplitude n v (p.1.2, p.2)) =ᵐ[
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates]
    (tensorDisorderPressure eig c I degree amplitude n ∘ tensorFlatToDisorder I degree n v) := by
  have hproj := (measurePreserving_snd (μ := μ)
    (ν := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)).comp
    (measurePreserving_prodAssoc μ (labeledCascadeLaw n b : Measure (LabeledTree n)) gaussianCoordinates)
  have he := hproj.quasiMeasurePreserving.ae (tensorFlatLog_eq_noise_ae eig c I degree amplitude n b v hb)
  filter_upwards [he] with p hp
  exact congrArg ((N : ℝ)⁻¹ * ·) (hp (specialRotation p.1.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozenFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the actual three-disorder pressure moments to one frozen Gaussian CGF. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

private lemma joint_map_eq_of_conditional_map_eq {Ω G E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure G) [SFinite Q]
    (f g : Ω × G → E) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ ω, Q.map (fun z => f (ω, z)) = Q.map (fun z => g (ω, z))) :
    (P.prod Q).map f = (P.prod Q).map g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply (hf hs), Measure.prod_apply (hg hs)]
  apply lintegral_congr_ae
  refine ae_of_all P fun ω => ?_
  have h := congrArg (fun ν : Measure E => ν s) (he ω)
  have hfω : Measurable (fun z => f (ω, z)) := hf.comp (measurable_const.prodMk measurable_id)
  have hgω : Measurable (fun z => g (ω, z)) := hg.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hfω hs, Measure.map_apply hgω hs] at h
  exact h

private lemma tensorNamespacedLog_conditional_law {N m k : ℕ} (eig c : Fin N → ℝ)
    (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (T : LabeledTree n) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    gaussianCoordinates.map (fun g => tensorFlatLog eig (specialRotation U) c I degree amplitude n
      (tensorPathProfile I degree n treeDegree h) (T, g)) =
    gaussianCoordinates.map (fun g => tensorNamespacedLog eig c I degree amplitude n treeDegree h ((U, T), g)) := by
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
  let H := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1
  let K := fun F : Spin N × LabeledLeaf n → ℝ => Real.log (∫ x, Real.exp (H x + F x) ∂ν)
  have : ∀ F : (Spin N × LabeledLeaf n → ℝ), IsProbabilityMeasure ((fun _ => ν) F) :=
    fun _ => by
      change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hE : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) × (Spin N × LabeledLeaf n) => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hc : Measurable (fun _ : Spin N × LabeledLeaf n → ℝ => H x) := measurable_const
    exact hc.add (measurable_pi_apply x)
  have hK : Measurable K := (measurable_random_referencePartition
    (ν := fun _ : Spin N × LabeledLeaf n → ℝ => ν) measurable_const hE).log
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hleft : Measurable (fun g x => cylinderField
      (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) g) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  have hright : Measurable (fun g x => cylinderField
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) g) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  change gaussianCoordinates.map (K ∘ (fun g x => cylinderField
      (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) g)) =
    gaussianCoordinates.map (K ∘ (fun g x => cylinderField
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) g))
  rw [← Measure.map_map hK hleft, ← Measure.map_map hK hright, tensorNamespacedFields_law]

private lemma measurable_tensorLeafField_joint {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (tensorLeafCoefficients (specialRotation p.1) I degree amplitude n v x) p.2) := by
  simp only [tensorLeafCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_spinTensorFeature I degree amplitude x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag n x.2 i)).comp measurable_snd)

private lemma measurable_tensorJointLog {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (Y : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) × (Spin N × LabeledLeaf n)) → ℝ)
    (hY : Measurable Y) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      Real.log (∫ x : Spin N × LabeledLeaf n,
        Real.exp (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 + Y (p, x))
        ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)) := by
  have hbase : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) => rotatedEnergy eig (specialRotation p.1.1.1) p.2.1 + fieldEnergy c p.2.1) := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
      unfold rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
    exact (hr.comp measurable_fst.fst).add_const (fieldEnergy c x.1)
  let ν := fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact (measurable_random_referencePartition (ν := ν)
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd)
    (hbase.add hY)).log

lemma measurable_tensorNamespacedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (tensorNamespacedLog eig c I degree amplitude n treeDegree h) := by
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hY : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amplitude n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hp : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
        (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
    convert (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp hp using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact measurable_tensorJointLog eig c n _ hY

private lemma measurable_tensorJointFlatLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      tensorFlatLog eig (specialRotation p.1.1) c I degree amplitude n
        (tensorPathProfile I degree n treeDegree h) (p.1.2, p.2)) := by
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hY : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorLeafCoefficients (specialRotation p.1.1.1) I degree amplitude n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hp : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
        (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
    convert (measurable_tensorLeafField_joint I degree amplitude n v x).comp hp using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact measurable_tensorJointLog eig c n _ hY

/-- The tensor pressure has the marked-cascade pressure law,
including the Haar rotation. This is a law identity, stronger than matching means. -/
theorem tensorNamespacedPressure_law {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hb : CascadeExponents n b) :
    HasLaw (tensorNamespacedPressure eig c I degree amplitude n treeDegree h)
      ((μ.prod (tensorRootTreeLaw I degree n b
        (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
        (tensorPathProfile I degree n treeDegree h 0))).map
          (tensorDisorderPressure eig c I degree amplitude n))
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  let P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
    tensorFlatLog eig (specialRotation p.1.1) c I degree amplitude n
      (tensorPathProfile I degree n treeDegree h) (p.1.2, p.2)
  let G := tensorNamespacedLog eig c I degree amplitude n treeDegree h
  have hF : Measurable F := measurable_tensorJointFlatLog eig c I degree amplitude n treeDegree h
  have hG : Measurable G := measurable_tensorNamespacedLog eig c I degree amplitude n treeDegree h
  have he : (P.prod gaussianCoordinates).map F = (P.prod gaussianCoordinates).map G :=
    joint_map_eq_of_conditional_map_eq P gaussianCoordinates F G hF hG
      (fun ω => tensorNamespacedLog_conditional_law eig c ω.1 I degree amplitude n ω.2 treeDegree h)
  let S := fun x : ℝ => (N : ℝ)⁻¹ * x
  have hS : Measurable S := measurable_id.const_mul _
  have hes : (P.prod gaussianCoordinates).map (S ∘ F) = (P.prod gaussianCoordinates).map (S ∘ G) := by
    rw [← Measure.map_map hS hF, ← Measure.map_map hS hG, he]
  have hactual := (hasLaw_map (measurable_tensorDisorderPressure eig c I degree amplitude n).aemeasurable).comp
    (tensorFlatToDisorder_measurePreserving μ I degree n b (tensorPathProfile I degree n treeDegree h)).hasLaw
  have hflat := hactual.congr (tensorFlatPressure_eq_disorder_ae μ eig c I degree amplitude n b
    (tensorPathProfile I degree n treeDegree h) hb)
  refine ⟨(hG.const_mul (N : ℝ)⁻¹).aemeasurable, ?_⟩
  exact hes.symm.trans hflat.map_eq

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorMinimumPenalty
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual minimizing objective has a vanishing penalty whenever its
pressure has a uniform vanishing perturbation cost. Its negative minimum
is the scalar pressure envelope used in the cavity telescoping argument. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma tensorMinimumPenalty_nonneg {N m : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) :
    0 ≤ tensorMinimumPenalty u v :=
  add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (perturbationWeight_nonneg j)
    (sq_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma tensorMinimumPenalty_center (N m : ℕ) :
    tensorMinimumPenalty (fun _ : Fin N => (3 : ℝ)/2) (fun _ : Fin m => (3 : ℝ)/2) = 0 := by
  simp [tensorMinimumPenalty]

lemma tensorPerturbationObjective_eq {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) :
    tensorPerturbationObjective μ eig c I t n b h u v =
      -tensorPerturbationPressureMean μ eig c I u v t n b h + tensorMinimumPenalty u v := by
  unfold tensorPerturbationObjective tensorMinimumPenalty
  ring

/-- A genuine minimum lies within the same uniform cost of the base pressure,
and its quadratic penalty is at most twice that cost. -/
theorem tensor_minimum_envelope_cost {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (t : ℝ) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eig c I t n b h u v ≤
        tensorPerturbationObjective μ eig c I t n b h u' v')
    (P δ : ℝ)
    (hcost : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      |tensorPerturbationPressureMean μ eig c I u' v' t n b h - P| ≤ δ) :
    |(-tensorPerturbationObjective μ eig c I t n b h u v) - P| ≤ δ ∧
      tensorMinimumPenalty u v ≤ 2 * δ := by
  have hcenter : ∀ j : Fin N, (3 : ℝ)/2 ∈ Set.Icc (1 : ℝ) 2 := fun _ => by norm_num
  have hcenter' : ∀ a : Fin m, (3 : ℝ)/2 ∈ Set.Icc (1 : ℝ) 2 := fun _ => by norm_num
  have hc := abs_le.mp (hcost _ _ hcenter hcenter')
  have hp := abs_le.mp (hcost u v hu hv)
  have hm := hmin _ _ hcenter hcenter'
  rw [tensorPerturbationObjective_eq, tensorPerturbationObjective_eq,
    tensorMinimumPenalty_center] at hm
  have hn := tensorMinimumPenalty_nonneg u v
  rw [tensorPerturbationObjective_eq]
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-volume perturbation minimizers provide exactly the natural-index
amplitudes used in the physical cavity model. The unused coordinates are one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityBaseAmplitude_fin {N : ℕ} (u : Fin N → ℝ) (j : Fin N) :
    cavityBaseAmplitude u j = u j := by
  simp only [cavityBaseAmplitude, dite_eq_left j.isLt]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAmplitudePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending a finite minimizing perturbation by the physical convention
adds only an exponentially small tail to its quadratic penalty. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityBaseAmplitude_mem {N : ℕ} (u : Fin N → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (j : ℕ) :
    cavityBaseAmplitude u j ∈ Set.Icc (1 : ℝ) 2 := by
  unfold cavityBaseAmplitude
  split_ifs with hj
  · exact hu ⟨j,hj⟩
  · norm_num

lemma cavityBaseAmplitude_penalty {N m n : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) :
    tensorMinimumPenalty (fun j : Fin (N+n) => cavityBaseAmplitude u j) v =
      tensorMinimumPenalty u v + (1/4:ℝ)*((1/2:ℝ)^N-(1/2:ℝ)^(N+n)) := by
  have hleft : (∑ j : Fin N, perturbationWeight j *
      (cavityBaseAmplitude u j - 3/2)^2) =
      ∑ j : Fin N, perturbationWeight j * (u j-3/2)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [cavityBaseAmplitude_fin]
  have hright : (∑ j : Fin n, perturbationWeight (Fin.natAdd N j) *
      (cavityBaseAmplitude u (Fin.natAdd N j) - 3/2)^2) =
      (1/4:ℝ) * ∑ j : Fin n, perturbationWeight (Fin.natAdd N j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj : ¬(Fin.natAdd N j).val<N := by simp only [Fin.val_natAdd]; omega
    simp only [cavityBaseAmplitude, dite_eq_right hj]
    ring
  have hweight : (∑ j : Fin n, perturbationWeight (Fin.natAdd N j)) =
      (1/2:ℝ)^N-(1/2:ℝ)^(N+n) := by
    have hs := perturbationWeight_sum (N+n)
    rw [Fin.sum_univ_add] at hs
    have hl : (∑ j : Fin N, perturbationWeight (Fin.castAdd n j)) =
        1-(1/2:ℝ)^N := by simpa only [Fin.val_castAdd] using perturbationWeight_sum N
    rw [hl] at hs
    linarith
  unfold tensorMinimumPenalty
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd]
  rw [hleft, hright, hweight]
  ring

lemma cavityBaseAmplitude_penalty_le {N m n : ℕ} (u : Fin N → ℝ) (v : Fin m → ℝ) :
    tensorMinimumPenalty (fun j : Fin (N+n) => cavityBaseAmplitude u j) v ≤
      tensorMinimumPenalty u v + (1/4:ℝ)*(1/2:ℝ)^N := by
  rw [cavityBaseAmplitude_penalty]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) (N+n)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorMinimumIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual minimum envelopes satisfy the physical finite-volume pressure
increment inequality, with only the vanishing quadratic penalty loss. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensor_minimum_increment {N n m depth : ℕ}
    (μ : Measure (SpecialOrthogonal (N+n))) (ν : Measure (SpecialOrthogonal N))
    (eigF cF : Fin (N+n) → ℝ) (eigB cB : Fin N → ℝ)
    (IF : Fin m → Finset (Fin (N+n))) (IB : Fin m → Finset (Fin N))
    (t : ℝ) (b h : ℕ → ℝ) (uF : Fin (N+n) → ℝ) (vF : Fin m → ℝ)
    (uB : Fin N → ℝ) (vB : Fin m → ℝ)
    (huB : ∀ j, uB j ∈ Set.Icc (1 : ℝ) 2) (hvB : ∀ a, vB a ∈ Set.Icc (1 : ℝ) 2)
    (hminF : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eigF cF IF t depth b h uF vF ≤
        tensorPerturbationObjective μ eigF cF IF t depth b h u' v') :
    let uE := fun j : Fin (N+n) => cavityBaseAmplitude uB j;
    -(N+n : ℝ)*tensorPerturbationObjective μ eigF cF IF t depth b h uF vF +
      (N : ℝ)*tensorPerturbationObjective ν eigB cB IB t depth b h uB vB ≥
    ((N+n : ℝ)*tensorPerturbationPressureMean μ eigF cF IF uE vB t depth b h -
      (N : ℝ)*tensorPerturbationPressureMean ν eigB cB IB uB vB t depth b h) -
      (n : ℝ)*tensorMinimumPenalty uB vB - (N+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^N := by
  intro uE
  have hm := hminF uE vB (fun j => cavityBaseAmplitude_mem uB huB j) hvB
  simp only [tensorPerturbationObjective_eq] at hm
  have hp := cavityBaseAmplitude_penalty_le (n := n) uB vB
  have hscale := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ)≤N+n)
  have hpscale := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤N+n)
  simp only [tensorPerturbationObjective_eq]
  dsimp only [uE] at hscale ⊢
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTemperatureModulus
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform temperature continuity of the enriched pressure and its
identity with the pressure under the original disorder law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorNamespacedMeanPressure_eq_disorder {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hb : CascadeExponents n b) :
    tensorNamespacedMeanPressure μ eig c I degree amp n b r h =
      (∫ p, tensorDisorderPressure eig c I degree amp n p
        ∂μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1))
          (tensorPathProfile I degree n r h 0))) - h n / 2 := by
  have hlaw := tensorNamespacedPressure_law μ eig c I degree amp n b r h hb
  unfold tensorNamespacedMeanPressure
  exact congrArg (fun x => x - h n / 2) (hlaw.integral_eq.trans
    (integral_map (measurable_tensorDisorderPressure eig c I degree amp n).aemeasurable
      aestronglyMeasurable_id))

lemma tensorNamespacedMeanPressure_eq_perturbation {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (hb : CascadeExponents n b) :
    tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
      (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
      n b (fun j => enumeratedTreeDegree m j) h =
      tensorPerturbationPressureMean μ eig c I u v t n b h - h n / 2 :=
  tensorNamespacedMeanPressure_eq_disorder μ _ c I _ _ n b _ h hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorZeroAmplitude
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing zero-amplitude tensor marks

Projection onto the site coordinates sends the tensor Gaussian product law
to the original site-field law.  This identifies the actual zero-amplitude
cascade pressure with the unperturbed rotated enriched pressure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorSiteProjection_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) (site : ℝ≥0)
    (hv : ∀ i, v (Sum.inl i) = site) :
    MeasurePreserving (tensorSiteProjection I degree)
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ))
      (vectorGaussianLaw N site : Measure (Fin N → ℝ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i))
  have hfst := measurePreserving_fst
    (μ := Measure.pi (fun i : Fin N => gaussianReal 0 (v (Sum.inl i))))
    (ν := Measure.pi (fun j : Sigma (fun j : Fin k => SpectralTensorIndex I (degree j)) =>
      gaussianReal 0 (v (Sum.inr j))))
  have h := hfst.comp hsplit
  change MeasurePreserving (tensorSiteProjection I degree)
    (Measure.pi (fun i => gaussianReal 0 (v i)))
    (Measure.pi (fun i : Fin N => gaussianReal 0 site))
  change MeasurePreserving (tensorSiteProjection I degree)
    (Measure.pi (fun i => gaussianReal 0 (v i)))
    (Measure.pi (fun i : Fin N => gaussianReal 0 (v (Sum.inl i)))) at h
  simpa only [hv] using h

lemma spinTensorEnergy_zero_amplitude {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (z : SpinTensorIndex I degree → ℝ) (σ : Spin N) :
    spinTensorEnergy U I degree (fun _ => 0) z σ =
      fieldEnergy (tensorSiteProjection I degree z) σ := by
  classical
  simp only [spinTensorEnergy, Fintype.sum_sum_type, spinTensorFeature, zero_mul,
    mul_zero, Finset.sum_const_zero, add_zero, tensorSiteProjection, fieldEnergy]

lemma spinTensorTerminal_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (z : SpinTensorIndex I degree → ℝ) :
    spinTensorTerminal eig U c I degree (fun _ => 0) z =
      rotatedFieldTerminal eig U c (tensorSiteProjection I degree z) := by
  unfold spinTensorTerminal rotatedFieldTerminal
  congr 1
  funext σ
  rw [spinTensorEnergy_zero_amplitude]
  simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- Zero-amplitude tensor coordinates disappear at every Gaussian recursion
step, irrespective of their unused variances. -/
theorem tensorCascadeValue_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (site : ℕ → ℝ≥0) (hv : ∀ j i, v j (Sum.inl i) = site j)
    (z : SpinTensorIndex I degree → ℝ) :
    tensorCascadeValue eig U c I degree (fun _ => 0) n b v z =
      rotatedCascadeValue n b site eig U c (tensorSiteProjection I degree z) := by
  induction n generalizing b v site z with
  | zero => exact spinTensorTerminal_zero_amplitude eig U c I degree z
  | succ n ih =>
    let F := rotatedCascadeValue n (fun j => b (j + 1)) (fun j => site (j + 1)) eig U c
    have hF : Measurable F :=
      measurable_cascadeRecursion n (fun j => b (j + 1))
        (fun j => vectorGaussianLaw N (site (j + 1)))
        (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
    have hE : Measurable (fun w : Fin N → ℝ =>
        Real.exp (b 0 * F (tensorSiteProjection I degree z + w))) :=
      ((hF.comp (measurable_const.add measurable_id)).const_mul (b 0)).exp
    have hm := tensorSiteProjection_measurePreserving I degree (v 0) (site 0) (hv 0)
    change logMean (b 0) (tensorGaussianLaw I degree (v 0) : Measure _)
        (fun w => tensorCascadeValue eig U c I degree (fun _ => 0) n
          (fun j => b (j + 1)) (fun j => v (j + 1)) (z + w)) =
      logMean (b 0) (vectorGaussianLaw N (site 0) : Measure _)
        (fun w => F (tensorSiteProjection I degree z + w))
    unfold logMean
    congr 1
    congr 1
    calc
      _ = ∫ w : SpinTensorIndex I degree → ℝ,
          Real.exp (b 0 * F (tensorSiteProjection I degree z + tensorSiteProjection I degree w))
          ∂(tensorGaussianLaw I degree (v 0) : Measure _) := by
        apply integral_congr_ae
        refine ae_of_all _ fun w => ?_
        dsimp only
        rw [ih (fun j => b (j + 1)) (fun j => v (j + 1))
          (fun j => site (j + 1)) (fun j i => hv (j + 1) i)]
        rfl
      _ = _ := hm.hasLaw.integral_comp hE.aestronglyMeasurable

/-- The exact unperturbed enriched-pressure identity used at temperature zero. -/
theorem tensorEnrichedPressure_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (site : ℕ → ℝ≥0) (hv : ∀ j i, v j (Sum.inl i) = site j)
    (root : SpinTensorIndex I degree → ℝ≥0) (rootSite : ℝ≥0)
    (hroot : ∀ i, root (Sum.inl i) = rootSite) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b v root =
      rotatedEnrichedPressure n b site rootSite eig U c := by
  unfold tensorEnrichedPressure rotatedEnrichedPressure
  congr 1
  have hF : Measurable (rotatedCascadeValue n b site eig U c) :=
    measurable_cascadeRecursion n b (fun j => vectorGaussianLaw N (site j))
      (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
  calc
    _ = ∫ z : SpinTensorIndex I degree → ℝ,
        rotatedCascadeValue n b site eig U c (tensorSiteProjection I degree z)
        ∂(tensorGaussianLaw I degree root : Measure _) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => tensorCascadeValue_zero_amplitude eig U c I degree n b v site hv z
    _ = _ := (tensorSiteProjection_measurePreserving I degree root rootSite hroot).hasLaw.integral_comp
      hF.aestronglyMeasurable

/-- The manuscript profile retains precisely the original linear-field
increments when the monomial amplitudes vanish. -/
theorem tensorPathPressure_zero_amplitude {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b
      (fun i => tensorPathProfile I degree n treeDegree h (i + 1))
      (tensorPathProfile I degree n treeDegree h 0) =
    rotatedEnrichedPressure n b (fun i => varianceIncrement h (i + 1))
      (varianceIncrement h 0) eig U c :=
  tensorEnrichedPressure_zero_amplitude eig U c I degree n b _ _
    (fun _ _ => rfl) _ _ (fun _ => rfl)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorZeroFieldPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! With both the linear-field heights and the monomial amplitudes zero,
the cascade leaves the original finite Ising pressure unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma vectorGaussianLaw_zero_ae (N : ℕ) :
    ∀ᵐ z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)), z = 0 := by
  have hi (i : Fin N) :
      ∀ᵐ z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)), z i = 0 := by
    have hz : ∀ᵐ x ∂gaussianReal 0 0, x = 0 := by
      simp [gaussianReal_zero_var, ae_dirac_eq]
    exact (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 0) i).quasiMeasurePreserving.ae hz
  filter_upwards [ae_all_iff.mpr hi] with z hz
  funext i
  exact hz i

lemma integral_vectorGaussianLaw_zero {N : ℕ} (F : (Fin N → ℝ) → ℝ) :
    (∫ z, F z ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ))) = F 0 := by
  calc
    _ = ∫ _ : Fin N → ℝ, F 0 ∂(vectorGaussianLaw N 0 : Measure (Fin N → ℝ)) := by
      apply integral_congr_ae
      filter_upwards [vectorGaussianLaw_zero_ae N] with z hz
      rw [hz]
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

lemma logMean_vectorGaussianLaw_zero {N : ℕ} {b : ℝ} (hb : b ≠ 0)
    (F : (Fin N → ℝ) → ℝ) :
    logMean b (vectorGaussianLaw N 0 : Measure (Fin N → ℝ)) F = F 0 := by
  unfold logMean
  rw [integral_vectorGaussianLaw_zero, Real.log_exp]
  exact mul_div_cancel_left₀ (F 0) hb

lemma rotatedCascadeValue_zero_variance {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (eig : Fin N → ℝ) (U : Rotation N)
    (c z : Fin N → ℝ) :
    rotatedCascadeValue n b (fun _ => 0) eig U c z = rotatedFieldTerminal eig U c z := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change logMean (b 0) (vectorGaussianLaw N 0 : Measure (Fin N → ℝ))
      (fun w => rotatedCascadeValue n (fun i => b (i + 1)) (fun _ => 0) eig U c (z + w)) = _
    rw [logMean_vectorGaussianLaw_zero (hb.1 0 (by omega)).1.ne']
    simpa only [add_zero] using ih (fun i => b (i + 1)) hb.tail

lemma rotatedEnrichedPressure_zero_variance {N : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) :
    rotatedEnrichedPressure n b (fun _ => 0) 0 eig U c = rotatedPressure eig U c := by
  unfold rotatedEnrichedPressure
  rw [integral_vectorGaussianLaw_zero, rotatedCascadeValue_zero_variance n b hb]
  simp only [rotatedPressure, rotatedFieldTerminal, add_zero]

lemma varianceIncrement_zero_path (i : ℕ) : varianceIncrement (fun _ => 0) i = 0 := by
  cases i <;> simp [varianceIncrement, pathIncrement]

/-- The exact unperturbed pressure at zero field height, including the root. -/
theorem tensorPathPressure_zero_field {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (r : Fin k → ℕ) :
    tensorEnrichedPressure eig U c I degree (fun _ => 0) n b
      (fun i => tensorPathProfile I degree n r (fun _ => 0) (i + 1))
      (tensorPathProfile I degree n r (fun _ => 0) 0) = rotatedPressure eig U c := by
  rw [tensorPathPressure_zero_amplitude]
  simp_rw [varianceIncrement_zero_path]
  exact rotatedEnrichedPressure_zero_variance n b hb eig U c

/-- At zero random-field height the centered actual pressure differs from
the ordinary Haar-mean pressure only by the established perturbation cost. -/
theorem tensorNamespacedMeanPressure_zero_field_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ 2)
    (t : ℝ) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    |tensorNamespacedMeanPressure μ (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) (fun _ => 0) -
      ∫ U : SpecialOrthogonal N, rotatedPressure (fun i => t * eig i) (specialRotation U) c ∂μ| ≤
      2 * m * perturbationScale N + 8 * perturbationScale N ^ 2 := by
  have h := tensorNamespacedMeanPressure_perturbation_cost hhaar hgauss hN μ hμ eig c I
    u hu v hv t n b (fun _ => 0) hb monotone_const (by rfl)
  have hbase (U : SpecialOrthogonal N) :
      tensorEnrichedPressure (fun i => t * eig i) (specialRotation U) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) 0 n b
        (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (fun _ => 0) (i + 1))
        (tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j)
          n (fun j => enumeratedTreeDegree m j) (fun _ => 0) 0) =
      rotatedPressure (fun i => t * eig i) (specialRotation U) c := by
    exact tensorPathPressure_zero_field (fun i => t * eig i) (specialRotation U) c I
      (fun j : Fin N => enumeratedSpectralDegree m j) n b hb (fun j => enumeratedTreeDegree m j)
  simp_rw [hbase] at h
  simpa only [zero_div, sub_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorMinimumPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual zero-field perturbation minima approximate the unperturbed Haar
pressure, with a uniform cost independent of the auxiliary cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem tensor_zero_field_minimum_cost
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {N m : ℕ} (hN : 3≤N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (hμ : μ.IsMulLeftInvariant)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (t : ℝ) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective μ eig c I t n b (fun _ => 0) u v ≤
        tensorPerturbationObjective μ eig c I t n b (fun _ => 0) u' v') :
    |(-tensorPerturbationObjective μ eig c I t n b (fun _ => 0) u v) -
      ∫ U, rotatedPressure (fun i => t*eig i) (specialRotation U) c ∂μ| ≤
        2*m*perturbationScale N+8*perturbationScale N^2 ∧
    tensorMinimumPenalty u v ≤ 2*(2*m*perturbationScale N+8*perturbationScale N^2) := by
  apply tensor_minimum_envelope_cost μ eig c I t n b (fun _ => 0) u v hu hv hmin
  intro u' v' hu' hv'
  have hua : ∀ j, |u' j|≤2 := fun j => abs_le.mpr ⟨by linarith [(hu' j).1], (hu' j).2⟩
  have hva : ∀ a, |v' a|≤2 := fun a => abs_le.mpr ⟨by linarith [(hv' a).1], (hv' a).2⟩
  have hc := tensorNamespacedMeanPressure_zero_field_cost hhaar hgauss hN μ hμ eig c I
    u' hua v' hva t n b hb
  rw [tensorNamespacedMeanPressure_eq_perturbation μ eig c I u' v' t n b (fun _ => 0) hb] at hc
  simpa only [zero_div, sub_zero] using hc

/-- Both errors vanish along any diverging sequence of physical dimensions.
No fixed-depth assumption is required. -/
theorem tensor_zero_field_minimum_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ r, 3≤N r) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (r : ℕ) → Measure (SpecialOrthogonal (N r))) [∀ r, IsProbabilityMeasure (μ r)]
    (hμ : ∀ r, (μ r).IsMulLeftInvariant)
    (eig c : (r : ℕ) → Fin (N r) → ℝ) (I : (r : ℕ) → Fin m → Finset (Fin (N r)))
    (t : ℕ → ℝ) (n : ℕ → ℕ) (b : ℕ → ℕ → ℝ) (hb : ∀ r, CascadeExponents (n r) (b r))
    (u : (r : ℕ) → Fin (N r) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ r) (eig r) (c r) (I r) (t r) (n r) (b r) (fun _ => 0) (u r) (v r) ≤
        tensorPerturbationObjective (μ r) (eig r) (c r) (I r) (t r) (n r) (b r) (fun _ => 0) u' v') :
    Tendsto (fun r => -tensorPerturbationObjective (μ r) (eig r) (c r) (I r) (t r) (n r)
      (b r) (fun _ => 0) (u r) (v r) -
      ∫ U, rotatedPressure (fun i => t r*eig r i) (specialRotation U) (c r) ∂μ r) atTop (𝓝 0) ∧
    Tendsto (fun r => tensorMinimumPenalty (u r) (v r)) atTop (𝓝 0) := by
  have hc r := tensor_zero_field_minimum_cost hhaar hgauss (hN r) (μ r) (hμ r)
    (eig r) (c r) (I r) (t r) (n r) (b r) (hb r) (u r) (v r) (hu r) (hv r) (hmin r)
  have hδ := (fullPerturbationCost_tendsto m).comp hNlim
  constructor
  · exact squeeze_zero_norm (fun r => by simpa only [Real.norm_eq_abs, Function.comp_def] using (hc r).1) hδ
  · apply squeeze_zero (fun r => tensorMinimumPenalty_nonneg (u r) (v r))
      (fun r => (hc r).2)
    simpa only [mul_zero, Function.comp_def] using hδ.const_mul 2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTelescoping
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final arithmetic-progression telescoping step in the cavity lower
bound, with an eventual increment bound and the actual terminal dimension. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_progression_pressure_lower (A : ℕ → ℝ) (N₀ step L : ℝ)
    (hN₀ : 0 < N₀) (hstep : 0 < step)
    (hinc : ∀ ε > 0, ∀ᶠ n in atTop, step * (L - ε) ≤ A (n + 1) - A n) :
    ∀ ε > 0, ∀ᶠ n in atTop, L - ε ≤ A n / (N₀ + step * n) := by
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hinc (ε / 2) (half_pos hε))
  have hlower : ∀ n, M ≤ n → A M + ((n : ℝ) - M) * step * (L - ε / 2) ≤ A n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hi := hM n hn
      push_cast
      nlinarith
  let D := A M - (M : ℝ) * step * (L - ε / 2) - N₀ * (L - ε)
  have hb : 0 < step * (ε / 2) := mul_pos hstep (half_pos hε)
  have hcast := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (-D / (step * (ε / 2))))
  filter_upwards [eventually_ge_atTop M, hcast] with n hn hlarge
  have hden : 0 < N₀ + step * n := add_pos_of_pos_of_nonneg hN₀ (by positivity)
  apply (le_div_iff₀ hden).mpr
  have hmul := (div_le_iff₀ hb).mp hlarge
  have ha := hlower n hn
  dsimp only [D] at hmul
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityEnvelopeTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A vanishing-error comparison transfers a cavity increment bound through
the scalar pressure envelope and back to the ordinary normalized pressure. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_envelope_progression_lower
    (A P Δ err : ℕ → ℝ) (N₀ step L : ℝ) (hN₀ : 0<N₀) (hstep : 0 < step)
    (hclose : Tendsto (fun r => A r/(N₀+step*r)-P r) atTop (𝓝 0))
    (herr : Tendsto err atTop (𝓝 0))
    (hinc : ∀ r, Δ r-step*err r ≤ A (r+1)-A r)
    (hlower : ∀ ε>0, ∀ᶠ r in atTop, L-ε≤Δ r/step) :
    ∀ ε>0, ∀ᶠ r in atTop, L-ε≤P r := by
  have hA : ∀ ε>0, ∀ᶠ r in atTop, step*(L-ε)≤A (r+1)-A r := by
    intro ε hε
    have he := herr.eventually (eventually_lt_nhds (half_pos hε))
    filter_upwards [hlower (ε/2) (half_pos hε), he] with r hr he
    have hd := (le_div_iff₀ hstep).mp hr
    have hi := hinc r
    nlinarith
  have htel := cavity_progression_pressure_lower A N₀ step L hN₀ hstep hA
  intro ε hε
  have hc := hclose.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [htel (ε/2) (half_pos hε),hc] with r hr hc
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPenaltyRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The extension penalty is negligible in each fixed-size cavity step. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_extension_penalty_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^N) atTop (𝓝 0) := by
  have hlin : Tendsto (fun N : ℕ => (N : ℝ)*(1/2:ℝ)^N) atTop (𝓝 0) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2:ℝ)) (by norm_num)).tendsto_atTop_zero
  have hgeom : Tendsto (fun N : ℕ => (1/2:ℝ)^N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hh := (hlin.add (hgeom.const_mul (n : ℝ))).const_mul (1/4:ℝ)
  simp only [mul_zero, add_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  ring

lemma cavity_total_minimum_penalty_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (n : ℕ) (p : ℕ → ℝ) (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun r => (n : ℝ)*p r+(N r+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r)) atTop (𝓝 0) := by
  simpa only [mul_zero, add_zero, Function.comp_def] using
    (hp.const_mul (n : ℝ)).add ((cavity_extension_penalty_tendsto n).comp hN)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorEnvelopeLower
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity increment lower bound passes through actual minimizing
pressure envelopes to the ordinary Haar pressure on an arithmetic progression. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem tensor_envelope_pressure_lower_oai
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m depth N₀ n : ℕ) (hN₀ : 3≤N₀) (hn : 0<n)
    (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (u : (N : ℕ) → Fin N → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) (hv : ∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
        (fun _ => 0) (u N) (v N) ≤
      tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v')
    (L : ℝ)
    (hlower : ∀ ε>0, ∀ᶠ r in atTop,
      let N := N₀+n*r
      L-ε ≤ ((N+n : ℝ)*tensorPerturbationPressureMean (μ (N+n)) (eig (N+n)) (c (N+n))
        (I (N+n)) (fun j => cavityBaseAmplitude (u N) j) (v N) 1 depth b (fun _ => 0) -
        (N : ℝ)*tensorPerturbationPressureMean (μ N) (eig N) (c N) (I N)
          (u N) (v N) 1 depth b (fun _ => 0))/(n : ℝ)) :
    ∀ ε>0, ∀ᶠ r in atTop, L-ε ≤
      ∫ U, rotatedPressure (eig (N₀+n*r)) (specialRotation U) (c (N₀+n*r)) ∂μ (N₀+n*r) := by
  let N := fun r => N₀+n*r
  have hN r : 3≤N r := by dsimp only [N]; omega
  have hNlim : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    dsimp only [N]
    change r≤N₀+n*r
    have : r≤n*r := Nat.le_mul_of_pos_left r hn
    omega
  let O := fun k => tensorPerturbationObjective (μ k) (eig k) (c k) (I k) 1 depth b
    (fun _ => 0) (u k) (v k)
  let A := fun r => -(N r : ℝ)*O (N r)
  let P := fun r => ∫ U, rotatedPressure (eig (N r)) (specialRotation U) (c (N r)) ∂μ (N r)
  let Δ := fun r => ((N r+n : ℝ)*tensorPerturbationPressureMean (μ (N r+n)) (eig (N r+n))
      (c (N r+n)) (I (N r+n)) (fun j => cavityBaseAmplitude (u (N r)) j) (v (N r))
      1 depth b (fun _ => 0) - (N r : ℝ)*tensorPerturbationPressureMean (μ (N r))
      (eig (N r)) (c (N r)) (I (N r)) (u (N r)) (v (N r)) 1 depth b (fun _ => 0))
  let p := fun r => tensorMinimumPenalty (u (N r)) (v (N r))
  let E := fun r => (n : ℝ)*p r+(N r+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r)
  have hcost := tensor_zero_field_minimum_tendsto hhaar hgauss N hN hNlim m
    (fun r => μ (N r)) (fun r => hμ (N r)) (fun r => eig (N r)) (fun r => c (N r))
    (fun r => I (N r)) (fun _ => 1) (fun _ => depth) (fun _ => b) (fun _ => hb)
    (fun r => u (N r)) (fun r => v (N r)) (fun r => hu (N r)) (fun r => hv (N r))
    (fun r => hmin (N r) (hN r))
  have hclose : Tendsto (fun r => A r/((N₀ : ℝ)+(n : ℝ)*r)-P r) atTop (𝓝 0) := by
    have hz := hcost.1
    simp only [one_mul] at hz
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    have hpos : (N r : ℝ)≠0 := Nat.cast_ne_zero.mpr (by have := hN r; omega)
    have hNr : (N₀ : ℝ)+(n : ℝ)*r=(N r : ℝ) := by simp only [N, Nat.cast_add, Nat.cast_mul]
    rw [hNr]
    dsimp only [A, O, P]
    apply congrArg (fun x : ℝ => x - ∫ U, rotatedPressure (eig (N r))
      (specialRotation U) (c (N r)) ∂μ (N r))
    apply (div_eq_iff hpos).mpr
    ring
  have hE : Tendsto E atTop (𝓝 0) := cavity_total_minimum_penalty_tendsto N hNlim n p hcost.2
  have hinc r : Δ r-(n : ℝ)*(E r/(n : ℝ))≤A (r+1)-A r := by
    have hh := tensor_minimum_increment (depth := depth) (μ (N r+n)) (μ (N r))
      (eig (N r+n)) (c (N r+n)) (eig (N r)) (c (N r)) (I (N r+n)) (I (N r))
      1 b (fun _ => 0) (u (N r+n)) (v (N r+n)) (u (N r)) (v (N r))
      (hu (N r)) (hv (N r)) (hmin (N r+n) (by have := hN r; omega))
    have hsucc : N (r+1)=N r+n := by simp only [N, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    dsimp only [A]
    rw [hsucc, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
    dsimp only [Δ, E, p, O] at *
    simp only [Nat.cast_add] at ⊢
    linarith
  exact cavity_envelope_progression_lower A P Δ (fun r => E r/(n : ℝ)) N₀ n L
    (by exact_mod_cast (show 0<N₀ by omega)) (by exact_mod_cast hn) hclose
    (by simpa only [zero_div] using hE.div_const (n : ℝ)) hinc hlower

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.tensor_envelope_pressure_lower_oai := @OAI.InvariantIsing.tensor_envelope_pressure_lower_oai
