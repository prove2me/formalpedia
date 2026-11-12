-- Prove2me | solution 1 for OAI.InvariantIsing.vectorTerminal_pair_formula
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:32:41.205841+00:00
-- url     : https://prove2.me/submissions/334c8bb4-4c79-42c3-adf9-6bf6c1d516cd

import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

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

omit [Nonempty E] in
lemma measurable_measureRestrict {s : Set E} (hs : MeasurableSet s) :
    Measurable (fun ν : Measure E => ν.restrict s) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)



lemma sigmaPart_eq_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, sigmaPart μ ν = ν := by
  have ha : ∀ n, ∀ᵐ ν ∂poissonLaw μ,
      ν (disjointed (spanningSets μ) n) < ∞ := by
    intro n
    have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
    apply ae_lt_top (Measure.measurable_coe hm)
    rw [poissonLaw_mean_count μ hm]
    exact ((measure_mono (disjointed_subset _ _)).trans_lt
      (measure_spanningSets_lt_top μ n)).ne
  filter_upwards [ae_all_iff.mpr ha] with ν hν
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

omit [Nonempty E] in
lemma measurable_sigmaPart_param (μ : Measure E) [SigmaFinite μ]
    {A : Type*} [MeasurableSpace A] {N : A → Measure E} (hN : Measurable N)
    {F : A × E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂sigmaPart μ (N a)) := by
  simp only [sigmaPart, lintegral_sum_measure]
  apply Measurable.tsum
  intro n
  exact measurable_finitePart_param
    ((measurable_measureRestrict (MeasurableSet.disjointed (measurableSet_spanningSets μ) n)).comp hN) hF

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
-- module Solutions.OAIQ258_II.IsingPerceptron_LintegralGammaKernel
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lintegral Gamma Kernel. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron.Marked

variable {E : Type} [MeasurableSpace E] [Nonempty E]

lemma poissonGood_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, PoissonGood μ ν := by
  rw [show (fun ν => PoissonGood μ ν) =
    (fun ν => ∀ n, ν (disjointed (spanningSets μ) n) < ∞) from rfl, ae_all_iff]
  intro n
  have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
  apply ae_lt_top (Measure.measurable_coe hm)
  rw [poissonLaw_mean_count μ hm]
  exact ((measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)).ne

omit [Nonempty E] in
lemma sigmaPart_eq_of_good (μ : Measure E) [SigmaFinite μ] {ν : Measure E}
    (hν : PoissonGood μ ν) : sigmaPart μ ν = ν := by
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

end IsingPerceptron.Marked

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

namespace IsingPerceptron

lemma measurable_map_sigmaPart_param {E F P : Type*} [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace P] (μ : Measure E) [SigmaFinite μ]
    {N : P → Measure E} (hN : Measurable N) {G : P × E → F} (hG : Measurable G) :
    Measurable (fun p => (sigmaPart μ (N p)).map (fun x => G (p,x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : Measurable (fun p : P × E => s.indicator (1 : F → ℝ≥0∞) (G p)) :=
    (measurable_const.indicator hs).comp hG
  convert measurable_sigmaPart_param μ hN hf using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [Measure.map_apply (f := fun x => G (p,x))
    (hG.comp (measurable_const.prodMk measurable_id)) hs]
  exact (lintegral_indicator_one (hs.preimage
    (hG.comp (measurable_const.prodMk measurable_id)))).symm

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma measurable_noiseTreeDisplace (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeDisplace n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeDisplace
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1,
          noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2))
    have hs : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.1.1) := by fun_prop
    have ha : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.1) := by fun_prop
    have hx : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.1) := by fun_prop
    have hv : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.2) := by fun_prop
    exact (((hc 0).comp (hs.prodMk ha)).mul hx).prodMk
      ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (hs.prodMk ha)).prodMk hv))

end IsingPerceptron

namespace IsingPerceptron

lemma map_powerIntensity_subtree {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) (Q : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    (hm : (∫⁻ a, ENNReal.ofReal (c a ^ b) ∂μ) = 1)
    {T : A × B → C} (hT : Measurable T)
    (hLaw : ∀ a, P.map (fun v => T (a,v)) = Q) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) = (powerIntensity b).prod Q := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) :=
    ((hc.comp (measurable_fst.comp measurable_snd)).mul measurable_fst).prodMk
      (hT.comp measurable_snd)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF, lintegral_prod
    (fun p : ℝ × (A × B) => f (c p.2.1*p.1,T p.2)) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : A) :
      (∫⁻ v, f (c a*x,T (a,v)) ∂P) = ∫⁻ w, f (c a*x,w) ∂Q := by
    rw [← hLaw a, lintegral_map]
    · exact hf.comp (measurable_const.prodMk measurable_id)
    · exact hT.comp (measurable_const.prodMk measurable_id)
  have hp (x : ℝ) : (∫⁻ v : A × B, f (c v.1*x,T v) ∂μ.prod P) =
      ∫⁻ a, ∫⁻ w, f (c a*x,w) ∂Q ∂μ := by
    rw [lintegral_prod (fun v : A × B => f (c v.1*x,T v))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [hv]
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × A => ∫⁻ w, f (c p.2*p.1,w) ∂Q) :=
    (hf.comp ((((hc.comp (measurable_snd.comp measurable_fst)).mul
      (measurable_fst.comp measurable_fst))).prodMk measurable_snd)).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : A) : (∫⁻ x, ∫⁻ w, f (c a*x,w) ∂Q ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) * (∫⁻ x, ∫⁻ w, f (x,w) ∂Q ∂powerIntensity b) := by
    rw [← lintegral_map hf.lintegral_prod_right' (measurable_const_mul (c a)),
      map_powerIntensity_mul (hcpos a), lintegral_smul_measure]
    rfl
  simp_rw [hx]
  rw [lintegral_mul_const _ (by fun_prop), hm, one_mul,
    ← lintegral_prod _ hf.aemeasurable]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_law (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeDisplace n b μ c u s) =
      rawCascadeLaw n b := by
  induction n generalizing b μ c u s with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let P : Measure (NoiseTree A n) := noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))
    let Q : Measure (RawTree n) := rawCascadeLaw n (fun j => b (j+1))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let G : A × NoiseTree A n → RawTree n := fun p =>
      noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2
    have hG : Measurable G :=
      (measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hGLaw (a : A) : P.map (fun v => G (a,v)) = Q :=
      ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))
        (fun i => hcpos (i+1)) (fun i => hm (i+1)) (u 0 (s,a))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n :=
      fun p => (c 0 (s,p.2.1) * p.1,G p.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))).mul
        measurable_fst).prodMk (hG.comp measurable_snd)
    have hI : I.map T = (powerIntensity (b 0)).prod Q :=
      map_powerIntensity_subtree (b 0) (μ 0 : Measure A) P Q (c := fun a => c 0 (s,a))
        ((hc 0).comp (measurable_const.prodMk measurable_id)) (hcpos 0 s) (hm 0 s) hG hGLaw
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod Q)
    calc
      _ = (poissonLaw I).map (fun ν => ν.map T) := by
        apply Measure.map_congr
        filter_upwards [sigmaPart_eq_ae I] with ν hν
        change (sigmaPart I ν).map T = ν.map T
        rw [hν]
      _ = poissonLaw (I.map T) := poissonLaw_map I hT
      _ = _ := poissonLaw_congr hI

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
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma measurable_noiseTreeKeep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeKeep n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeKeep
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1, (p.2.2.1,
          noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)))
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
          (ℝ × (A × NoiseTree A n)) => p.2.2.1)).prodMk
        ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))))

lemma noiseTreeKeep_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n) :
    noiseTreeForget A n (noiseTreeKeep n b μ c u s ν) = noiseTreeDisplace n b μ c u s ν := by
  induction n generalizing b μ c u s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeKeep noiseTreeForget noiseTreeDisplace
    rw [Measure.map_map]
    · congr 1
      funext p
      dsimp only [Function.comp_apply]
      rw [ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))]
    · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (by fun_prop))
    · exact (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul
          measurable_fst).prodMk
        ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => p.2.1)).prodMk
          ((measurable_noiseTreeKeep n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))))

end IsingPerceptron

namespace IsingPerceptron

lemma map_powerIntensity_keep_subtree {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    {T : A × B → C} (hT : Measurable T) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,(p.2.1,T p.2))) =
      (powerIntensity b).prod
        (((μ.prod P).withDensity (fun p => ENNReal.ofReal (c p.1^b))).map (fun p => (p.1,T p))) := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1 * p.1,(p.2.1,T p.2))) :=
    ((hc.comp (measurable_fst.comp measurable_snd)).mul measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (hT.comp measurable_snd))
  have hD : Measurable (fun p : A × B => ENNReal.ofReal (c p.1^b)) := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF]
  rw [lintegral_prod_symm _ (show Measurable (fun p : ℝ × (A × B) =>
    f (c p.2.1*p.1,(p.2.1,T p.2))) from hf.comp hF).aemeasurable]
  have hx (p : A × B) : (∫⁻ x, f (c p.1*x,(p.1,T p)) ∂powerIntensity b) =
      ENNReal.ofReal (c p.1^b) * ∫⁻ x, f (x,(p.1,T p)) ∂powerIntensity b := by
    calc
      _ = ∫⁻ x, f (x,(p.1,T p)) ∂(powerIntensity b).map (fun x => c p.1*x) :=
        (lintegral_map (hf.comp (measurable_id.prodMk measurable_const))
          (measurable_const_mul (c p.1))).symm
      _ = _ := by
        rw [map_powerIntensity_mul (hcpos p.1), lintegral_smul_measure]
        rfl
  simp_rw [hx]
  have hg : Measurable (fun p : A × B => ∫⁻ x, f (x,(p.1,T p)) ∂powerIntensity b) := by
    have hh : Measurable (fun p : (A × B) × ℝ => f (p.2,(p.1.1,T p.1))) :=
      hf.comp (measurable_snd.prodMk
        ((measurable_fst.comp measurable_fst).prodMk (hT.comp measurable_fst)))
    exact hh.lintegral_prod_right'
  calc
    _ = ∫⁻ p, (∫⁻ x, f (x,(p.1,T p)) ∂powerIntensity b)
        ∂(μ.prod P).withDensity (fun p => ENNReal.ofReal (c p.1^b)) :=
      (lintegral_withDensity_eq_lintegral_mul _ hD hg).symm
    _ = ∫⁻ p, (∫⁻ x, f (x,p) ∂powerIntensity b)
        ∂(((μ.prod P).withDensity (fun p => ENNReal.ofReal (c p.1^b))).map
          (fun p => (p.1,T p))) :=
      (lintegral_map hf.lintegral_prod_left' (measurable_fst.prodMk hT)).symm
    _ = _ := (lintegral_prod_symm _ hf.aemeasurable).symm

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeKeep_law_succ (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) :
    let P := (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n))
    let G := fun p : A × NoiseTree A n => (p.1,
      noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2)
    (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))).map
      (noiseTreeKeep (n+1) b μ c u s) =
      poissonLaw ((powerIntensity (b 0)).prod
        ((((μ 0 : Measure A).prod P).withDensity (fun p => ENNReal.ofReal (c 0 (s,p.1)^b 0))).map G)) := by
  dsimp only
  let P := (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n))
  let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
  let T : A × NoiseTree A n → NoiseTree A n := fun p =>
    noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
      (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2
  have hT : Measurable T :=
    (measurable_noiseTreeKeep n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
      (((hu 0).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  let G : ℝ × (A × NoiseTree A n) → ℝ × (A × NoiseTree A n) :=
    fun p => (c 0 (s,p.2.1)*p.1,(p.2.1,T p.2))
  have hG : Measurable G :=
    (((hc 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))).mul
      measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (hT.comp measurable_snd))
  rw [noiseCascadeLaw_succ]
  calc
    _ = (poissonLaw I).map (fun ν => ν.map G) := by
      apply Measure.map_congr
      filter_upwards [sigmaPart_eq_ae I] with ν hν
      change (sigmaPart I ν).map G = ν.map G
      rw [hν]
    _ = poissonLaw (I.map G) := poissonLaw_map I hG
    _ = _ := by
      apply poissonLaw_congr
      exact map_powerIntensity_keep_subtree (b 0) (μ 0 : Measure A) P
        ((hc 0).comp (measurable_const.prodMk measurable_id)) (hcpos 0 s) hT

end IsingPerceptron

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

lemma withDensity_map_pullback {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure E) {f : E → F} (hf : Measurable f) {w : F → ℝ≥0∞} (hw : Measurable w) :
    (ν.withDensity (fun x => w (f x))).map f = (ν.map f).withDensity w := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    _ = ∫⁻ x, g (f x) ∂ν.withDensity (fun x => w (f x)) :=
      lintegral_map' hg.aemeasurable hf.aemeasurable
    _ = ∫⁻ x, w (f x) * g (f x) ∂ν :=
      lintegral_withDensity_eq_lintegral_mul _ (hw.comp hf) (hg.comp hf)
    _ = ∫⁻ x, w x * g x ∂ν.map f :=
      (lintegral_map' (hw.mul hg).aemeasurable hf.aemeasurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hw hg).symm

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

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [Nonempty A] in
lemma measurable_noiseLeafKeep (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafKeep n c u p.1 p.2) := by
  induction n generalizing c u with
  | zero => exact measurable_const
  | succ n ih =>
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : S × NoiseLeaf A (n+1) => p.2.2.1)).prodMk
        ((ih (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))))

lemma noiseWeightedLeafMeasure_lintegral (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n) {F : NoiseLeaf A n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseWeightedLeafMeasure n c u s ν) = noiseTreeTotal A n ν *
      ∫⁻ v, noiseLeafProduct n c u s v * F (noiseLeafKeep n c u s v) ∂noiseLeafKernel A n ν := by
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
  have hk : Measurable (noiseLeafKeep n c u s) :=
    (measurable_noiseLeafKeep n hc hu).comp (measurable_const.prodMk measurable_id)
  rw [noiseWeightedLeafMeasure, lintegral_map' hF.aemeasurable hk.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun v => noiseTreeTotal A n ν * noiseLeafProduct n c u s v) from measurable_const.mul hp)
      (show Measurable (fun v => F (noiseLeafKeep n c u s v)) from hF.comp hk)]
  change (∫⁻ v, (noiseTreeTotal A n ν * noiseLeafProduct n c u s v) *
    F (noiseLeafKeep n c u s v) ∂noiseLeafKernel A n ν) = _
  simp_rw [mul_assoc]
  exact lintegral_const_mul _ (hp.mul (hF.comp hk))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

lemma measurableSet_noiseGibbsRegular (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    MeasurableSet {p : S × NoiseTree A n | NoiseGibbsRegular n b μ c u p.1 p.2} := by
  induction n generalizing b μ c u with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    have htot : Measurable (fun p : S × NoiseTree A (n+1) => noiseTreeTotal A (n+1) p.2) :=
      (measurable_noiseTreeTotal A (n+1)).comp measurable_snd
    have hkeep : Measurable (fun p : S × NoiseTree A (n+1) =>
        noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u p.1 p.2)) :=
      (measurable_noiseTreeTotal A (n+1)).comp (measurable_noiseTreeKeep (n+1) b μ hc hu)
    have hgood : MeasurableSet {p : S × NoiseTree A (n+1) | Marked.PoissonGood I p.2} :=
      by
        simp only [Marked.PoissonGood, ofPred_forall]
        exact MeasurableSet.iInter (fun j => measurableSet_lt
          ((Measure.measurable_coe (MeasurableSet.disjointed (measurableSet_spanningSets I) j)).comp measurable_snd)
          (measurable_const (a := (∞ : ℝ≥0∞))))
    let B := {p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) |
      ¬ NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2}
    have hB : MeasurableSet B :=
      ((ih _ _ (fun j => hc (j+1)) (fun j => hu (j+1))).preimage
        (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))).compl
    have hm : Measurable (fun p : S × NoiseTree A (n+1) =>
        ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) :=
      measurable_sigmaPart_param I measurable_snd (measurable_const.indicator hB)
    have he : {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} =
        {p | (∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) = 0} := by
      ext p
      rw [mem_ofPred_eq, mem_ofPred_eq, ae_iff]
      change (sigmaPart I p.2) {x | (p,x) ∈ B} = 0 ↔ _
      have hh := lintegral_indicator_one (μ := sigmaPart I p.2)
        (show MeasurableSet {x : ℝ × (A × NoiseTree A n) | (p,x) ∈ B} from
          hB.preimage (measurable_const.prodMk measurable_id))
      simpa only [Set.indicator, mem_ofPred_eq, Pi.one_apply] using Iff.of_eq (congrArg (· = 0) hh).symm
    have htail : MeasurableSet {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} := by
      rw [he]
      exact measurableSet_eq_fun hm measurable_const
    exact ((measurableSet_lt measurable_const htot).inter (measurableSet_lt htot measurable_const)).inter
      (((measurableSet_lt measurable_const hkeep).inter (measurableSet_lt hkeep measurable_const)).inter
        (hgood.inter htail))

lemma noiseGibbsRegular_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, ∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A) = 1) (s : S) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), NoiseGibbsRegular n b μ c u s ν := by
  induction n generalizing b μ c u s with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    have htot := noiseCascade_good A (n+1) b hb μ
    have hkeep : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) ∧
          noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) < ∞ := by
      simp_rw [noiseTreeTotal, noiseTreeKeep_forget (n+1) b μ hc hu]
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        ((measurable_noiseTreeDisplace (n+1) b μ hc hu).comp
          (measurable_const.prodMk measurable_id)).aemeasurable
      change ∀ᵐ y ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))).map
        (noiseTreeDisplace (n+1) b μ c u s), 0 < rawTreeTotal (n+1) y ∧ rawTreeTotal (n+1) y < ∞
      rw [noiseTreeDisplace_law (n+1) b μ hc hu hcpos hm s]
      exact (rawCascade_total_moments (n+1) b hb).1
    let E := fun p : ℝ × (A × NoiseTree A n) =>
      NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2
    have hE : MeasurableSet {p | E p} :=
      (measurableSet_noiseGibbsRegular n _ _ (fun j => hc (j+1)) (fun j => hu (j+1))).preimage
        (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))
    have ha : ∀ᵐ p ∂I, E p := by
      apply (Measure.ae_prod_iff_ae_ae hE).mpr
      apply ae_of_all
      intro x
      apply (Measure.ae_prod_iff_ae_ae (hE.preimage (measurable_const.prodMk measurable_id))).mpr
      apply ae_of_all
      intro a
      exact ih _ hb.tail _ (fun j => hc (j+1)) (fun j => hu (j+1))
        (fun j => hcpos (j+1)) (fun j => hm (j+1)) (u 0 (s,a))
    have hd := poissonLaw_ae_intensity I hE ha
    filter_upwards [htot,hkeep,Marked.poissonGood_ae I,hd] with ν hν hk hg hd
    refine ⟨hν.1,hk,hg,?_⟩
    rwa [Marked.sigmaPart_eq_of_good I hg]

lemma noiseLeafKernel_unnormalized_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    noiseTreeTotal A (n+1) ν * (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_lintegral n ν hν hF, ← mul_assoc,
    ENNReal.mul_inv_cancel hν.1.ne' hν.2.ne, one_mul]

theorem noiseWeightedLeafMeasure_eq (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    noiseWeightedLeafMeasure n c u s ν =
      noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) •
        noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
  induction n generalizing b μ c u s with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    simp [noiseWeightedLeafMeasure_lintegral 0 hc hu s ν hF,
      noiseTreeKeep, noiseTreeTotal, rawTreeTotal, noiseLeafProduct,
      noiseLeafKeep, noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j+1)
    let μt := fun j => μ (j+1)
    let ct := fun j => c (j+1)
    let ut := fun j => u (j+1)
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n bt μt : Measure (NoiseTree A n)))
    let T : ℝ × (A × NoiseTree A n) → ℝ × (A × NoiseTree A n) := fun p =>
      (c 0 (s,p.2.1)*p.1,(p.2.1,noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2))
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul measurable_fst).prodMk
        ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => p.2.1)).prodMk
          ((measurable_noiseTreeKeep n bt μt (fun j => hc (j+1)) (fun j => hu (j+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))))
    have hσ : sigmaPart I ν = ν := Marked.sigmaPart_eq_of_good I hν.2.2.1
    have hd : ∀ᵐ p ∂ν, NoiseGibbsRegular n bt μt ct ut (u 0 (s,p.2.1)) p.2.2 := by
      have hh : ∀ᵐ p ∂sigmaPart I ν, NoiseGibbsRegular n bt μt ct ut (u 0 (s,p.2.1)) p.2.2 := hν.2.2.2
      rwa [hσ] at hh
    have hkeep : noiseTreeKeep (n+1) b μ c u s ν = ν.map T := by
      change (sigmaPart I ν).map T = _
      rw [hσ]
    apply Measure.ext_of_lintegral
    intro F hF
    have hG : Measurable (fun v : NoiseLeaf A (n+1) =>
        noiseLeafProduct (n+1) c u s v * F (noiseLeafKeep (n+1) c u s v)) :=
      ((measurable_noiseLeafProduct (n+1) hc hu).comp (measurable_const.prodMk measurable_id)).mul
        (hF.comp ((measurable_noiseLeafKeep (n+1) hc hu).comp (measurable_const.prodMk measurable_id)))
    rw [noiseWeightedLeafMeasure_lintegral (n+1) hc hu s ν hF,
      noiseLeafKernel_unnormalized_lintegral n ν hν.1 hG,
      lintegral_smul_measure, smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hν.2.1 hF, hkeep]
    have hmF : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p : (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n =>
        (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
          (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    rw [lintegral_map' (show AEMeasurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) _ from
      (((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (by fun_prop))).mul hmF).aemeasurable) hT.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hd] with p hp
    have hFp : Measurable (fun v : NoiseLeaf A n => F (c 0 (s,p.2.1)*p.1,(p.2.1,v))) :=
      hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun η : Measure (NoiseLeaf A n) =>
      ∫⁻ v, F (c 0 (s,p.2.1)*p.1,(p.2.1,v)) ∂η)
      (ih bt μt (fun j => hc (j+1)) (fun j => hu (j+1))
        (fun j => hcpos (j+1)) (u 0 (s,p.2.1)) p.2.2 hp)
    rw [noiseWeightedLeafMeasure_lintegral n (fun j => hc (j+1)) (fun j => hu (j+1)) _ _ hFp,
      lintegral_smul_measure, smul_eq_mul] at he
    change ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
      (∫⁻ v, (ENNReal.ofReal (c 0 (s,p.2.1)) * noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v) *
        F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))
          ∂noiseLeafKernel A n p.2.2) =
      ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) *
        noiseTreeTotal A n (noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2) *
        (∫⁻ v, F (c 0 (s,p.2.1)*p.1,(p.2.1,v))
          ∂noiseLeafKernel A n (noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2))
    have hcmax : max (c 0 (s,p.2.1)*p.1) 0 = c 0 (s,p.2.1)*max p.1 0 := by
      rw [mul_max_of_nonneg _ _ (hcpos 0 s p.2.1).le, mul_zero]
    rw [hcmax, ENNReal.ofReal_mul (hcpos 0 s p.2.1).le]
    simp_rw [mul_assoc]
    have hz : Measurable (fun v : NoiseLeaf A n => noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v *
        F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))) :=
      (((measurable_noiseLeafProduct n (fun j => hc (j+1)) (fun j => hu (j+1))).comp
        (measurable_const.prodMk measurable_id)).mul
        (hFp.comp ((measurable_noiseLeafKeep n (fun j => hc (j+1)) (fun j => hu (j+1))).comp
          (measurable_const.prodMk measurable_id))))
    rw [lintegral_const_mul _ hz]
    calc
      _ = ENNReal.ofReal (c 0 (s,p.2.1)) * ENNReal.ofReal (max p.1 0) *
          (noiseTreeTotal A n p.2.2 * ∫⁻ v, noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v *
            F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))
              ∂noiseLeafKernel A n p.2.2) := by ring
      _ = _ := by rw [he]; ring

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

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [MeasurableSpace S] in
lemma NoiseGibbsRegular.masses {n : ℕ} {b : ℕ → ℝ} {μ : ℕ → ProbabilityMeasure A}
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S} {s : S} {ν : NoiseTree A n}
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    (0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞) ∧
      (0 < noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) ∧
        noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) < ∞) := by
  cases n with
  | zero => simp [noiseTreeTotal, rawTreeTotal]
  | succ n => exact ⟨hν.1,hν.2.1⟩

theorem noiseTiltedLeafLaw_keep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    (noiseTiltedLeafLaw n c u s ν).map (noiseLeafKeep n c u s) =
      noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
  let m := (noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
  have hk : Measurable (noiseLeafKeep n c u s) :=
    (measurable_noiseLeafKeep n hc hu).comp (measurable_const.prodMk measurable_id)
  have he : (noiseTreeTotal A n ν • m).map (noiseLeafKeep n c u s) =
      noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) •
        noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := noiseWeightedLeafMeasure_eq n b μ hc hu hcpos s ν hν
    unfold noiseWeightedLeafMeasure at hh
    change Measure.map (noiseLeafKeep n c u s)
      ((noiseLeafKernel A n ν).withDensity (noiseTreeTotal A n ν • noiseLeafProduct n c u s)) = _ at hh
    rwa [withDensity_smul _ hp] at hh
  have hm : noiseTreeTotal A n ν * m univ = noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := congrArg (fun η : Measure (NoiseLeaf A n) => η univ) he
    simpa only [Measure.map_apply hk MeasurableSet.univ, preimage_univ,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hh
  have hm0 : 0 < m univ := by
    by_contra hh
    have hz : m univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
    rw [hz, mul_zero] at hm
    exact hν.masses.2.1.ne' hm.symm
  have him : m univ < ∞ := by
    have hlt : noiseTreeTotal A n ν * m univ < ∞ := hm ▸ hν.masses.2.2
    rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
    · exact h.2
    · exact (hν.masses.1.1.ne' h).elim
    · exact (hm0.ne' h).elim
  change (normalizeMass m).map _ = _
  rw [← normalizeMass_smul m hν.masses.1 ⟨hm0,him⟩,
    normalizeMass_map _ hk (by
      simp only [Measure.smul_apply, smul_eq_mul, hm]
      exact hν.masses.2), he,
    normalizeMass_smul _ hν.masses.2 (by simp), normalizeMass_of_probability]

omit [MeasurableSpace A] [MeasurableSpace S] [Nonempty A] in
lemma noiseLeafProduct_telescoping (n : ℕ) (X : ℕ → S → ℝ) (u : ℕ → S × A → S)
    (s : S) (v : NoiseLeaf A n) :
    noiseLeafProduct n (fun i p => Real.exp (X (i+1) (u i p) - X i p.1)) u s v =
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v - X 0 s)) := by
  induction n generalizing X u s with
  | zero => simp [noiseLeafProduct, noiseLeafTerminal]
  | succ n ih =>
    rw [noiseLeafProduct]
    have hi := ih (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2
    rw [hi]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    change X 1 (u 0 (s,v.2.1)) - X 0 s +
      (noiseLeafTerminal n (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2 -
        X 1 (u 0 (s,v.2.1))) = _
    change _ = noiseLeafTerminal n (fun i => X (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2 - X 0 s
    ring

end IsingPerceptron

namespace IsingPerceptron
lemma normalizeMass_smul_any {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞) :
    normalizeMass (c • ν) = normalizeMass ν := by
  by_cases hν : 0 < ν univ ∧ ν univ < ∞
  · exact normalizeMass_smul ν hc hν
  · have ht : ¬ (0 < (c • ν) univ ∧ (c • ν) univ < ∞) := by
      intro h
      apply hν
      simp only [Measure.smul_apply, smul_eq_mul] at h
      constructor
      · by_contra hh
        have hz : ν univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
        simpa [hz] using h.1
      · rcases ENNReal.mul_lt_top_iff.mp h.2 with hh | hh | hh
        · exact hh.2
        · exact (hc.1.ne' hh).elim
        · simp [hh]
    simp only [normalizeMass, ite_eq_right ht, ite_eq_right hν]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma noiseTerminalGibbsLaw_eq_tilted (n : ℕ) {X : ℕ → S → ℝ}
    {u : ℕ → S × A → S} (hX : ∀ i, Measurable (X i))
    (hu : ∀ i, Measurable (u i)) (s : S) (ν : NoiseTree A n) :
    noiseTerminalGibbsLaw n X u s ν = noiseTiltedLeafLaw n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s ν := by
  have hm : Measurable (noiseLeafProduct n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s) :=
    (measurable_noiseLeafProduct n (fun i => ((hX (i+1) |>.comp (hu i)).sub
      ((hX i).comp measurable_fst)).exp) hu).comp (measurable_const.prodMk measurable_id)
  have hd : (fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v))) =
      ENNReal.ofReal (Real.exp (X 0 s)) • noiseLeafProduct n
        (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, noiseLeafProduct_telescoping]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  unfold noiseTerminalGibbsLaw noiseTiltedLeafLaw
  rw [hd, withDensity_smul _ hm, normalizeMass_smul_any _]
  exact ⟨ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top⟩

theorem noiseTerminalGibbsLaw_keep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s ν) :
    (noiseTerminalGibbsLaw n X u s ν).map (noiseLeafKeep n
      (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s) =
      noiseLeafKernel A n (noiseTreeKeep n b μ
        (fun i p => Real.exp (X (i+1) (u i p)-X i p.1)) u s ν) := by
  rw [noiseTerminalGibbsLaw_eq_tilted n hX hu]
  exact noiseTiltedLeafLaw_keep n b μ (fun i => ((hX (i+1) |>.comp (hu i)).sub
    ((hX i).comp measurable_fst)).exp) hu (fun _ _ _ => Real.exp_pos _) s ν hν

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedForestCoordinates_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledLeafEncodable _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

lemma measurable_labeledTreeForget (n : ℕ) : Measurable (labeledTreeForget n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact measurable_labeledMarkedMeasure.comp
      (measurable_fst.prodMk (Measurable.of_eval (fun m => Measurable.of_eval
        (fun i => ih.comp ((measurable_pi_apply i).comp
          ((measurable_pi_apply m).comp measurable_snd))))))

theorem labeledCascadeLaw_forget (n : ℕ) (b : ℕ → ℝ) :
    (labeledCascadeLaw n b : Measure (LabeledTree n)).map (labeledTreeForget n) =
      rawCascadeLaw n b := by
  induction n generalizing b with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    let b' := fun j => b (j+1)
    have hp : MeasurePreserving (labeledTreeForget n)
        (labeledCascadeLaw n b' : Measure (LabeledTree n)) (rawCascadeLaw n b') :=
      ⟨measurable_labeledTreeForget n,ih b'⟩
    have hpi : MeasurePreserving (fun ω : ℕ → LabeledTree n => fun i => labeledTreeForget n (ω i))
        (Measure.infinitePi (fun _ : ℕ => (labeledCascadeLaw n b' : Measure (LabeledTree n))))
        (Measure.infinitePi (fun _ : ℕ => (rawCascadeLaw n b' : Measure (RawTree n)))) := by
      refine ⟨Measurable.of_eval (fun _ => (measurable_labeledTreeForget n).comp
        (measurable_pi_apply _)),?_⟩
      rw [Measure.infinitePi_map_pi _ (fun _ => measurable_labeledTreeForget n)]
      simp_rw [hp.map_eq]
    have hppi : MeasurePreserving (fun ω : ℕ → ℕ → LabeledTree n =>
        fun m i => labeledTreeForget n (ω m i))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
          (fun _ : ℕ => (labeledCascadeLaw n b' : Measure (LabeledTree n)))))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
          (fun _ : ℕ => (rawCascadeLaw n b' : Measure (RawTree n))))) := by
      refine ⟨Measurable.of_eval (fun _ => hpi.measurable.comp (measurable_pi_apply _)),?_⟩
      rw [Measure.infinitePi_map_pi _ (fun _ => hpi.measurable)]
      simp_rw [hpi.map_eq]
    have hprod := (MeasurePreserving.id
      (labeledPoissonLaw (intensityComponents (powerIntensity (b 0))))).prod hppi
    change ((labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
        (fun _ : ℕ => (labeledCascadeLaw n b' : Measure (LabeledTree n)))))).map
      (labeledMarkedMeasure ∘ Prod.map id (fun ω => fun m i => labeledTreeForget n (ω m i))) = _
    rw [← Measure.map_map measurable_labeledMarkedMeasure hprod.measurable,hprod.map_eq,
      labeledMarkedMeasure_law,rawCascadeLaw_succ]
    apply poissonLaw_congr
    rw [intensityComponents_sum]

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

lemma rawTreeTotal_labeled_eq (n : ℕ) (ω : LabeledTree n) :
    rawTreeTotal n (labeledTreeForget n ω) = ∑' v, labeledLeafWeight n ω v := by
  induction n with
  | zero => simp [rawTreeTotal,labeledLeafWeight]
  | succ n ih =>
    change (∫⁻ p : ℝ × RawTree n, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2
      ∂labeledMarkedMeasure (ω.1,fun m i => labeledTreeForget n (ω.2 m i))) = _
    have hm : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2) :=
      (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_rawTreeTotal n).comp measurable_snd)
    simp only [labeledMarkedMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hm]
    simp only [ih]
    change _ = ∑' v : ChildLabel × LabeledLeaf n,
      childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [finiteCloud_tsum_weight]

lemma labeledLeafMass_univ (n : ℕ) (ω : LabeledTree n) :
    labeledLeafMass n ω Set.univ = rawTreeTotal n (labeledTreeForget n ω) := by
  rw [← lintegral_one,labeledLeafMass_lintegral]
  simp only [mul_one,rawTreeTotal_labeled_eq]

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
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma reference_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (referencePartition ν H)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin,referencePartition] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x)))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ConvexDerivativeFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replica_tilted_pi {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hz : 0 < referencePartition ν H := _root_.MeasureTheory.integral_exp_pos he
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton,Measure.pi_singleton,Measure.pi_singleton]
  simp_rw [tilted_singleton]
  rw [show referencePartition (Measure.pi (fun _ : Fin r => ν)) (fun σ => ∑ i, H (σ i)) =
    (referencePartition ν H)^r from reference_replica_partition ν H r]
  rw [Real.exp_sum,ENNReal.ofReal_div_of_pos (pow_pos hz r),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),ENNReal.ofReal_pow hz.le]
  simp_rw [ENNReal.ofReal_div_of_pos hz]
  rw [Finset.prod_mul_distrib,ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
  simp

lemma referenceReplicaMean_eq_tilted {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← replica_tilted_pi ν H he r,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [reference_replica_partition]; rfl

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {A : Type*} [MeasurableSpace A]

theorem logMean_normalized_moment (μ : Measure A) [IsProbabilityMeasure μ]
    (F : A → ℝ) {b : ℝ} (hb : b ≠ 0)
    (hi : Integrable (fun a => Real.exp (b*F a)) μ) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp (F a-logMean b μ F))^b) ∂μ) = 1 := by
  let M := ∫ a, Real.exp (b*F a) ∂μ
  have hM : 0 < M := integral_exp_pos μ F hi
  have he a : (Real.exp (F a-logMean b μ F))^b = M⁻¹ * Real.exp (b*F a) := by
    rw [← Real.exp_mul]
    have he' : (F a-logMean b μ F)*b = -Real.log M+b*F a := by
      dsimp only [logMean, M]
      field_simp
      ring
    rw [he', Real.exp_add, Real.exp_neg, Real.exp_log hM]
  simp_rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun a => (Real.exp_pos _).le)]
  change ENNReal.ofReal M⁻¹ * ENNReal.ofReal M = 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le), inv_mul_cancel₀ hM.ne', ENNReal.ofReal_one]

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma backwardValue_step (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : i < n) (s : S) :
    backwardValue n b μ u F i s = logMean (b i) (μ i : Measure A)
      (fun a => backwardValue n b μ u F (i+1) (u i (s,a))) := by
  unfold backwardValue
  rw [show n-i = (n-(i+1))+1 by omega, cascadeRecursion]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

omit [MeasurableSpace S] in
lemma backwardValue_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : n ≤ i) :
    backwardValue n b μ u F i = F := by
  simp [backwardValue, Nat.sub_eq_zero_of_le hi, cascadeRecursion]

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [MeasurableSpace S] [Nonempty A] in
lemma backwardValue_multiplier_moment_admissible (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) (u : ℕ → S × A → S) (F : S → ℝ)
    (hb : ∀ i < n, 0 < b i)
    (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A))
    (i : ℕ) (s : S) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp
      (backwardValue n b μ u F (i+1) (stoppedUpdate n u i (s,a)) -
        backwardValue n b μ u F i s)) ^ b i) ∂(μ i : Measure A)) = 1 := by
  by_cases hi : i < n
  · simp only [stoppedUpdate, ite_eq_left hi, backwardValue_step n b μ u F hi]
    exact logMean_normalized_moment _ _ (hb i hi).ne' (hadm i hi s)
  · have hni : n ≤ i := by omega
    simp only [stoppedUpdate, ite_eq_right hi,
      backwardValue_terminal n b μ u F hni,
      backwardValue_terminal n b μ u F (show n ≤ i+1 by omega), sub_self,
      Real.exp_zero, Real.one_rpow, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]

end IsingPerceptron

namespace IsingPerceptron
variable {S : Type*} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

lemma backwardValue_linearGrowth_moments (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hb : ∀ i < n, 0 < b i) :
    ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ (fun _ p => p.1+p.2) F (i+1) (s+a))) (μ i : Measure S) := by
  intro i hi s
  apply integrable_exp_of_linearGrowth _ (hμ i hi)
    ((measurable_backwardValue n b μ (fun _ => measurable_fst.add measurable_snd) hF (i+1)).comp
      (measurable_const.add measurable_id))
  apply HasLinearGrowth.add_left
  unfold backwardValue
  exact cascadeRecursion_linearGrowth _ _ _ (fun j hj => hμ (i+1+j) (by omega)) hF hG
    (fun j hj => hb (i+1+j) (by omega))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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


lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_RetainedDisplacement
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Displacement. -/

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

variable {A : Type} [MeasurableSpace A]

lemma measurable_noiseLeafMark (n : ℕ) (i : Fin n) : Measurable (fun v : NoiseLeaf A n => noiseLeafMark n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst.comp measurable_snd
    · exact (ih j).comp (measurable_snd.comp measurable_snd)

omit [MeasurableSpace A] in
lemma noiseLeafMark_keep {S : Type} (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (v : NoiseLeaf A n) (i : Fin n) :
    noiseLeafMark n (noiseLeafKeep n c u s v) i = noiseLeafMark n v i := by
  induction n generalizing c u s with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih _ _ _ _ j

lemma noiseLeafMark_labeled (n : ℕ) (ω : LabeledTree n) (g : ForestVertex n → A)
    (v : LabeledLeaf n) (i : Fin n) :
    noiseLeafMark n (labeledNoiseLeaf A n (ω,markForestOfCoords A n g) v) i = g (edgeAt n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [noiseLeafMark,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_zero]
    · simpa only [noiseLeafMark,Fin.cases_succ,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_succ] using
        ih (ω.2 v.1.1 v.1.2) (fun w => g (v.1.1,v.1.2,some w)) v.2 j

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma sampling_replica_morphism {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y] (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω')
    {ν : Ω → Measure X} {κ : Ω' → Measure Y} (hν : Measurable ν) (hκ : Measurable κ)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (κ ω)]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    {ψ : Ω → X → Y} (hψ : Measurable (fun p : Ω × X => ψ p.1 p.2))
    (h : ∀ᵐ ω ∂P, (ν ω).map (ψ ω) = κ (T ω)) :
    (P ⊗ₘ probabilityReplicaKernel ν hν).map (fun p i => ψ p.1 (p.2 i)) =
      probabilityReplicaKernel κ hκ ∘ₘ Q := by
  have hΨ : Measurable (fun p : Ω × (ℕ → X) => fun i => ψ p.1 (p.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact hψ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hΨ,Measure.lintegral_compProd
    (show Measurable (fun p : Ω × (ℕ → X) => F (fun i => ψ p.1 (p.2 i))) from hF.comp hΨ)]
  have he : (∫⁻ ω, ∫⁻ σ, F (fun i => ψ ω (σ i)) ∂(probabilityReplicaKernel ν hν) ω ∂P) =
      ∫⁻ ω, ∫⁻ σ, F σ ∂(probabilityReplicaKernel κ hκ) (T ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [h] with ω hω
    change (∫⁻ σ, F (fun i => ψ ω (σ i)) ∂Measure.infinitePi (fun _ : ℕ => ν ω)) =
      ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => κ (T ω))
    have hψω : Measurable (ψ ω) := hψ.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map hF (by fun_prop : Measurable (fun σ : ℕ → X => fun i => ψ ω (σ i))),
      Measure.infinitePi_map_pi _ (fun _ => hψω)]
    simp only [hω]
  rw [he]
  have hI : Measurable (fun ω => ∫⁻ σ, F σ ∂(probabilityReplicaKernel κ hκ) ω) := hF.lintegral_kernel
  rw [← lintegral_map hI hT,hPQ]
  change _ = ∫⁻ σ, F σ ∂Q.bind (probabilityReplicaKernel κ hκ)
  exact (Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable).symm

 

theorem labeled_marked_replica_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
    (P ⊗ₘ probabilityReplicaKernel (fun p => labeledLeafLaw n p.1)
      ((measurable_labeledLeafLaw n).comp measurable_fst)).map
      (fun p i => labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) (p.2 i)) =
      markedReplicaLaw n b μ := by
  intro P
  let T := fun p : LabeledTree n × (ForestVertex n → A) =>
    labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : P.map T = (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) :=
    labeledNoiseCoordinates_law A n b μ
  have hp : MeasurePreserving T P (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism P _ (ν := fun p : LabeledTree n × (ForestVertex n → A) => labeledLeafLaw n p.1)
    (κ := noiseLeafKernel A n) ((measurable_labeledLeafLaw n).comp measurable_fst)
    (noiseLeafKernel A n).measurable hT hPQ
    (ψ := fun p v => labeledNoiseLeaf A n (p.1,markForestOfCoords A n p.2) v)
  · apply measurable_from_prod_countable_left
    intro v
    exact (measurable_labeledNoiseLeaf A n v).comp (by fun_prop)
  · filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good A n b hb μ)] with p hp
    apply labeledLeafLaw_noiseMap A n p.1 (markForestOfCoords A n p.2) hp
    cases n with
    | zero => simp [noiseTreeTotal,rawTreeTotal]
    | succ n => exact hp.1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma normalizeMass_exp {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    normalizeMass (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = ν.tilted H := by
  have hZ : (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) univ =
      ENNReal.ofReal (∫ x, Real.exp (H x) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  have hpos := _root_.MeasureTheory.integral_exp_pos he
  rw [normalizeMass,ite_eq_left (by rw [hZ]; exact ⟨ENNReal.ofReal_pos.mpr hpos,ENNReal.ofReal_lt_top⟩),
    hZ,Measure.tilted,← withDensity_smul _ hH.exp.ennreal_ofReal]
  congr 1; funext x
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_inv_of_pos hpos,mul_comm]

lemma normalizeMass_weight_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (ν : Measure X) {ψ : X → Y} (hψ : Measurable ψ)
    {w : Y → ℝ≥0∞} (hw : Measurable w)
    (hm : 0 < ((ν.map ψ).withDensity w) univ ∧ ((ν.map ψ).withDensity w) univ < ∞) :
    (normalizeMass (ν.withDensity (fun x => w (ψ x)))).map ψ =
      normalizeMass ((ν.map ψ).withDensity w) := by
  have he := withDensity_map_pullback ν hψ hw
  have hmass : (ν.withDensity (fun x => w (ψ x))) univ = ((ν.map ψ).withDensity w) univ := by
    rw [← he,Measure.map_apply hψ MeasurableSet.univ]; rfl
  rw [normalizeMass_map _ hψ (by simpa only [hmass] using hm),he]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A conditional product-law bridge for ancestor-dependent cascade marks. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace InvariantIsing

/-- Replacing a mark by a seed realization and replacing each descendant law
by the same conditional law preserves the full marked subtree distribution. -/
lemma ancestor_fiber_map_product {S A B C D : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure S) (μ : Measure A) (Q : Measure B) (R : Measure C)
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {f : S → A} (hf : Measurable f) (hlaw : P.map f = μ)
    {g : A × B → D} {h : A × C → D} (hg : Measurable g) (hh : Measurable h)
    (hsub : ∀ a, Q.map (fun b => g (a,b)) = R.map (fun c => h (a,c))) :
    (P.prod Q).map (fun p => (f p.1,g (f p.1,p.2))) =
      (μ.prod R).map (fun p => (p.1,h p)) := by
  have hleft : Measurable (fun p : S × B => (f p.1,g (f p.1,p.2))) :=
    (hf.comp measurable_fst).prodMk (hg.comp ((hf.comp measurable_fst).prodMk measurable_snd))
  have hright : Measurable (fun p : A × C => (p.1,h p)) := measurable_fst.prodMk hh
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hleft, lintegral_map hF hright]
  rw [lintegral_prod (fun p : S × B => F (f p.1,g (f p.1,p.2))) (hF.comp hleft).aemeasurable,
    lintegral_prod (fun p : A × C => F (p.1,h p)) (hF.comp hright).aemeasurable]
  have hi a : MeasureTheory.lintegral Q (fun b => F (a,g (a,b))) =
      MeasureTheory.lintegral R (fun c => F (a,h (a,c))) := by
    have hFa : Measurable (fun d : D => F (a,d)) := hF.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map (g := fun b : B => g (a,b)) hFa
      (hg.comp (measurable_const.prodMk measurable_id)), hsub a,
      lintegral_map (g := fun c : C => h (a,c)) hFa
        (hh.comp (measurable_const.prodMk measurable_id))]
  simp_rw [hi]
  have hJ : Measurable (fun a => MeasureTheory.lintegral R (fun c => F (a,h (a,c)))) :=
    (hF.comp hright).lintegral_prod_right'
  rw [← lintegral_map hJ hf, hlaw]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedTree
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-depth vector cascade marking by independent uniform seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

section Coordinates
variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
lemma measurable_cascadeSeedTree (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) :
    Measurable (fun p : (ι → ℝ) × NoiseTree unitInterval n => cascadeSeedTree n b ψ p.1 p.2) := by
  induction n generalizing b ψ with
  | zero => exact measurable_const
  | succ n ih =>
    unfold cascadeSeedTree
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
        (ℝ × (unitInterval × NoiseTree unitInterval n)) =>
          (p.2.1, (ψ 0 p.1.1 p.2.2.1,
            cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
              (p.1.1+ψ 0 p.1.1 p.2.2.1) p.2.2.2)))
    have hmark : Measurable (fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
        (ℝ × (unitInterval × NoiseTree unitInterval n)) => ψ 0 p.1.1 p.2.2.1) :=
      (hψ 0).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    exact (by fun_prop : Measurable (fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
      (ℝ × (unitInterval × NoiseTree unitInterval n)) => p.2.1)).prodMk
        (hmark.prodMk ((ih _ _ (fun i => hψ (i+1))).comp
          (((by fun_prop : Measurable (fun p : ((ι → ℝ) × NoiseTree unitInterval (n+1)) ×
            (ℝ × (unitInterval × NoiseTree unitInterval n)) => p.1.1)).add hmark).prodMk (by fun_prop))))

omit [Fintype ι] in
lemma cascadeSeedTree_law_succ (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    let P : Measure (NoiseTree unitInterval n) :=
      noiseCascadeLaw unitInterval n (fun j => b (j+1)) (fun _ => cascadeSeedLaw)
    let G := fun p : ℝ × (unitInterval × NoiseTree unitInterval n) =>
      (p.1, (ψ 0 z p.2.1,
        cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1)) (z+ψ 0 z p.2.1) p.2.2))
    (noiseCascadeLaw unitInterval (n+1) b (fun _ => cascadeSeedLaw) :
      Measure (NoiseTree unitInterval (n+1))).map (cascadeSeedTree (n+1) b ψ z) =
      poissonLaw (((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod P)).map G) := by
  intro P G
  let J := (powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod P)
  have hG : Measurable G := by
    change Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) =>
      (p.1, (ψ 0 z p.2.1,
        cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1)) (z+ψ 0 z p.2.1) p.2.2)))
    have hmark : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) => ψ 0 z p.2.1) :=
      (hψ 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))
    exact measurable_fst.prodMk (hmark.prodMk
      ((measurable_cascadeSeedTree n _ _ (fun i => hψ (i+1))).comp
        ((measurable_const.add hmark).prodMk (by fun_prop))))
  rw [noiseCascadeLaw_succ]
  change (poissonLaw J).map _ = poissonLaw (J.map G)
  calc
    _ = (poissonLaw J).map (fun T => T.map G) := by
      apply Measure.map_congr
      filter_upwards [sigmaPart_eq_ae J] with T hT
      change (sigmaPart J T).map G = T.map G
      rw [hT]
    _ = _ := poissonLaw_map J hG

end Coordinates
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularity of uniform-seed trees, independent of the ancestor state. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing

lemma cascadeSeedRegular_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    ∀ᵐ T ∂(noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure _),
      CascadeSeedRegular n b T := by
  exact noiseGibbsRegular_ae n b hb (fun _ => cascadeSeedLaw)
    (fun _ => measurable_const) (fun _ => measurable_const) (fun _ _ _ => zero_lt_one)
    (fun _ _ => by simp) PUnit.unit

lemma cascadeSeedRegular_sigma {n : ℕ} {b : ℕ → ℝ} {T : NoiseTree unitInterval (n+1)}
    (hT : CascadeSeedRegular (n+1) b T) :
    sigmaPart ((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod
      (noiseCascadeLaw unitInterval n (fun j => b (j+1)) (fun _ => cascadeSeedLaw)))) T = T :=
  Marked.sigmaPart_eq_of_good _ hT.2.2.1

lemma cascadeSeedRegular_tail {n : ℕ} {b : ℕ → ℝ} {T : NoiseTree unitInterval (n+1)}
    (hT : CascadeSeedRegular (n+1) b T) :
    ∀ᵐ p ∂T, CascadeSeedRegular n (fun j => b (j+1)) p.2.2 := by
  have h := hT.2.2.2
  rwa [cascadeSeedRegular_sigma hT] at h

lemma cascadeSeedRegular_total {n : ℕ} {b : ℕ → ℝ} {T : NoiseTree unitInterval (n+1)}
    (hT : CascadeSeedRegular (n+1) b T) :
    0 < noiseTreeTotal unitInterval (n+1) T ∧ noiseTreeTotal unitInterval (n+1) T < ∞ := hT.1

theorem cascadeSeedTree_total {ι : Type} [Fintype ι] (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (T : NoiseTree unitInterval n) (hT : CascadeSeedRegular n b T) (z : ι → ℝ) :
    noiseTreeTotal (ι → ℝ) n (cascadeSeedTree n b ψ z T) = noiseTreeTotal unitInterval n T := by
  induction n generalizing b ψ z with
  | zero => rfl
  | succ n ih =>
    have hmap : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) =>
        (p.1,(ψ 0 z p.2.1,cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
          (z+ψ 0 z p.2.1) p.2.2))) := by
      have hm : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) => ψ 0 z p.2.1) :=
        (hψ 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))
      exact measurable_fst.prodMk (hm.prodMk
        ((measurable_cascadeSeedTree n _ _ (fun i => hψ (i+1))).comp
          ((measurable_const.add hm).prodMk (by fun_prop))))
    rw [cascadeSeedTree, cascadeSeedRegular_sigma hT, noiseTreeTotal_succ, noiseTreeTotal_succ]
    rw [lintegral_map (show Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
      ENNReal.ofReal (max p.1 0) * noiseTreeTotal (ι → ℝ) n p.2.2) from
        (by fun_prop : Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
          ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal (ι → ℝ) n).comp
            (measurable_snd.comp measurable_snd))) hmap]
    apply lintegral_congr_ae
    filter_upwards [cascadeSeedRegular_tail hT] with p hp
    rw [ih _ _ (fun i => hψ (i+1)) _ hp]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedLeaf
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weight-preserving leaf map for ancestor-dependent vector marks. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

lemma measurable_cascadeSeedLeaf (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) :
    Measurable (fun p : (ι → ℝ) × NoiseLeaf unitInterval n => cascadeSeedLeaf n ψ p.1 p.2) := by
  induction n generalizing ψ with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : Measurable (fun p : (ι → ℝ) × NoiseLeaf unitInterval (n+1) => ψ 0 p.1 p.2.2.1) :=
      (hψ 0).comp (measurable_fst.prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    exact (measurable_fst.comp measurable_snd).prodMk (hm.prodMk
      ((ih _ (fun i => hψ (i+1))).comp
        ((measurable_fst.add hm).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_MarkForestRootLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-branch and two-distinct-branch laws of the finite independent mark forest. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {A : Type} [MeasurableSpace A]

lemma markForestRoot_preserving (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (a : ChildLabel) :
    MeasurePreserving (fun z : MarkForest A (n+1) => z a.1 a.2)
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      ((μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))) := by
  let Q := (μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) a.2).comp
    (measurePreserving_eval_infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => Q)) a.1)

lemma markForestRoots_preserving (n : ℕ) (μ : ℕ → ProbabilityMeasure A)
    (a b : ChildLabel) (hab : a ≠ b) :
    MeasurePreserving (fun z : MarkForest A (n+1) => (z a.1 a.2,z b.1 b.2))
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      (((μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))).prod
        ((μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)))) := by
  let Q := (μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))
  have hf : MeasurePreserving (fun z : MarkForest A (n+1) => fun p : ChildLabel => z p.1 p.2)
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      (Measure.infinitePi fun _ : ChildLabel => Q) :=
    ⟨by fun_prop, Measure.infinitePi_map_curry_symm (fun (_ _ : ℕ) => Q)⟩
  have hp : MeasurePreserving (fun z : ChildLabel → A × MarkForest A n => (z a,z b))
      (Measure.infinitePi fun _ : ChildLabel => Q) (Q.prod Q) :=
    ⟨by fun_prop, Measure.infinitePi_map_eval_prod hab⟩
  exact hp.comp hf

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ancestor-state increment path generated by an independent seed forest. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

lemma measurable_cascadeSeedPath (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (α : LabeledLeaf n) :
    Measurable (fun p : (ι → ℝ) × MarkForest unitInterval n => cascadeSeedPath n ψ p.1 p.2 α) := by
  induction n generalizing ψ with
  | zero => exact Measurable.of_eval fun i => i.elim0
  | succ n ih =>
    have hm : Measurable (fun p : (ι → ℝ) × MarkForest unitInterval (n+1) =>
        ψ 0 p.1 (p.2 α.1.1 α.1.2).1) :=
      (hψ 0).comp (measurable_fst.prodMk (by fun_prop))
    apply Measurable.of_eval
    intro i
    refine Fin.cases hm ?_ i
    intro j
    exact ((measurable_pi_apply j).comp (ih _ (fun i => hψ (i+1)) α.2)).comp
      ((measurable_fst.add hm).prodMk (by fun_prop))

lemma cascadeSeedPath_labeled (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) (z : ι → ℝ)
    (T : LabeledTree n) (g : MarkForest unitInterval n) (α : LabeledLeaf n) :
    noiseLeafMark n (cascadeSeedLeaf n ψ z (labeledNoiseLeaf unitInterval n (T,g) α)) =
      cascadeSeedPath n ψ z g α := by
  induction n generalizing ψ z with
  | zero => exact funext fun i => i.elim0
  | succ n ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun k => ψ (k+1)) (z+ψ 0 z (g α.1.1 α.1.2).1)
      (T.2 α.1.1 α.1.2) (g α.1.1 α.1.2).2 α.2) j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_NoiseLeafAncestry
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shared ancestry read from the sequence of Poisson edge weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma measurable_noiseLeafCommonDepth {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (n : ℕ) : Measurable (fun p : NoiseLeaf A n × NoiseLeaf B n =>
      noiseLeafCommonDepth n p.1 p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite (measurableSet_eq_fun measurable_fst.fst measurable_snd.fst)
      (measurable_const.add (ih.comp (measurable_fst.snd.snd.prodMk measurable_snd.snd.snd)))
      measurable_const

lemma noiseLeafCommonDepth_seed {ι : Type} (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (z w : ι → ℝ) (v v' : NoiseLeaf unitInterval n) :
    noiseLeafCommonDepth n (cascadeSeedLeaf n ψ z v) (cascadeSeedLeaf n ψ w v') =
      noiseLeafCommonDepth n v v' := by
  induction n generalizing ψ z w with
  | zero => rfl
  | succ n ih =>
    change (if v.1 = v'.1 then 1 + noiseLeafCommonDepth n
      (cascadeSeedLeaf n (fun j => ψ (j+1)) (z+ψ 0 z v.2.1) v.2.2)
      (cascadeSeedLeaf n (fun j => ψ (j+1)) (w+ψ 0 w v'.2.1) v'.2.2) else 0) = _
    rw [ih]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_NoiseReplicaPairData
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint branch-depth and two-mark-path observable on noise replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma measurable_noiseReplicaPairData {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (noiseReplicaPairData (A := A) n) := by
  change Measurable (fun σ : ℕ → NoiseLeaf A n =>
    (noiseLeafCommonDepth n (σ 0) (σ 1),
      fun i => (noiseLeafMark n (σ 0) i,noiseLeafMark n (σ 1) i)))
  apply Measurable.prodMk
  · have hp : Measurable (fun σ : ℕ → NoiseLeaf A n => (σ 0,σ 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    exact (measurable_noiseLeafCommonDepth (A := A) (B := A) n).comp hp
  · exact Measurable.of_eval fun i =>
      ((measurable_noiseLeafMark n i).comp (measurable_pi_apply 0)).prodMk
        ((measurable_noiseLeafMark n i).comp (measurable_pi_apply 1))

lemma noiseReplicaPairData_keep_labeled {A S : Type} [MeasurableSpace A]
    (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (T : LabeledTree n) (g : ForestVertex n → A) (σ : ℕ → LabeledLeaf n)
    (hdepth : noiseLeafCommonDepth n
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (T,markForestOfCoords A n g) (σ 0)))
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (T,markForestOfCoords A n g) (σ 1))) =
        labeledCommonDepth n (σ 0) (σ 1)) :
    noiseReplicaPairData n (fun i => noiseLeafKeep n c u s
      (labeledNoiseLeaf A n (T,markForestOfCoords A n g) (σ i))) =
      (labeledCommonDepth n (σ 0) (σ 1),fun i => (g (edgeAt n (σ 0) i),g (edgeAt n (σ 1) i))) := by
  apply Prod.ext hdepth
  funext i
  simp only [noiseReplicaPairData,noiseLeafMark_keep,noiseLeafMark_labeled]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_SamplingIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling Independent. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

lemma independent_marks_sampling {Ω G X : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace X] (P : Measure Ω) (Q : Measure G) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (K : Kernel Ω X) [IsMarkovKernel K] :
    ((P.prod Q) ⊗ₘ K.comap Prod.fst measurable_fst).map (fun p => (p.2,p.1.2)) =
      (K ∘ₘ P).prod Q := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  simp only [Kernel.comap_apply]
  have hI : Measurable (fun p : Ω × G => ∫⁻ x, F (x,p.2) ∂K p.1) :=
    (show Measurable (fun p : (Ω × G) × X => F (p.2,p.1.2)) from by fun_prop).lintegral_kernel_prod_right' (κ := K.comap Prod.fst measurable_fst)
  rw [lintegral_prod _ hI.aemeasurable]
  have he (ω : Ω) : (∫⁻ g, ∫⁻ x, F (x,g) ∂K ω ∂Q) = ∫⁻ x, ∫⁻ g, F (x,g) ∂Q ∂K ω :=
    lintegral_lintegral_swap (by fun_prop)
  simp_rw [he]
  rw [lintegral_prod _ hF.aemeasurable]
  exact (Measure.lintegral_bind (Kernel.aemeasurable K) (hF.lintegral_prod_right').aemeasurable).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CoordinatePairData
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable labeled two-path observable in the original forest coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma measurable_coordinatePairData {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (coordinatePairData (A := A) n) := by
  have hE : Measurable (fun p : (ForestVertex n → A) × LabeledLeaf n =>
      fun i => p.1 (edgeAt n p.2 i)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact Measurable.of_eval fun i => measurable_pi_apply (edgeAt n α i)
  have hp (j : ℕ) : Measurable (fun p : (ForestVertex n → A) × (ℕ → LabeledLeaf n) =>
      (p.1,p.2 j)) := measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
  have hd : Measurable (fun p : (ForestVertex n → A) × (ℕ → LabeledLeaf n) =>
      (p.2 0,p.2 1)) := ((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd)
  exact ((measurable_of_countable (fun q : LabeledLeaf n × LabeledLeaf n =>
    labeledCommonDepth n q.1 q.2)).comp hd).prodMk (Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp (hE.comp (hp 0))).prodMk
        ((measurable_pi_apply i).comp (hE.comp (hp 1))))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n with
  | zero => simp
  | succ n => simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PoissonScaledWeights
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct active Poisson weights after deterministic positive rescaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal NNReal
namespace InvariantIsing

lemma independent_scaled_ne (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν] (c d : ℝ) (hd : d ≠ 0) :
    ∀ᵐ p : ℝ × ℝ ∂μ.prod ν, c * p.1 ≠ d * p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)).compl).mpr
  refine ae_of_all _ fun x => ?_
  have h : ∀ᵐ y ∂ν, y ≠ c * x / d := by
    rw [ae_iff]
    convert (measure_singleton (c * x / d) : ν {c * x / d} = 0) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext y
    simp
  filter_upwards [h] with y hy he
  apply hy
  exact (eq_div_iff hd).mpr (by simpa only [Pi.mul_apply, mul_comm] using he.symm)

lemma finiteMeasure_normalize_noAtoms (μ : FiniteMeasure ℝ)
    [NullSingletonClass (μ : Measure ℝ)] (hμ : μ ≠ 0) :
    NullSingletonClass (μ.normalize : Measure ℝ) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero hμ]
  constructor
  intro x
  simp only [Measure.smul_apply, measure_singleton, smul_zero]

lemma finitePoissonCloud_point_law (μ : FiniteMeasure ℝ) (i : ℕ) :
    MeasurePreserving (fun p : ℕ × (ℕ → ℝ) => p.2 i)
      (finitePoissonCloud μ.mass (μ.normalize : Measure ℝ)) (μ.normalize : Measure ℝ) := by
  exact (measurePreserving_eval_infinitePi _ i).comp
    (measurePreserving_snd (μ := poissonMeasure μ.mass)
      (ν := Measure.infinitePi fun _ : ℕ => (μ.normalize : Measure ℝ)))

lemma finitePoissonCloud_zero_inactive (i : ℕ) :
    ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud (0 : FiniteMeasure ℝ).mass
      ((0 : FiniteMeasure ℝ).normalize : Measure ℝ), ¬ i < p.1 := by
  have h : ∀ᵐ n : ℕ ∂poissonMeasure (0 : FiniteMeasure ℝ).mass, n = 0 := by
    simp [poissonMeasure_zero_eq_dirac]
  have hm := (measurePreserving_fst (μ := poissonMeasure (0 : FiniteMeasure ℝ).mass)
    (ν := Measure.infinitePi fun _ : ℕ => ((0 : FiniteMeasure ℝ).normalize : Measure ℝ)))
  filter_upwards [hm.quasiMeasurePreserving.tendsto_ae.eventually h] with p hp
  simp [hp]

lemma finitePoissonCloud_scaled_distinct (μ : FiniteMeasure ℝ)
    [NullSingletonClass (μ : Measure ℝ)] (hμ : μ ≠ 0)
    (i j : ℕ) (hij : i ≠ j) (c d : ℝ) (hd : d ≠ 0) :
    ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud μ.mass (μ.normalize : Measure ℝ),
      c * p.2 i ≠ d * p.2 j := by
  let : NullSingletonClass (μ.normalize : Measure ℝ) := finiteMeasure_normalize_noAtoms μ hμ
  have hpair : MeasurePreserving (fun g : ℕ → ℝ => (g i,g j))
      (Measure.infinitePi fun _ : ℕ => (μ.normalize : Measure ℝ))
      ((μ.normalize : Measure ℝ).prod (μ.normalize : Measure ℝ)) :=
    ⟨by fun_prop, Measure.infinitePi_map_eval_prod hij⟩
  exact ((hpair.comp (measurePreserving_snd (μ := poissonMeasure μ.mass)
    (ν := Measure.infinitePi fun _ : ℕ => (μ.normalize : Measure ℝ)))).quasiMeasurePreserving.tendsto_ae.eventually
      (independent_scaled_ne _ _ c d hd))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PoissonLabeledWeights
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive rescaling cannot merge active labeled Poisson points. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

lemma labeledPoisson_scaled_pair (μ : ℕ → FiniteMeasure ℝ)
    [∀ n, NullSingletonClass (μ n : Measure ℝ)]
    (a b : ChildLabel) (hab : a ≠ b) (c d : ℝ) (hd : d ≠ 0) :
    ∀ᵐ ω ∂labeledPoissonLaw μ,
      a.2 < (ω a.1).1 → b.2 < (ω b.1).1 → c * (ω a.1).2 a.2 ≠ d * (ω b.1).2 b.2 := by
  have hev (m : ℕ) := measurePreserving_eval_infinitePi
    (fun j => finitePoissonCloud (μ j).mass ((μ j).normalize : Measure ℝ)) m
  by_cases ha : μ a.1 = 0
  · have hno : ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud (μ a.1).mass
        ((μ a.1).normalize : Measure ℝ), ¬ a.2 < p.1 := by
      rw [ha]
      exact finitePoissonCloud_zero_inactive a.2
    exact ((hev a.1).quasiMeasurePreserving.tendsto_ae.eventually hno).mono
      (fun ω hω hactive _ => (hω hactive).elim)
  by_cases hb : μ b.1 = 0
  · have hno : ∀ᵐ p : ℕ × (ℕ → ℝ) ∂finitePoissonCloud (μ b.1).mass
        ((μ b.1).normalize : Measure ℝ), ¬ b.2 < p.1 := by
      rw [hb]
      exact finitePoissonCloud_zero_inactive b.2
    exact ((hev b.1).quasiMeasurePreserving.tendsto_ae.eventually hno).mono
      (fun ω hω _ hactive => (hω hactive).elim)
  by_cases hm : a.1 = b.1
  · have hij : a.2 ≠ b.2 := fun h => hab (Prod.ext hm h)
    have h := finitePoissonCloud_scaled_distinct (μ a.1) ha a.2 b.2 hij c d hd
    exact ((hev a.1).quasiMeasurePreserving.tendsto_ae.eventually h).mono
      (fun ω hω _ _ => by simpa only [hm] using hω)
  · have hp : MeasurePreserving (fun ω : WeightCloud => (ω a.1,ω b.1))
        (labeledPoissonLaw μ)
        ((finitePoissonCloud (μ a.1).mass ((μ a.1).normalize : Measure ℝ)).prod
          (finitePoissonCloud (μ b.1).mass ((μ b.1).normalize : Measure ℝ))) :=
      ⟨by fun_prop, Measure.infinitePi_map_eval_prod hm⟩
    have hq := ((finitePoissonCloud_point_law (μ a.1) a.2).prod
      (finitePoissonCloud_point_law (μ b.1) b.2)).comp hp
    let : NullSingletonClass ((μ b.1).normalize : Measure ℝ) :=
      finiteMeasure_normalize_noAtoms _ hb
    exact (hq.quasiMeasurePreserving.tendsto_ae.eventually
      (independent_scaled_ne _ _ c d hd)).mono (fun _ h _ _ => h)

lemma labeledPoisson_scaled_distinct (μ : ℕ → FiniteMeasure ℝ)
    [∀ n, NullSingletonClass (μ n : Measure ℝ)]
    (c : ChildLabel → ℝ) (hc : ∀ a, c a ≠ 0) :
    ∀ᵐ ω ∂labeledPoissonLaw μ, ∀ a b : ChildLabel,
      a.2 < (ω a.1).1 → b.2 < (ω b.1).1 →
      c a * (ω a.1).2 a.2 = c b * (ω b.1).2 b.2 → a = b := by
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  by_cases h : a = b
  · exact ae_of_all _ (fun _ _ _ _ => h)
  · exact (labeledPoisson_scaled_pair μ a b h (c a) (c b) (hc b)).mono
      (fun _ hh ha hb he => (hh ha hb he).elim)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_LabeledScaledAncestry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive ancestor-dependent reweighting preserves the sampled branch labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing
variable {A S : Type} [MeasurableSpace A]

lemma labeledCascade_scaled_simple_ae (n : ℕ) (b : ℕ → ℝ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (hc : ∀ i p, c i p ≠ 0) (s : S) (z : MarkForest A n) :
    ∀ᵐ ω ∂(labeledCascadeLaw n b : Measure (LabeledTree n)), ScaledLabelSimple n c u s ω z := by
  induction n generalizing b c u s with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    let bs := fun i => b (i+1)
    let Q : Measure (ℕ → ℕ → LabeledTree n) := Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => (labeledCascadeLaw n bs : Measure (LabeledTree n))
    have hchildren : ∀ᵐ ω ∂Q, ∀ a : ChildLabel,
        ScaledLabelSimple n (fun j => c (j+1)) (fun j => u (j+1))
          (u 0 (s,(z a.1 a.2).1)) (ω a.1 a.2) (z a.1 a.2).2 := by
      rw [ae_all_iff]
      intro a
      have hp := (measurePreserving_eval_infinitePi
        (fun _ : ℕ => (labeledCascadeLaw n bs : Measure (LabeledTree n))) a.2).comp
        (measurePreserving_eval_infinitePi
          (fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
            (labeledCascadeLaw n bs : Measure (LabeledTree n))) a.1)
      exact hp.quasiMeasurePreserving.tendsto_ae.eventually
        (ih bs _ _ (fun i p => hc (i+1) p) _ (z a.1 a.2).2)
    have hroot := labeledPoisson_scaled_distinct (intensityComponents (powerIntensity (b 0)))
      (fun a : ChildLabel => c 0 (s,(z a.1 a.2).1)) (fun a => hc 0 _)
    have hfst := (measurePreserving_fst
      (μ := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))) (ν := Q)).quasiMeasurePreserving.tendsto_ae.eventually hroot
    have hsnd := (measurePreserving_snd
      (μ := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))) (ν := Q)).quasiMeasurePreserving.tendsto_ae.eventually hchildren
    filter_upwards [hfst,hsnd] with ω hω hω'
    exact ⟨hω,hω'⟩

lemma labeledLeafWeight_active {n : ℕ} (ω : LabeledTree (n+1))
    (v : LabeledLeaf (n+1)) (hv : labeledLeafWeight (n+1) ω v ≠ 0) :
    v.1.2 < (ω.1 v.1.1).1 := by
  by_contra h
  exact hv (by simp [labeledLeafWeight,childLabelWeight,h])

lemma noiseLeafCommonDepth_keep_labeled (n : ℕ) (c : ℕ → S × A → ℝ)
    (u : ℕ → S × A → S) (s : S) (ω : LabeledTree n) (z : MarkForest A n)
    (hω : ScaledLabelSimple n c u s ω z)
    (v w : LabeledLeaf n) (hv : labeledLeafWeight n ω v ≠ 0)
    (hw : labeledLeafWeight n ω w ≠ 0) :
    noiseLeafCommonDepth n
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (ω,z) v))
      (noiseLeafKeep n c u s (labeledNoiseLeaf A n (ω,z) w)) = labeledCommonDepth n v w := by
  induction n generalizing c u s with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨a,v⟩
    rcases w with ⟨a',w⟩
    have hva := labeledLeafWeight_active ω (a,v) hv
    have hwa := labeledLeafWeight_active ω (a',w) hw
    have hvt : labeledLeafWeight n (ω.2 a.1 a.2) v ≠ 0 := (mul_ne_zero_iff.mp hv).2
    have hwt : labeledLeafWeight n (ω.2 a'.1 a'.2) w ≠ 0 := (mul_ne_zero_iff.mp hw).2
    by_cases he : a = a'
    · subst a'
      simp only [noiseLeafKeep,labeledNoiseLeaf,noiseLeafCommonDepth,labeledCommonDepth,ite_true, if_true]
      rw [ih _ _ _ _ _ (hω.2 a) v w hvt hwt, Nat.add_comm]
    · have hne : c 0 (s,(z a.1 a.2).1) * (ω.1 a.1).2 a.2 ≠
          c 0 (s,(z a'.1 a'.2).1) * (ω.1 a'.1).2 a'.2 :=
        fun hh => he (hω.1 a a' hva hwa hh)
      simp only [noiseLeafKeep,labeledNoiseLeaf,noiseLeafCommonDepth,labeledCommonDepth,
        ite_eq_right he]
      exact ite_eq_right hne

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_LabeledAncestrySampling
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure ancestry preservation on the labeled sampling space. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S]

lemma labeled_ancestry_preserved_ae (n : ℕ) (b : ℕ → ℝ)
    (ν : Measure (MarkForest A n)) [IsProbabilityMeasure ν]
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcne : ∀ i p, c i p ≠ 0) (s : S) :
    ∀ᵐ p ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod ν,
      ∀ v w : LabeledLeaf n, labeledLeafWeight n p.1 v ≠ 0 → labeledLeafWeight n p.1 w ≠ 0 →
        noiseLeafCommonDepth n
          (noiseLeafKeep n c u s (labeledNoiseLeaf A n p v))
          (noiseLeafKeep n c u s (labeledNoiseLeaf A n p w)) = labeledCommonDepth n v w := by
  rw [ae_all_iff]
  intro v
  rw [ae_all_iff]
  intro w
  have hm (a : LabeledLeaf n) : Measurable (fun p : LabeledTree n × MarkForest A n =>
      noiseLeafKeep n c u s (labeledNoiseLeaf A n p a)) :=
    (measurable_noiseLeafKeep n hc hu).comp
      (measurable_const.prodMk (measurable_labeledNoiseLeaf A n a))
  have he : MeasurableSet {p : LabeledTree n × MarkForest A n |
      noiseLeafCommonDepth n (noiseLeafKeep n c u s (labeledNoiseLeaf A n p v))
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n p w)) = labeledCommonDepth n v w} :=
    measurableSet_eq_fun ((measurable_noiseLeafCommonDepth n).comp ((hm v).prodMk (hm w))) measurable_const
  have hs : MeasurableSet {p : LabeledTree n × MarkForest A n |
      labeledLeafWeight n p.1 v ≠ 0 → labeledLeafWeight n p.1 w ≠ 0 →
        noiseLeafCommonDepth n (noiseLeafKeep n c u s (labeledNoiseLeaf A n p v))
          (noiseLeafKeep n c u s (labeledNoiseLeaf A n p w)) = labeledCommonDepth n v w} :=
    (measurableSet_eq_fun ((measurable_labeledLeafWeight n v).comp measurable_fst) measurable_const).compl.imp
      ((measurableSet_eq_fun ((measurable_labeledLeafWeight n w).comp measurable_fst) measurable_const).compl.imp he)
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  apply (Measure.ae_ae_comm hs).mpr
  exact ae_of_all _ fun z => (labeledCascade_scaled_simple_ae n b c u hcne s z).mono
    (fun ω hω hv hw => noiseLeafCommonDepth_keep_labeled n c u s ω z hω v w hv hw)

lemma labeledLeafLaw_positive_weight (n : ℕ) (ω : LabeledTree n)
    (hω : 0 < rawTreeTotal n (labeledTreeForget n ω) ∧ rawTreeTotal n (labeledTreeForget n ω) < ∞) :
    ∀ᵐ v ∂labeledLeafLaw n ω, labeledLeafWeight n ω v ≠ 0 := by
  rw [labeledLeafLaw, normalizeMass, ite_eq_left (by simpa only [labeledLeafMass_univ] using hω)]
  apply Measure.ae_smul_measure
  rw [ae_iff]
  have hz : {v : LabeledLeaf n | ¬labeledLeafWeight n ω v ≠ 0} =
      {v : LabeledLeaf n | labeledLeafWeight n ω v = 0} := by ext v; simp
  rw [hz,labeledLeafMass,withDensity_apply _ (Set.to_countable _).measurableSet]
  apply setLIntegral_eq_zero (Set.to_countable _).measurableSet
  intro v hv
  exact hv

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_LabeledReplicaAncestry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ancestry preservation under any absolutely continuous labeled Gibbs sampling. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma gibbsProbability_absolutelyContinuous {X : Type} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) : gibbsProbability ν H ≪ ν := by
  unfold gibbsProbability
  split_ifs
  · exact Measure.AbsolutelyContinuous.rfl
  · exact tilted_absolutelyContinuous _ _

lemma labeledCascade_total_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    ∀ᵐ ω ∂(labeledCascadeLaw n b : Measure (LabeledTree n)),
      0 < rawTreeTotal n (labeledTreeForget n ω) ∧ rawTreeTotal n (labeledTreeForget n ω) < ⊤ := by
  have h : MeasurePreserving (labeledTreeForget n) (labeledCascadeLaw n b : Measure (LabeledTree n))
      (rawCascadeLaw n b : Measure (RawTree n)) :=
    ⟨measurable_labeledTreeForget n,labeledCascadeLaw_forget n b⟩
  exact h.quasiMeasurePreserving.tendsto_ae.eventually (rawCascade_total_moments n b hb).1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CoordinateReplicaAncestry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampled ancestry with the forest represented by its independent coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

theorem coordinate_sampled_ancestry_ae {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcne : ∀ i p, c i p ≠ 0) (s : S)
    (ν : LabeledTree n × (ForestVertex n → A) → Measure (LabeledLeaf n))
    (hν : Measurable ν) [∀ p, IsProbabilityMeasure (ν p)]
    (habs : ∀ p, ν p ≪ labeledLeafLaw n p.1) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi fun a : ForestVertex n => (μ (forestVertexDepth n a) : Measure A))
    ∀ᵐ q ∂P ⊗ₘ probabilityReplicaKernel ν hν,
      noiseLeafCommonDepth n
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n
          (q.1.1,markForestOfCoords A n q.1.2) (q.2 0)))
        (noiseLeafKeep n c u s (labeledNoiseLeaf A n
          (q.1.1,markForestOfCoords A n q.1.2) (q.2 1))) =
      labeledCommonDepth n (q.2 0) (q.2 1) := by
  intro P
  have hcoord : MeasurePreserving (fun p : LabeledTree n × (ForestVertex n → A) =>
      (p.1,markForestOfCoords A n p.2)) P
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (markForestLaw A n μ : Measure (MarkForest A n))) :=
    (MeasurePreserving.id _).prod
      ⟨measurable_markForestOfCoords A n,markForestOfCoords_law A n μ⟩
  have hroot := hcoord.quasiMeasurePreserving.tendsto_ae.eventually
    (labeled_ancestry_preserved_ae n b (markForestLaw A n μ : Measure (MarkForest A n)) c u hc hu hcne s)
  have hm : Measurable (fun p : (LabeledTree n × (ForestVertex n → A)) × LabeledLeaf n =>
      noiseLeafKeep n c u s (labeledNoiseLeaf A n
        (p.1.1,markForestOfCoords A n p.1.2) p.2)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_noiseLeafKeep n hc hu).comp
      (measurable_const.prodMk ((measurable_labeledNoiseLeaf A n α).comp hcoord.measurable))
  have hp (i : ℕ) : Measurable (fun q : (LabeledTree n × (ForestVertex n → A)) ×
      (ℕ → LabeledLeaf n) => (q.1,q.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((measurable_noiseLeafCommonDepth n).comp
      ((hm.comp (hp 0)).prodMk (hm.comp (hp 1))))
      ((measurable_of_countable (fun p : LabeledLeaf n × LabeledLeaf n =>
        labeledCommonDepth n p.1 p.2)).comp
        (((measurable_pi_apply 0).comp measurable_snd).prodMk
          ((measurable_pi_apply 1).comp measurable_snd))))
  have ht := (measurePreserving_fst (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (ν := Measure.infinitePi fun a : ForestVertex n =>
      (μ (forestVertexDepth n a) : Measure A))).quasiMeasurePreserving.tendsto_ae.eventually
        (labeledCascade_total_ae n b hb)
  filter_upwards [hroot,ht] with p hpath htotal
  have hpos := (habs p).ae_le (labeledLeafLaw_positive_weight n p.1 htotal)
  have h0 := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν p) 0).quasiMeasurePreserving.tendsto_ae.eventually hpos
  have h1 := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν p) 1).quasiMeasurePreserving.tendsto_ae.eventually hpos
  filter_upwards [h0,h1] with σ hσ0 hσ1
  exact hpath (σ 0) (σ 1) hσ0 hσ1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaPushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Observable pushforwards from a conditional replica law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma map_compProd_snd {Ω X Y : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) [SFinite P] (K : Kernel Ω X) [IsSFiniteKernel K]
    {F : X → Y} (hF : Measurable F) :
    (P ⊗ₘ K).map (fun p => F p.2) = (K ∘ₘ P).map F := by
  change (P ⊗ₘ K).map (F ∘ Prod.snd) = _
  rw [← Measure.map_map hF measurable_snd]
  change Measure.map F (P ⊗ₘ K).snd = _
  rw [Measure.snd_compProd]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_PairProductShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pairing the two independent root seeds separately from their two subforests. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma pairProductShuffle_preserving {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (η : Measure C) (ρ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite η] [SFinite ρ] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (η.prod ρ)) ((μ.prod η).prod (ν.prod ρ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (η.prod ρ)
  have h2 := (MeasurePreserving.id μ).prod
    ((measurePreserving_prodAssoc ν η ρ).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := η)).prod (MeasurePreserving.id ρ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc η ν ρ)
  have h5 := (measurePreserving_prodAssoc μ η (ν.prod ρ)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

lemma markForestPairRoots_preserving {A : Type} [MeasurableSpace A]
    (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (a b : ChildLabel) :
    MeasurePreserving (fun p : MarkForest A (n+1) × MarkForest A (n+1) =>
      (((p.1 a.1 a.2).1,(p.2 b.1 b.2).1),((p.1 a.1 a.2).2,(p.2 b.1 b.2).2)))
      ((markForestLaw A (n+1) μ : Measure (MarkForest A (n+1))).prod
        (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1))))
      (((μ 0 : Measure A).prod (μ 0 : Measure A)).prod
        ((markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)).prod
          (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)))) :=
  (pairProductShuffle_preserving _ _ _ _).comp
    ((markForestRoot_preserving n μ a).prod (markForestRoot_preserving n μ b))

lemma markForestDistinctRoots_preserving {A : Type} [MeasurableSpace A]
    (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (a b : ChildLabel) (hab : a ≠ b) :
    MeasurePreserving (fun g : MarkForest A (n+1) =>
      (((g a.1 a.2).1,(g b.1 b.2).1),((g a.1 a.2).2,(g b.1 b.2).2)))
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      (((μ 0 : Measure A).prod (μ 0 : Measure A)).prod
        ((markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)).prod
          (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)))) :=
  (pairProductShuffle_preserving _ _ _ _).comp (markForestRoots_preserving n μ a b hab)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeKeepUpdate
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite tree uses only the updates before its depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma noiseTreeKeep_update_congr {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (c : ℕ → S × A → ℝ) (u u' : ℕ → S × A → S)
    (hu : ∀ i < n, u i = u' i) (s : S) (T : NoiseTree A n) :
    noiseTreeKeep n b μ c u s T = noiseTreeKeep n b μ c u' s T := by
  induction n generalizing b μ c u u' s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeKeep
    congr 1
    funext p
    apply congrArg (fun V => (c 0 (s,p.2.1)*p.1,(p.2.1,V)))
    rw [hu 0 (by omega)]
    exact ih _ _ _ _ _ (fun i hi => hu (i+1) (by omega)) _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedRetainedLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full retained finite vector cascade is realized by ancestor-dependent seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

theorem cascadeSeedTree_retained_law {ι : Type} [Fintype ι]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (ι → ℝ))
    (c : ℕ → (ι → ℝ) × (ι → ℝ) → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hc : ∀ i, Measurable (c i)) (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (hcpos : ∀ i z a, 0 < c i (z,a))
    (hm : ∀ i z, (∫⁻ a, ENNReal.ofReal (c i (z,a)^b i) ∂(μ i : Measure (ι → ℝ))) = 1)
    (hseed : ∀ i z, volume.map (ψ i z) = (μ i : Measure (ι → ℝ)).withDensity
      (fun a => ENNReal.ofReal (c i (z,a)^b i))) (z : ι → ℝ) :
    (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) :
      Measure (NoiseTree unitInterval n)).map (cascadeSeedTree n b ψ z) =
    (noiseCascadeLaw (ι → ℝ) n b μ : Measure (NoiseTree (ι → ℝ) n)).map
      (noiseTreeKeep n b μ c (fun _ p => p.1+p.2) z) := by
  induction n generalizing b μ c ψ z with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) =
      (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit)
    rfl
  | succ n ih =>
    let bs := fun j => b (j+1)
    let ms := fun j => μ (j+1)
    let cs := fun j => c (j+1)
    let ps := fun j => ψ (j+1)
    let Q : Measure (NoiseTree unitInterval n) :=
      noiseCascadeLaw unitInterval n bs (fun _ => cascadeSeedLaw)
    let P : Measure (NoiseTree (ι → ℝ) n) := noiseCascadeLaw (ι → ℝ) n bs ms
    let ρ : Measure (ι → ℝ) := (μ 0 : Measure (ι → ℝ)).withDensity
      (fun a => ENNReal.ofReal (c 0 (z,a)^b 0))
    let : IsProbabilityMeasure ρ := ⟨by
      change ((μ 0 : Measure (ι → ℝ)).withDensity _ ) Set.univ = 1
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      exact hm 0 z⟩
    let : IsProbabilityMeasure Q := by
      change IsProbabilityMeasure (noiseCascadeLaw unitInterval n bs (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n))
      first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_cascadeSeedTree <;> assumption) | (apply Measurable.aemeasurable; apply measurable_noiseTreeKeep <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    let : IsProbabilityMeasure P := by
      change IsProbabilityMeasure (noiseCascadeLaw (ι → ℝ) n bs ms : Measure (NoiseTree (ι → ℝ) n))
      first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_cascadeSeedTree <;> assumption) | (apply Measurable.aemeasurable; apply measurable_noiseTreeKeep <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    let G : (ι → ℝ) × NoiseTree unitInterval n → NoiseTree (ι → ℝ) n :=
      fun p => cascadeSeedTree n bs ps (z+p.1) p.2
    let H : (ι → ℝ) × NoiseTree (ι → ℝ) n → NoiseTree (ι → ℝ) n :=
      fun p => noiseTreeKeep n bs ms cs (fun _ p => p.1+p.2) (z+p.1) p.2
    have hG : Measurable G := (measurable_cascadeSeedTree n bs ps (fun i => hψ (i+1))).comp
      ((measurable_const.add measurable_fst).prodMk measurable_snd)
    have hH : Measurable H :=
      (measurable_noiseTreeKeep n bs ms (fun i => hc (i+1))
        (fun _ => measurable_fst.add measurable_snd)).comp
          ((measurable_const.add measurable_fst).prodMk measurable_snd)
    have hsub a : Q.map (fun q => G (a,q)) = P.map (fun p => H (a,p)) :=
      ih bs ms cs ps (fun i => hc (i+1)) (fun i => hψ (i+1))
        (fun i => hcpos (i+1)) (fun i => hm (i+1)) (fun i => hseed (i+1)) (z+a)
    have hf : Measurable (ψ 0 z) := (hψ 0).comp (measurable_const.prodMk measurable_id)
    have hlaw : (cascadeSeedLaw : Measure unitInterval).map (ψ 0 z) = ρ := hseed 0 z
    have hpair := ancestor_fiber_map_product (cascadeSeedLaw : Measure unitInterval) ρ Q P hf hlaw hG hH hsub
    have hmap : Measurable (fun p : unitInterval × NoiseTree unitInterval n =>
        (ψ 0 z p.1,G (ψ 0 z p.1,p.2))) :=
      (hf.comp measurable_fst).prodMk (hG.comp ((hf.comp measurable_fst).prodMk measurable_snd))
    rw [cascadeSeedTree_law_succ n b ψ hψ z,
      noiseTreeKeep_law_succ n b μ (u := fun (_ : ℕ) (p : (ι → ℝ) × (ι → ℝ)) => p.1+p.2)
        hc (fun _ => measurable_fst.add measurable_snd) hcpos z]
    apply poissonLaw_congr
    change (((powerIntensity (b 0)).prod ((cascadeSeedLaw : Measure unitInterval).prod Q)).map
      (Prod.map id (fun p => (ψ 0 z p.1,G (ψ 0 z p.1,p.2))))) =
      (powerIntensity (b 0)).prod
        ((((μ 0 : Measure (ι → ℝ)).prod P).withDensity
          (fun p => ENNReal.ofReal (c 0 (z,p.1)^b 0))).map (fun p => (p.1,H p)))
    rw [← Measure.map_prod_map _ _ measurable_id hmap, Measure.map_id, hpair]
    congr 1
    congr 1
    exact prod_withDensity_left
      ((((hc 0).comp (measurable_const.prodMk measurable_id)).pow_const (b 0)).ennreal_ofReal)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedLeafLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling commutes with the ancestor-dependent seed marking. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing

theorem cascadeSeedLeaf_law {ι : Type} [Fintype ι] (n : ℕ) (b : ℕ → ℝ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (T : NoiseTree unitInterval n) (hT : CascadeSeedRegular n b T) (z : ι → ℝ) :
    (noiseLeafKernel unitInterval n T).map (cascadeSeedLeaf n ψ z) =
      noiseLeafKernel (ι → ℝ) n (cascadeSeedTree n b ψ z T) := by
  induction n generalizing b ψ z with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let G : ℝ × (unitInterval × NoiseTree unitInterval n) →
        ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) := fun p =>
      (p.1,(ψ 0 z p.2.1,cascadeSeedTree n (fun j => b (j+1)) (fun j => ψ (j+1))
        (z+ψ 0 z p.2.1) p.2.2))
    have hG : Measurable G := by
      have hm : Measurable (fun p : ℝ × (unitInterval × NoiseTree unitInterval n) => ψ 0 z p.2.1) :=
        (hψ 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))
      exact measurable_fst.prodMk (hm.prodMk
        ((measurable_cascadeSeedTree n _ _ (fun i => hψ (i+1))).comp
          ((measurable_const.add hm).prodMk (by fun_prop))))
    have htree : cascadeSeedTree (n+1) b ψ z T = T.map G := by
      change (sigmaPart _ T).map G = T.map G
      rw [cascadeSeedRegular_sigma hT]
    have htotal := cascadeSeedTree_total (n+1) b ψ hψ T hT z
    have ht := cascadeSeedRegular_total hT
    have htarget : 0 < noiseTreeTotal (ι → ℝ) (n+1) (cascadeSeedTree (n+1) b ψ z T) ∧
        noiseTreeTotal (ι → ℝ) (n+1) (cascadeSeedTree (n+1) b ψ z T) < ∞ := by
      rwa [htotal]
    have hleaf : Measurable (cascadeSeedLeaf (n+1) ψ z) :=
      (measurable_cascadeSeedLeaf (n+1) ψ hψ).comp (measurable_const.prodMk measurable_id)
    apply Measure.ext_of_lintegral
    intro F hF
    have hint : Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal (ι → ℝ) n p.2.2 *
          (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel (ι → ℝ) n p.2.2)) := by
      have hi := (hF.comp (show Measurable (fun p :
          (ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n)) × NoiseLeaf (ι → ℝ) n =>
          (p.1.1,(p.1.2.1,p.2))) from by fun_prop)).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel (ι → ℝ) n).comap
          (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) => p.2.2) (by fun_prop))
      exact ((by fun_prop : Measurable (fun p : ℝ × ((ι → ℝ) × NoiseTree (ι → ℝ) n) =>
        ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal (ι → ℝ) n).comp (by fun_prop))).mul hi
    rw [lintegral_map hF hleaf,
      noiseLeafKernel_lintegral (A := unitInterval) n T ht
        (F := fun v => F (cascadeSeedLeaf (n+1) ψ z v)) (hF.comp hleaf),
      noiseLeafKernel_lintegral (A := ι → ℝ) n _ htarget hF, htotal, htree,
      lintegral_map hint hG]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [cascadeSeedRegular_tail hT] with p hp
    have hchild := ih (fun j => b (j+1)) (fun j => ψ (j+1)) (fun i => hψ (i+1))
      p.2.2 hp (z+ψ 0 z p.2.1)
    have hFp : Measurable (fun v : NoiseLeaf (ι → ℝ) n => F (p.1,(ψ 0 z p.2.1,v))) :=
      hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun ν : Measure (NoiseLeaf (ι → ℝ) n) =>
      ∫⁻ v, F (p.1,(ψ 0 z p.2.1,v)) ∂ν) hchild
    rw [lintegral_map (g := cascadeSeedLeaf n (fun j => ψ (j+1)) (z+ψ 0 z p.2.1)) hFp
      ((measurable_cascadeSeedLeaf n _ (fun i => hψ (i+1))).comp
        (measurable_const.prodMk measurable_id))] at he
    dsimp only [G, cascadeSeedLeaf]
    rw [cascadeSeedTree_total _ _ _ (fun i => hψ (i+1)) _ hp]
    rw [he]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint replica law under the finite ancestor-seed construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

theorem cascadeSeed_replica_law {ι : Type} [Fintype ι] (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
      probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
      (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) =
    probabilityReplicaKernel (noiseLeafKernel (ι → ℝ) n) (noiseLeafKernel (ι → ℝ) n).measurable ∘ₘ
      (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)).map
        (cascadeSeedTree n b ψ z) := by
  apply sampling_replica_morphism
    (P := (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)))
    (Q := (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)).map
      (cascadeSeedTree n b ψ z))
    (noiseLeafKernel unitInterval n).measurable (noiseLeafKernel (ι → ℝ) n).measurable
    ((measurable_cascadeSeedTree n b ψ hψ).comp (measurable_const.prodMk measurable_id)) rfl
    (ψ := fun _ v => cascadeSeedLeaf n ψ z v)
  · exact ((measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk measurable_id)).comp measurable_snd
  · filter_upwards [cascadeSeedRegular_ae n b hb] with T hT
    exact cascadeSeedLeaf_law n b ψ hψ T hT z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_GibbsMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pushforward of an integrable terminal Gibbs tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing

lemma gibbsProbability_map_normalize {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (ν : Measure X) [IsProbabilityMeasure ν]
    {f : X → Y} (hf : Measurable f) {H : Y → ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H (f x))) ν) :
    (gibbsProbability ν (fun x => H (f x))).map f =
      normalizeMass ((ν.map f).withDensity (fun y => ENNReal.ofReal (Real.exp (H y)))) := by
  have hI : Integrable (fun y => Real.exp (H y)) (ν.map f) :=
    (integrable_map_measure hH.exp.aestronglyMeasurable hf.aemeasurable).mpr hi
  have hmass : ((ν.map f).withDensity (fun y => ENNReal.ofReal (Real.exp (H y)))) Set.univ =
      ENNReal.ofReal (∫ y, Real.exp (H y) ∂ν.map f) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun y => (Real.exp_pos _).le)]
  rw [gibbsProbability_eq_tilted _ _ hi, ← normalizeMass_exp ν (fun x => H (f x)) (hH.comp hf) hi]
  apply normalizeMass_weight_map ν hf hH.exp.ennreal_ofReal
  rw [hmass]
  have : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  exact ⟨ENNReal.ofReal_pos.mpr (integral_exp_pos hI), ENNReal.ofReal_lt_top⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_ReferenceInfiniteReplicas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite reference replica mean as the initial coordinates of iid Gibbs replicas. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma referenceReplicaMean_infinite {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (D : (Fin r → X) → ℝ) (hD : Measurable D) :
    referenceReplicaMean ν H D =
      ∫ σ : ℕ → X, D (fun i => σ i) ∂Measure.infinitePi (fun _ : ℕ => gibbsProbability ν H) := by
  let := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he]
  simp_rw [gibbsProbability_eq_tilted ν H he]
  have hp : MeasurePreserving (fun σ : ℕ → X => fun i : Fin r => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν.tilted H)) (Measure.pi (fun _ : Fin r => ν.tilted H)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]
  exact (hp.hasLaw.integral_comp hD.aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeUnweightedAncestry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common prefix of sampled unweighted leaves is their labeled common prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma noiseLeafKeep_one {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (v : NoiseLeaf A n) :
    noiseLeafKeep n (fun _ (_ : PUnit × A) => 1) (fun _ _ => PUnit.unit) PUnit.unit v = v := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change (1 * v.1,(v.2.1,noiseLeafKeep n _ _ _ v.2.2)) = v
    rw [one_mul,ih]

lemma coordinate_unweighted_depth_ae {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi fun a : ForestVertex n => (μ (forestVertexDepth n a) : Measure A))
    ∀ᵐ q ∂P ⊗ₘ probabilityReplicaKernel (fun p => labeledLeafLaw n p.1)
        ((measurable_labeledLeafLaw n).comp measurable_fst),
      noiseLeafCommonDepth n
        (labeledNoiseLeaf A n (q.1.1,markForestOfCoords A n q.1.2) (q.2 0))
        (labeledNoiseLeaf A n (q.1.1,markForestOfCoords A n q.1.2) (q.2 1)) =
      labeledCommonDepth n (q.2 0) (q.2 1) := by
  simpa only [noiseLeafKeep_one] using coordinate_sampled_ancestry_ae n b hb μ
    (fun _ (_ : PUnit × A) => 1) (fun _ _ => PUnit.unit)
    (fun _ => measurable_const) (fun _ => measurable_const) (fun _ _ => one_ne_zero)
    PUnit.unit (fun p => labeledLeafLaw n p.1)
    ((measurable_labeledLeafLaw n).comp measurable_fst) (fun _ => Measure.AbsolutelyContinuous.rfl)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedForestPairData
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A pair of ancestor-generated paths on the independent uniform forest. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

lemma measurable_seedForestPairData (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    Measurable (seedForestPairData n ψ z) := by
  have hm : Measurable (fun p : LabeledLeaf n × MarkForest unitInterval n =>
      cascadeSeedPath n ψ z p.2 p.1) := by
    apply measurable_from_prod_countable_right
    intro α
    exact (measurable_cascadeSeedPath n ψ hψ α).comp (measurable_const.prodMk measurable_id)
  change Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
    (labeledCommonDepth n (q.1 0) (q.1 1),fun i =>
      (cascadeSeedPath n ψ z q.2 (q.1 0) i,cascadeSeedPath n ψ z q.2 (q.1 1) i)))
  apply Measurable.prodMk
  · have hp : Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
        (q.1 0,q.1 1)) :=
      ((measurable_pi_apply 0).comp measurable_fst).prodMk
        ((measurable_pi_apply 1).comp measurable_fst)
    exact (measurable_of_countable (fun p : LabeledLeaf n × LabeledLeaf n =>
      labeledCommonDepth n p.1 p.2)).comp hp
  · have hp (j : ℕ) : Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
        (q.1 j,q.2)) :=
      ((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd
    exact Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp (hm.comp (hp 0))).prodMk
      ((measurable_pi_apply i).comp (hm.comp (hp 1)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CascadeSeedPairCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint seed paths and branch depth after removing the random tree coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem cascade_seed_pair_coordinates (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ) :
    ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
      probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
        (fun p => noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) =
    ((cascadeReplicaLaw n b).prod
      (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))).map
        (seedForestPairData n ψ z) := by
  let Q := Measure.infinitePi (fun _ : ForestVertex n => (cascadeSeedLaw : Measure unitInterval))
  let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod Q
  let K := probabilityReplicaKernel (labeledLeafLaw n) (measurable_labeledLeafLaw n)
  let Ψ := fun p : (LabeledTree n × (ForestVertex n → unitInterval)) × (ℕ → LabeledLeaf n) =>
    fun i => labeledNoiseLeaf unitInterval n (p.1.1,markForestOfCoords unitInterval n p.1.2) (p.2 i)
  let F := fun σ : ℕ → NoiseLeaf unitInterval n =>
    noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (σ i))
  let G := fun p : (ℕ → LabeledLeaf n) × (ForestVertex n → unitInterval) =>
    seedForestPairData n ψ z (p.1,markForestOfCoords unitInterval n p.2)
  have hF : Measurable F := (measurable_noiseReplicaPairData n).comp
    (Measurable.of_eval fun i => (measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk (measurable_pi_apply i)))
  have hG : Measurable G := (measurable_seedForestPairData n ψ hψ z).comp
    (measurable_fst.prodMk ((measurable_markForestOfCoords unitInterval n).comp measurable_snd))
  have hΨ : Measurable Ψ := by
    apply Measurable.of_eval
    intro i
    have hm : Measurable (fun p : (LabeledTree n × (ForestVertex n → unitInterval)) × LabeledLeaf n =>
        labeledNoiseLeaf unitInterval n (p.1.1,markForestOfCoords unitInterval n p.1.2) p.2) := by
      apply measurable_from_prod_countable_left
      intro α
      exact (measurable_labeledNoiseLeaf unitInterval n α).comp (by fun_prop)
    exact hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  rw [map_compProd_snd _ _ hF]
  change (markedReplicaLaw n b (fun _ => cascadeSeedLaw)).map F = _
  rw [← labeled_marked_replica_law n b hb (fun _ => cascadeSeedLaw),Measure.map_map hF hΨ]
  have he := independent_marks_sampling (labeledCascadeLaw n b : Measure (LabeledTree n)) Q K
  change (P ⊗ₘ K.comap Prod.fst measurable_fst).map (fun p => (p.2,p.1.2)) =
    (cascadeReplicaLaw n b).prod Q at he
  have hforest : ((cascadeReplicaLaw n b).prod Q).map
      (fun p => (p.1,markForestOfCoords unitInterval n p.2)) =
      (cascadeReplicaLaw n b).prod
        (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n)) := by
    change ((cascadeReplicaLaw n b).prod Q).map
      (Prod.map id (markForestOfCoords unitInterval n)) = _
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_markForestOfCoords unitInterval n),
      Measure.map_id]
    exact congrArg ((cascadeReplicaLaw n b).prod)
      (markForestOfCoords_law unitInterval n (fun _ => cascadeSeedLaw))
  rw [← hforest,Measure.map_map (measurable_seedForestPairData n ψ hψ z) (by fun_prop)]
  change (P ⊗ₘ K.comap Prod.fst measurable_fst).map (F ∘ Ψ) = ((cascadeReplicaLaw n b).prod Q).map G
  rw [← he,Measure.map_map hG (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [coordinate_unweighted_depth_ae n b hb (fun _ => cascadeSeedLaw)] with p hp
  apply Prod.ext
  · exact (noiseLeafCommonDepth_seed n ψ z z (Ψ p 0) (Ψ p 1)).trans hp
  · funext i
    exact Prod.ext (congrFun (cascadeSeedPath_labeled n ψ z p.1.1
      (markForestOfCoords unitInterval n p.1.2) (p.2 0)) i)
      (congrFun (cascadeSeedPath_labeled n ψ z p.1.1
        (markForestOfCoords unitInterval n p.1.2) (p.2 1)) i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedPairRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite two-path recursion for the ancestor-dependent uniform seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

lemma measurable_finCons {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} {a : X → Y} {w : X → Fin n → Y} (ha : Measurable a) (hw : Measurable w) :
    Measurable (fun x => (Fin.cons (a x) (w x) : Fin (n+1) → Y)) := by
  apply Measurable.of_eval
  intro i
  exact Fin.cases ha (fun j => (measurable_pi_apply j).comp hw) i

lemma measurable_seedPairPathMean (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (d : ℕ)
    {X : Type*} [MeasurableSpace X] (z₁ z₂ : X → (ι → ℝ))
    (h₁ : Measurable z₁) (h₂ : Measurable z₂)
    (F : X → (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => seedPairPathMean n ψ d (z₁ x) (z₂ x) (F x)) := by
  induction n generalizing X ψ d with
  | zero => exact hF.comp (measurable_id.prodMk measurable_const)
  | succ n ih =>
    cases d with
    | zero =>
      have hA : Measurable (fun p : X × (unitInterval × unitInterval) => ψ 0 (z₁ p.1) p.2.1) :=
        (hψ 0).comp ((h₁.comp measurable_fst).prodMk measurable_snd.fst)
      have hB : Measurable (fun p : X × (unitInterval × unitInterval) => ψ 0 (z₂ p.1) p.2.2) :=
        (hψ 0).comp ((h₂.comp measurable_fst).prodMk measurable_snd.snd)
      have hC : Measurable (fun p : (X × (unitInterval × unitInterval)) ×
          (Fin n → (ι → ℝ) × (ι → ℝ)) =>
          F p.1.1 (Fin.cons (ψ 0 (z₁ p.1.1) p.1.2.1,ψ 0 (z₂ p.1.1) p.1.2.2) p.2)) :=
        hF.comp (measurable_fst.fst.prodMk
          (measurable_finCons ((hA.comp measurable_fst).prodMk (hB.comp measurable_fst)) measurable_snd))
      exact (ih (fun i => ψ (i+1)) (fun i => hψ (i+1)) 0
        (fun p : X × (unitInterval × unitInterval) => z₁ p.1+ψ 0 (z₁ p.1) p.2.1)
        (fun p => z₂ p.1+ψ 0 (z₂ p.1) p.2.2)
        ((h₁.comp measurable_fst).add hA) ((h₂.comp measurable_fst).add hB)
        (fun p w => F p.1 (Fin.cons (ψ 0 (z₁ p.1) p.2.1,ψ 0 (z₂ p.1) p.2.2) w)) hC
        ).stronglyMeasurable.integral_prod_right.measurable
    | succ d =>
      have hA : Measurable (fun p : X × unitInterval => ψ 0 (z₁ p.1) p.2) :=
        (hψ 0).comp ((h₁.comp measurable_fst).prodMk measurable_snd)
      have hB : Measurable (fun p : X × unitInterval => ψ 0 (z₂ p.1) p.2) :=
        (hψ 0).comp ((h₂.comp measurable_fst).prodMk measurable_snd)
      have hC : Measurable (fun p : (X × unitInterval) ×
          (Fin n → (ι → ℝ) × (ι → ℝ)) =>
          F p.1.1 (Fin.cons (ψ 0 (z₁ p.1.1) p.1.2,ψ 0 (z₂ p.1.1) p.1.2) p.2)) :=
        hF.comp (measurable_fst.fst.prodMk
          (measurable_finCons ((hA.comp measurable_fst).prodMk (hB.comp measurable_fst)) measurable_snd))
      exact (ih (fun i => ψ (i+1)) (fun i => hψ (i+1)) d
        (fun p : X × unitInterval => z₁ p.1+ψ 0 (z₁ p.1) p.2)
        (fun p => z₂ p.1+ψ 0 (z₂ p.1) p.2)
        ((h₁.comp measurable_fst).add hA) ((h₂.comp measurable_fst).add hB)
        (fun p w => F p.1 (Fin.cons (ψ 0 (z₁ p.1) p.2,ψ 0 (z₂ p.1) p.2) w)) hC
        ).stronglyMeasurable.integral_prod_right.measurable

private lemma seed_abs_integral_bound {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (f : A → ℝ) {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) : |∫ a, f a ∂μ| ≤ C := by
  have hh : ∀ᵐ a ∂μ, ‖f a‖ ≤ C := ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs] using hf a
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) hh

lemma seedPairPathMean_abs_le (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) (d : ℕ) (z₁ z₂ : ι → ℝ)
    (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) {C : ℝ} (hF : ∀ w, |F w| ≤ C) :
    |seedPairPathMean n ψ d z₁ z₂ F| ≤ C := by
  induction n generalizing ψ d z₁ z₂ with
  | zero => exact hF _
  | succ n ih =>
    cases d <;> simp only [seedPairPathMean]
    all_goals
      apply seed_abs_integral_bound
      intro u
      exact ih _ _ _ _ _ (fun w => hF _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedIndependentKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing independent uniform seeds by their normalized conditional mark kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_independent_kernel (n : ℕ) (κ : ℕ → Kernel (ι → ℝ) (ι → ℝ))
    (hκ : ∀ i, IsMarkovKernel (κ i))
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (hlaw : ∀ i z, volume.map (ψ i z) = κ i z) (z₁ z₂ : ι → ℝ)
    (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) (hF : Measurable F)
    {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    seedPairPathMean n ψ 0 z₁ z₂ F = markPairPathMean n κ 0 z₁ z₂ F := by
  induction n generalizing κ ψ z₁ z₂ with
  | zero => rfl
  | succ n ih =>
    let H := fun p : (ι → ℝ) × (ι → ℝ) =>
      seedPairPathMean n (fun j => ψ (j+1)) 0 (z₁+p.1) (z₂+p.2)
        (fun w => F (Fin.cons (p.1,p.2) w))
    have hH : Measurable H := measurable_seedPairPathMean n (fun j => ψ (j+1))
      (fun j => hψ (j+1)) 0 (fun p : (ι → ℝ) × (ι → ℝ) => z₁+p.1) (fun p => z₂+p.2)
      (measurable_const.add measurable_fst) (measurable_const.add measurable_snd)
      (fun (p : (ι → ℝ) × (ι → ℝ)) w => F (Fin.cons (p.1,p.2) w))
      (hF.comp (measurable_finCons measurable_fst measurable_snd))
    have hP : MeasurePreserving (fun u : unitInterval × unitInterval =>
        (ψ 0 z₁ u.1,ψ 0 z₂ u.2)) (volume.prod volume) ((κ 0 z₁).prod (κ 0 z₂)) :=
      (show MeasurePreserving (ψ 0 z₁) volume (κ 0 z₁) from
        ⟨(hψ 0).comp (measurable_const.prodMk measurable_id),hlaw 0 z₁⟩).prod
      (show MeasurePreserving (ψ 0 z₂) volume (κ 0 z₂) from
        ⟨(hψ 0).comp (measurable_const.prodMk measurable_id),hlaw 0 z₂⟩)
    let := hκ 0
    have hiH : Integrable H ((κ 0 z₁).prod (κ 0 z₂)) :=
      Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using seedPairPathMean_abs_le n (fun j => ψ (j+1))
          0 (z₁+p.1) (z₂+p.2) (fun w => F (Fin.cons (p.1,p.2) w)) (fun w => hB _))
    calc
      _ = ∫ p, H p ∂(κ 0 z₁).prod (κ 0 z₂) := hP.hasLaw.integral_comp hH.aestronglyMeasurable
      _ = ∫ a₁, ∫ a₂, H (a₁,a₂) ∂κ 0 z₂ ∂κ 0 z₁ := integral_prod _ hiH
      _ = markPairPathMean (n+1) κ 0 z₁ z₂ F := by
        rw [markPairPathMean]
        apply integral_congr_ae
        apply ae_of_all
        intro a₁
        apply integral_congr_ae
        apply ae_of_all
        intro a₂
        exact ih (fun j => κ (j+1)) (fun j => hκ (j+1))
          (fun j => ψ (j+1)) (fun j => hψ (j+1)) (fun j z => hlaw (j+1) z)
          (z₁+a₁) (z₂+a₂) (fun w => F (Fin.cons (a₁,a₂) w))
          (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedIndependentPairEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two independent seed forests give the independent branch of the finite recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

private lemma zip_finCons {A B : Type*} {n : ℕ} (a : A) (b : B)
    (f : Fin n → A) (g : Fin n → B) :
    (fun i : Fin (n+1) => ((Fin.cons a f : Fin (n+1) → A) i,
      (Fin.cons b g : Fin (n+1) → B) i)) =
        (Fin.cons (a,b) (fun i => (f i,g i)) : Fin (n+1) → A × B) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem seed_independent_pair_evaluation (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z₁ z₂ : ι → ℝ)
    (α β : LabeledLeaf n) (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    (∫ g : MarkForest unitInterval n × MarkForest unitInterval n,
      F (fun i => (cascadeSeedPath n ψ z₁ g.1 α i,cascadeSeedPath n ψ z₂ g.2 β i))
      ∂(markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n)).prod
        (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))) =
      seedPairPathMean n ψ 0 z₁ z₂ F := by
  induction n generalizing ψ z₁ z₂ with
  | zero =>
    have he (g : MarkForest unitInterval 0 × MarkForest unitInterval 0) :
        (fun i => (cascadeSeedPath 0 ψ z₁ g.1 α i,cascadeSeedPath 0 ψ z₂ g.2 β i)) = Fin.elim0 :=
      funext fun i => i.elim0
    simp only [he,integral_const,probReal_univ,one_smul,seedPairPathMean]
  | succ n ih =>
    let Q : Measure (MarkForest unitInterval n) := markForestLaw unitInterval n (fun _ => cascadeSeedLaw)
    let H := fun p : (unitInterval × unitInterval) ×
        (MarkForest unitInterval n × MarkForest unitInterval n) =>
      F (Fin.cons (ψ 0 z₁ p.1.1,ψ 0 z₂ p.1.2) (fun i =>
        (cascadeSeedPath n (fun j => ψ (j+1)) (z₁+ψ 0 z₁ p.1.1) p.2.1 α.2 i,
         cascadeSeedPath n (fun j => ψ (j+1)) (z₂+ψ 0 z₂ p.1.2) p.2.2 β.2 i)))
    have hA : Measurable (fun p : (unitInterval × unitInterval) ×
        (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₁ p.1.1) :=
      (hψ 0).comp (measurable_const.prodMk measurable_fst.fst)
    have hD : Measurable (fun p : (unitInterval × unitInterval) ×
        (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₂ p.1.2) :=
      (hψ 0).comp (measurable_const.prodMk measurable_fst.snd)
    have hP := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) α.2).comp
      (((measurable_const (a := z₁)).add hA).prodMk measurable_snd.fst)
    have hR := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) β.2).comp
      (((measurable_const (a := z₂)).add hD).prodMk measurable_snd.snd)
    have hH : Measurable H := hF.comp (measurable_finCons (hA.prodMk hD)
      (Measurable.of_eval fun i => ((measurable_pi_apply i).comp hP).prodMk
        ((measurable_pi_apply i).comp hR)))
    have hiH : Integrable H ((volume.prod volume).prod (Q.prod Q)) :=
      Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using hB _)
    let R := fun g : MarkForest unitInterval (n+1) × MarkForest unitInterval (n+1) =>
      (((g.1 α.1.1 α.1.2).1,(g.2 β.1.1 β.1.2).1),
        ((g.1 α.1.1 α.1.2).2,(g.2 β.1.1 β.1.2).2))
    calc
      _ = ∫ g, H (R g)
          ∂(markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))).prod
            (markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))) := by
        apply integral_congr_ae
        apply ae_of_all
        intro g
        exact congrArg F (zip_finCons _ _ _ _)
      _ = ∫ p, H p ∂(volume.prod volume).prod (Q.prod Q) :=
        (markForestPairRoots_preserving n (fun _ => cascadeSeedLaw) α.1 β.1).hasLaw.integral_comp hH.aestronglyMeasurable
      _ = ∫ u, ∫ g, H (u,g) ∂Q.prod Q ∂volume.prod volume := integral_prod _ hiH
      _ = seedPairPathMean (n+1) ψ 0 z₁ z₂ F := by
        rw [seedPairPathMean]
        apply integral_congr_ae
        apply ae_of_all
        intro u
        exact ih (fun j => ψ (j+1)) (fun j => hψ (j+1))
          (z₁+ψ 0 z₁ u.1) (z₂+ψ 0 z₂ u.2) α.2 β.2
          (fun w => F (Fin.cons (ψ 0 z₁ u.1,ψ 0 z₂ u.2) w))
          (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedPairStep
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of one pair of root updates with both descendant paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

lemma measurable_seedPairStep (n : ℕ) (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z₁ z₂ : ι → ℝ)
    (α β : LabeledLeaf n) (F : (Fin (n+1) → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable F) : Measurable (seedPairStep n ψ z₁ z₂ α β F) := by
  have hA : Measurable (fun p : (unitInterval × unitInterval) ×
      (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₁ p.1.1) :=
    (hψ 0).comp (measurable_const.prodMk measurable_fst.fst)
  have hB : Measurable (fun p : (unitInterval × unitInterval) ×
      (MarkForest unitInterval n × MarkForest unitInterval n) => ψ 0 z₂ p.1.2) :=
    (hψ 0).comp (measurable_const.prodMk measurable_fst.snd)
  have hP := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) α).comp
    (((measurable_const (a := z₁)).add hA).prodMk measurable_snd.fst)
  have hR := (measurable_cascadeSeedPath n (fun j => ψ (j+1)) (fun j => hψ (j+1)) β).comp
    (((measurable_const (a := z₂)).add hB).prodMk measurable_snd.snd)
  exact hF.comp (measurable_finCons (hA.prodMk hB)
    (Measurable.of_eval fun i => ((measurable_pi_apply i).comp hP).prodMk
      ((measurable_pi_apply i).comp hR)))

lemma seedPairStep_root (n : ℕ) (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (z₁ z₂ : ι → ℝ) (α β : LabeledLeaf (n+1))
    (F : (Fin (n+1) → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (g h : MarkForest unitInterval (n+1)) :
    F (fun i => (cascadeSeedPath (n+1) ψ z₁ g α i,cascadeSeedPath (n+1) ψ z₂ h β i)) =
      seedPairStep n ψ z₁ z₂ α.2 β.2 F
        (((g α.1.1 α.1.2).1,(h β.1.1 β.1.2).1),((g α.1.1 α.1.2).2,(h β.1.1 β.1.2).2)) := by
  apply congrArg F
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedSharedPairEvaluation
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common labeled prefix determines the shared seed updates exactly. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_shared_pair_evaluation (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z₁ z₂ : ι → ℝ)
    (α β : LabeledLeaf n) (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    (∫ g : MarkForest unitInterval n,
      F (fun i => (cascadeSeedPath n ψ z₁ g α i,cascadeSeedPath n ψ z₂ g β i))
      ∂(markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))) =
      seedPairPathMean n ψ (labeledCommonDepth n α β) z₁ z₂ F := by
  induction n generalizing ψ z₁ z₂ with
  | zero =>
    have he (g : MarkForest unitInterval 0) :
        (fun i => (cascadeSeedPath 0 ψ z₁ g α i,cascadeSeedPath 0 ψ z₂ g β i)) = Fin.elim0 :=
      funext fun i => i.elim0
    simp only [he,integral_const,probReal_univ,one_smul,seedPairPathMean]
  | succ n ih =>
    rcases α with ⟨a,α⟩
    rcases β with ⟨b,β⟩
    let Q : Measure (MarkForest unitInterval n) := markForestLaw unitInterval n (fun _ => cascadeSeedLaw)
    by_cases hab : a = b
    · subst b
      rw [labeledCommonDepth,ite_eq_left rfl]
      let H := fun p : unitInterval × MarkForest unitInterval n =>
        seedPairStep n ψ z₁ z₂ α β F ((p.1,p.1),(p.2,p.2))
      have hH : Measurable H := (measurable_seedPairStep n ψ hψ z₁ z₂ α β F hF).comp (by fun_prop)
      have hiH : Integrable H (volume.prod Q) :=
        Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
          simpa only [Real.norm_eq_abs,H,seedPairStep] using hB _)
      calc
        _ = ∫ g : MarkForest unitInterval (n+1), H (g a.1 a.2)
            ∂(markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))) := by
          apply integral_congr_ae
          apply ae_of_all
          intro g
          exact seedPairStep_root n ψ z₁ z₂ (a,α) (a,β) F g g
        _ = ∫ p, H p ∂volume.prod Q :=
          (markForestRoot_preserving n (fun _ => cascadeSeedLaw) a).hasLaw.integral_comp hH.aestronglyMeasurable
        _ = ∫ u, ∫ g, H (u,g) ∂Q ∂volume := integral_prod _ hiH
        _ = seedPairPathMean (n+1) ψ (labeledCommonDepth n α β+1) z₁ z₂ F := by
          rw [seedPairPathMean]
          apply integral_congr_ae
          apply ae_of_all
          intro u
          exact ih (fun j => ψ (j+1)) (fun j => hψ (j+1))
            (z₁+ψ 0 z₁ u) (z₂+ψ 0 z₂ u) α β
            (fun w => F (Fin.cons (ψ 0 z₁ u,ψ 0 z₂ u) w))
            (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)
    · rw [labeledCommonDepth,ite_eq_right hab]
      let H := seedPairStep n ψ z₁ z₂ α β F
      have hH : Measurable H := measurable_seedPairStep n ψ hψ z₁ z₂ α β F hF
      have hiH : Integrable H ((volume.prod volume).prod (Q.prod Q)) :=
        Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ fun p => by
          simpa only [Real.norm_eq_abs,H,seedPairStep] using hB _)
      calc
        _ = ∫ g : MarkForest unitInterval (n+1),
            H (((g a.1 a.2).1,(g b.1 b.2).1),((g a.1 a.2).2,(g b.1 b.2).2))
            ∂(markForestLaw unitInterval (n+1) (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval (n+1))) := by
          apply integral_congr_ae
          apply ae_of_all
          intro g
          exact seedPairStep_root n ψ z₁ z₂ (a,α) (b,β) F g g
        _ = ∫ p, H p ∂(volume.prod volume).prod (Q.prod Q) :=
          (markForestDistinctRoots_preserving n (fun _ => cascadeSeedLaw) a b hab).hasLaw.integral_comp hH.aestronglyMeasurable
        _ = ∫ u, ∫ g, H (u,g) ∂Q.prod Q ∂volume.prod volume := integral_prod _ hiH
        _ = seedPairPathMean (n+1) ψ 0 z₁ z₂ F := by
          rw [seedPairPathMean]
          apply integral_congr_ae
          apply ae_of_all
          intro u
          exact seed_independent_pair_evaluation n (fun j => ψ (j+1)) (fun j => hψ (j+1))
            (z₁+ψ 0 z₁ u.1) (z₂+ψ 0 z₂ u.2) α β
            (fun w => F (Fin.cons (ψ 0 z₁ u.1,ψ 0 z₂ u.2) w))
            (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedPairIntegral
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the exact shared-prefix seed recursion over the unperturbed cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_pair_mean_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (z : ι → ℝ)
    (Φ : ℕ × (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) (hΦ : Measurable Φ)
    {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    (∫ p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n),
      Φ (noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i)))
      ∂((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
        probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable)) =
    ∫ α : ℕ → LabeledLeaf n, seedPairPathMean n ψ (labeledCommonDepth n (α 0) (α 1)) z z
      (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w)) ∂cascadeReplicaLaw n b := by
  have hS : Measurable (fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
      noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) :=
    (measurable_noiseReplicaPairData n).comp (Measurable.of_eval fun i =>
      (measurable_cascadeSeedLeaf n ψ hψ).comp
        (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hG : Measurable (fun q : (ℕ → LabeledLeaf n) × MarkForest unitInterval n =>
      Φ (seedForestPairData n ψ z q)) := hΦ.comp (measurable_seedForestPairData n ψ hψ z)
  have hiG : Integrable (fun q => Φ (seedForestPairData n ψ z q))
      ((cascadeReplicaLaw n b).prod
        (markForestLaw unitInterval n (fun _ => cascadeSeedLaw) : Measure (MarkForest unitInterval n))) :=
    Integrable.of_bound hG.aestronglyMeasurable C (ae_of_all _ fun q => by
      simpa only [Real.norm_eq_abs] using hB _)
  have h := congrArg (fun μ => ∫ p, Φ p ∂μ) (cascade_seed_pair_coordinates n b hb ψ hψ z)
  rw [integral_map hS.aemeasurable hΦ.aestronglyMeasurable,
    integral_map (measurable_seedForestPairData n ψ hψ z).aemeasurable hΦ.aestronglyMeasurable] at h
  rw [h,integral_prod _ hiG]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  exact seed_shared_pair_evaluation n ψ hψ z z (α 0) (α 1)
    (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w))
    (hΦ.comp (measurable_const.prodMk measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SeedSharedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-prefix seed updates become common conditional marks from the same ancestor state. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

theorem seed_shared_kernel (n : ℕ) (κ : ℕ → Kernel (ι → ℝ) (ι → ℝ))
    (hκ : ∀ i, IsMarkovKernel (κ i))
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    (hlaw : ∀ i z, volume.map (ψ i z) = κ i z) (d : ℕ) (z : ι → ℝ)
    (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) (hF : Measurable F)
    {C : ℝ} (hB : ∀ w, |F w| ≤ C) :
    seedPairPathMean n ψ d z z F = markPairPathMean n κ d z z F := by
  induction n generalizing κ ψ d z with
  | zero => rfl
  | succ n ih =>
    cases d with
    | zero => exact seed_independent_kernel (n+1) κ hκ ψ hψ hlaw z z F hF hB
    | succ d =>
      let H := fun a : ι → ℝ => seedPairPathMean n (fun j => ψ (j+1)) d
        (z+a) (z+a) (fun w => F (Fin.cons (a,a) w))
      have hH : Measurable H := measurable_seedPairPathMean n (fun j => ψ (j+1))
        (fun j => hψ (j+1)) d (fun a => z+a) (fun a => z+a)
        (measurable_const.add measurable_id) (measurable_const.add measurable_id)
        (fun a w => F (Fin.cons (a,a) w))
        (hF.comp (measurable_finCons (measurable_fst.prodMk measurable_fst) measurable_snd))
      have hP : MeasurePreserving (ψ 0 z) volume (κ 0 z) :=
        ⟨(hψ 0).comp (measurable_const.prodMk measurable_id),hlaw 0 z⟩
      calc
        _ = ∫ a, H a ∂κ 0 z := hP.hasLaw.integral_comp hH.aestronglyMeasurable
        _ = markPairPathMean (n+1) κ (d+1) z z F := by
          rw [markPairPathMean]
          apply integral_congr_ae
          apply ae_of_all
          intro a
          exact ih (fun j => κ (j+1)) (fun j => hκ (j+1))
            (fun j => ψ (j+1)) (fun j => hψ (j+1)) (fun j z => hlaw (j+1) z)
            d (z+a) (fun w => F (Fin.cons (a,a) w))
            (hF.comp (measurable_finCons measurable_const measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalCascade
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ancestor kernels for the two finite-dimensional Gaussian field terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

lemma vectorTerminalMultiplier_moment {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (i : ℕ) (z : Fin N → ℝ) :
    (∫⁻ a, ENNReal.ofReal (vectorTerminalMultiplier N n b v F i (z,a)^b i)
      ∂(vectorGaussianLaw N (v i) : Measure (Fin N → ℝ))) = 1 := by
  have hadm := backwardValue_linearGrowth_moments n b (fun j => vectorGaussianLaw N (v j))
    (fun j _ => vectorGaussianLaw_moments hN (v j)) hF hG (fun j hj => (hb.1 j hj).1)
  exact backwardValue_multiplier_moment_admissible n b (fun j => vectorGaussianLaw N (v j))
    (fun _ p => p.1+p.2) F (fun j hj => (hb.1 j hj).1) hadm i z

lemma vectorTerminalAncestorKernel_markov {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (i : ℕ) :
    IsMarkovKernel (vectorTerminalAncestorKernel N n b v F hF i) := by
  constructor
  intro z
  constructor
  change ((vectorGaussianLaw N (v i) : Measure (Fin N → ℝ)).withDensity _) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
  exact vectorTerminalMultiplier_moment hN n b v hb F hF hG i z

lemma vectorTerminalAncestorKernel_seed {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    ∃ ψ : ℕ → (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      ∀ i z, volume.map (ψ i z) = vectorTerminalAncestorKernel N n b v F hF i z := by
  have hex i : ∃ ψ : (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      Measurable (Function.uncurry ψ) ∧ ∀ z, volume.map (ψ z) = vectorTerminalAncestorKernel N n b v F hF i z := by
    let := vectorTerminalAncestorKernel_markov hN n b v hb F hF hG i
    exact (vectorTerminalAncestorKernel N n b v F hF i).exists_measurable_map_eq_unitInterval
  choose ψ hψ hLaw using hex
  exact ⟨ψ,hψ,hLaw⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalNoise
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Terminal Gibbs sampling and retained trees for finite vector fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal ENNReal
namespace InvariantIsing

lemma noiseLeafTerminal_vector_sum (N n : ℕ) (X : ℕ → (Fin N → ℝ) → ℝ)
    (u : ℕ → (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ))
    (F : (Fin N → ℝ) → ℝ) (hX : X n = F)
    (hu : ∀ i < n, u i = fun p => p.1+p.2) (z : Fin N → ℝ) (w : NoiseLeaf (Fin N → ℝ) n) :
    noiseLeafTerminal n X u z w = F (vectorLeafSum N n z w) := by
  induction n generalizing X u z with
  | zero => exact congrFun hX z
  | succ n ih =>
    rw [noiseLeafTerminal,hu 0 (by omega)]
    exact ih (fun i => X (i+1)) (fun i => u (i+1))
      (by simpa only [Nat.add_comm] using hX) (fun i hi => hu (i+1) (by omega)) (z+w.2.1) w.2.2

lemma vectorTerminalNoiseLaw_eq_backward (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) (T : NoiseTree (Fin N → ℝ) n) :
    vectorTerminalNoiseLaw N n F z T = noiseTerminalGibbsLaw n
      (vectorTerminalBackward N n b v F) (vectorTerminalUpdate N n) z T := by
  have hX : vectorTerminalBackward N n b v F n = F :=
    backwardValue_terminal n b (fun j => vectorGaussianLaw N (v j)) (fun _ p => p.1+p.2) F (le_refl n)
  have hu : ∀ i < n, vectorTerminalUpdate N n i = fun p => p.1+p.2 := by
    intro i hi
    funext p
    simp only [vectorTerminalUpdate,stoppedUpdate,hi,ite_true, if_true]
  unfold vectorTerminalNoiseLaw noiseTerminalGibbsLaw
  congr 2
  funext w
  rw [noiseLeafTerminal_vector_sum N n _ _ _ hX hu]

lemma vectorTerminalNoiseLaw_keep_ae {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    ∀ᵐ T ∂(noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)),
      (vectorTerminalNoiseLaw N n F z T).map
        (noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z) =
      noiseLeafKernel (Fin N → ℝ) n (noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
        (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z T) := by
  have hr := noiseGibbsRegular_ae n b hb (fun i => vectorGaussianLaw N (v i))
    (measurable_vectorTerminalMultiplier N n b v F hF) (measurable_vectorTerminalUpdate N n)
    (fun _ _ _ => Real.exp_pos _) (vectorTerminalMultiplier_moment hN n b v hb F hF hG) z
  filter_upwards [hr] with T hT
  rw [vectorTerminalNoiseLaw_eq_backward]
  exact noiseTerminalGibbsLaw_keep n b (fun i => vectorGaussianLaw N (v i))
    (measurable_vectorTerminalBackward N n b v F hF) (measurable_vectorTerminalUpdate N n) z T hT

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original labeled Gibbs laws for finite Gaussian vector terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma vectorLeafSum_labeled (N n : ℕ) (z : Fin N → ℝ) (p : VectorTerminalCoordinates N n)
    (α : LabeledLeaf n) :
    vectorLeafSum N n z (labeledNoiseLeaf (Fin N → ℝ) n (p.1,markForestOfCoords (Fin N → ℝ) n p.2) α) =
      labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    exact ih (z+p.2 (α.1.1,α.1.2,none))
      (p.1.2 α.1.1 α.1.2,fun a => p.2 (α.1.1,α.1.2,some a)) α.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorLabeledNoiseTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling the labeled vector terminal agrees with sampling its noise-tree representation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vector_labeled_noise_replica_law (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : CascadeExponents n b) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (z : Fin N → ℝ)
    (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
      Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1)) :
    (vectorTerminalCoordinateLaw N n b v ⊗ₘ
      probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z) (measurable_vectorLabeledTerminalLaw N n F hF z)).map
      (fun p i => labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i)) =
    probabilityReplicaKernel (vectorTerminalNoiseLaw N n F z) (measurable_vectorTerminalNoiseLaw N n F hF z) ∘ₘ
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure _) := by
  let T := fun p : VectorTerminalCoordinates N n => labeledNoiseJoin (Fin N → ℝ) n
    (p.1,markForestOfCoords (Fin N → ℝ) n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : (vectorTerminalCoordinateLaw N n b v).map T =
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure _) :=
    labeledNoiseCoordinates_law (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i))
  have hp : MeasurePreserving T (vectorTerminalCoordinateLaw N n b v)
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure _) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism (vectorTerminalCoordinateLaw N n b v) _
    (measurable_vectorLabeledTerminalLaw N n F hF z) (measurable_vectorTerminalNoiseLaw N n F hF z) hT hPQ
    (ψ := fun p α => labeledNoiseLeaf (Fin N → ℝ) n (p.1,markForestOfCoords (Fin N → ℝ) n p.2) α)
  · apply measurable_from_prod_countable_left
    intro α
    exact (measurable_labeledNoiseLeaf (Fin N → ℝ) n α).comp (by fun_prop)
  · have hg := hp.quasiMeasurePreserving.tendsto_ae.eventually
      (noiseCascade_good (Fin N → ℝ) n b hb (fun i => vectorGaussianLaw N (v i)))
    filter_upwards [hg,he] with p hg hi
    have ht : 0 < noiseTreeTotal (Fin N → ℝ) n (T p) ∧ noiseTreeTotal (Fin N → ℝ) n (T p) < ⊤ := by
      cases n with
      | zero => simp [noiseTreeTotal,rawTreeTotal]
      | succ n => exact hg.1
    have hbase := labeledLeafLaw_noiseMap (Fin N → ℝ) n p.1 (markForestOfCoords (Fin N → ℝ) n p.2) hg ht
    let f := labeledNoiseLeaf (Fin N → ℝ) n (p.1,markForestOfCoords (Fin N → ℝ) n p.2)
    let H := fun w => F (vectorLeafSum N n z w)
    have hH : Measurable H := hF.comp ((measurable_vectorLeafSum N n).comp (measurable_const.prodMk measurable_id))
    have hs : (fun α => H (f α)) = (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)) := by
      funext α
      exact congrArg F (vectorLeafSum_labeled N n z p α)
    have hi' : Integrable (fun α => Real.exp (H (f α))) (labeledLeafLaw n p.1) := by
      convert hi using 1
      all_goals try with_reducible_and_instances rfl
      funext α
      exact congrArg Real.exp (congrFun hs α)
    have h := gibbsProbability_map_normalize (labeledLeafLaw n p.1) (measurable_of_countable f) hH hi'
    rw [hs,hbase] at h
    exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorTerminalSeed
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint uniform-seed representation for terminal-tilted finite Gaussian vector fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vectorTerminal_seed_replica_law {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    ∃ ψ : ℕ → (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = vectorTerminalAncestorKernel N n b v F hF i z) ∧
      ∀ z,
        (((noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n))) ⊗ₘ
          probabilityReplicaKernel (vectorTerminalNoiseLaw N n F z) (measurable_vectorTerminalNoiseLaw N n F hF z)).map
          (fun p i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z (p.2 i)) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) := by
  obtain ⟨ψ,hψ,hlaw⟩ := vectorTerminalAncestorKernel_seed hN n b v hb F hF hG
  refine ⟨ψ,hψ,hlaw,fun z => ?_⟩
  have htree := cascadeSeedTree_retained_law n b (fun i => vectorGaussianLaw N (v i))
    (vectorTerminalMultiplier N n b v F) ψ (measurable_vectorTerminalMultiplier N n b v F hF) hψ
    (fun _ _ _ => Real.exp_pos _) (vectorTerminalMultiplier_moment hN n b v hb F hF hG) hlaw z
  have htree' : (noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)).map
      (cascadeSeedTree n b ψ z) =
      (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)).map
        (noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
          (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z) := by
    apply htree.trans
    apply congrArg (fun f : NoiseTree (Fin N → ℝ) n → NoiseTree (Fin N → ℝ) n => Measure.map f (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)))
    funext T
    apply noiseTreeKeep_update_congr
    intro i hi
    funext p
    simp only [vectorTerminalUpdate,stoppedUpdate,hi,ite_true, if_true]
  have hkeep := sampling_replica_morphism
    (P := (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)))
    (Q := (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n)).map
      (noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
        (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z))
    (T := noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
      (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z)
    (measurable_vectorTerminalNoiseLaw N n F hF z) (noiseLeafKernel (Fin N → ℝ) n).measurable
    ((measurable_noiseTreeKeep n b (fun i => vectorGaussianLaw N (v i))
      (measurable_vectorTerminalMultiplier N n b v F hF) (measurable_vectorTerminalUpdate N n)).comp
      ((measurable_const (a := z)).prodMk measurable_id)) rfl
    (ψ := fun _ w => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z w)
    (((measurable_noiseLeafKeep n (measurable_vectorTerminalMultiplier N n b v F hF)
      (measurable_vectorTerminalUpdate N n)).comp ((measurable_const (a := z)).prodMk measurable_id)).comp measurable_snd)
    (vectorTerminalNoiseLaw_keep_ae hN n b v hb F hF hG z)
  rw [hkeep,← htree',← cascadeSeed_replica_law n b hb ψ hψ z]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorLabeledSeedTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full labeled field replicas transported to the common uniform-seed construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vector_labeled_seed_replica_law {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    ∃ ψ : ℕ → (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = vectorTerminalAncestorKernel N n b v F hF i z) ∧
      ∀ z, (∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
        Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
          (labeledLeafLaw n p.1)) →
        (vectorTerminalCoordinateLaw N n b v ⊗ₘ
          probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z)
            (measurable_vectorLabeledTerminalLaw N n F hF z)).map
          (fun p i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z
            (labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i))) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p i => cascadeSeedLeaf n ψ z (p.2 i)) := by
  obtain ⟨ψ,hψ,hψlaw,hseed⟩ := vectorTerminal_seed_replica_law hN n b v hb F hF hG
  refine ⟨ψ,hψ,hψlaw,fun z he => ?_⟩
  have hkeep : Measurable (fun σ : ℕ → NoiseLeaf (Fin N → ℝ) n =>
      fun i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z (σ i)) := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_noiseLeafKeep n (measurable_vectorTerminalMultiplier N n b v F hF)
      (measurable_vectorTerminalUpdate N n)).comp
        ((measurable_const (a := z)).prodMk measurable_id)).comp (measurable_pi_apply i)
  have hleaf : Measurable (fun p : VectorTerminalCoordinates N n × LabeledLeaf n =>
      labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) p.2) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_labeledNoiseLeaf (Fin N → ℝ) n α).comp (by fun_prop)
  have hlabel : Measurable (fun p : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      fun i => labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i)) :=
    Measurable.of_eval fun i => hleaf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have h := congrArg (Measure.map (fun σ : ℕ → NoiseLeaf (Fin N → ℝ) n =>
      fun i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z (σ i)))
    (vector_labeled_noise_replica_law N n b v hb F hF z he)
  rw [Measure.map_map hkeep hlabel] at h
  exact h.trans ((map_compProd_snd
    (noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i)) : Measure (NoiseTree (Fin N → ℝ) n))
    (probabilityReplicaKernel (vectorTerminalNoiseLaw N n F z) (measurable_vectorTerminalNoiseLaw N n F hF z)) hkeep).symm.trans (hseed z))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorLabeledPairLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint ancestry and both complete paths for the original finite vector terminal. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

theorem vector_labeled_seed_pair_law {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    ∃ ψ : ℕ → (Fin N → ℝ) → unitInterval → (Fin N → ℝ),
      (∀ i, Measurable (Function.uncurry (ψ i))) ∧
      (∀ i z, volume.map (ψ i z) = vectorTerminalAncestorKernel N n b v F hF i z) ∧
      ∀ z, (∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
        Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
          (labeledLeafLaw n p.1)) →
        (vectorTerminalCoordinateLaw N n b v ⊗ₘ
          probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z)
            (measurable_vectorLabeledTerminalLaw N n F hF z)).map
          (fun p => coordinatePairData n (p.1.2,p.2)) =
        ((noiseCascadeLaw unitInterval n b (fun _ => cascadeSeedLaw) : Measure (NoiseTree unitInterval n)) ⊗ₘ
          probabilityReplicaKernel (noiseLeafKernel unitInterval n) (noiseLeafKernel unitInterval n).measurable).map
          (fun p => noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) := by
  obtain ⟨ψ,hψ,hψlaw,hfull⟩ := vector_labeled_seed_replica_law hN n b v hb F hF hG
  refine ⟨ψ,hψ,hψlaw,fun z he => ?_⟩
  have hm : Measurable (fun p : VectorTerminalCoordinates N n × LabeledLeaf n =>
      noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z
        (labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) p.2)) := by
    apply measurable_from_prod_countable_left
    intro α
    exact (measurable_noiseLeafKeep n (measurable_vectorTerminalMultiplier N n b v F hF)
      (measurable_vectorTerminalUpdate N n)).comp
      (measurable_const.prodMk ((measurable_labeledNoiseLeaf (Fin N → ℝ) n α).comp (by fun_prop)))
  have hK : Measurable (fun p : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      fun i => noiseLeafKeep n (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n) z
        (labeledNoiseLeaf (Fin N → ℝ) n (p.1.1,markForestOfCoords (Fin N → ℝ) n p.1.2) (p.2 i))) :=
    Measurable.of_eval fun i => hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hS : Measurable (fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
      fun i => cascadeSeedLeaf n ψ z (p.2 i)) :=
    Measurable.of_eval fun i => (measurable_cascadeSeedLeaf n ψ hψ).comp
      (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hdepth := coordinate_sampled_ancestry_ae n b hb (fun i => vectorGaussianLaw N (v i))
    (vectorTerminalMultiplier N n b v F) (vectorTerminalUpdate N n)
    (measurable_vectorTerminalMultiplier N n b v F hF) (measurable_vectorTerminalUpdate N n)
    (fun _ _ => (Real.exp_pos _).ne') z (vectorLabeledTerminalLaw N n F z)
    (measurable_vectorLabeledTerminalLaw N n F hF z)
    (fun p => gibbsProbability_absolutelyContinuous (labeledLeafLaw n p.1) _)
  have h := congrArg (Measure.map (noiseReplicaPairData (A := Fin N → ℝ) n)) (hfull z he)
  rw [Measure.map_map (measurable_noiseReplicaPairData n) hK,
    Measure.map_map (measurable_noiseReplicaPairData n) hS] at h
  refine (Measure.map_congr ?_).trans h
  filter_upwards [hdepth] with p hp
  exact (noiseReplicaPairData_keep_labeled n (vectorTerminalMultiplier N n b v F)
    (vectorTerminalUpdate N n) z p.1.1 p.1.2 p.2 hp).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_VectorPairIntegral
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved two-path formula for a finite Gaussian vector terminal. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma vectorTerminalPairMean_eq_integral (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (z : Fin N → ℝ)
    (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
      Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1))
    (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hΦ : Measurable Φ)
    {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    vectorTerminalPairMean N n b v F z Φ =
      ∫ q : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n), Φ (coordinatePairData n (q.1.2,q.2))
        ∂(vectorTerminalCoordinateLaw N n b v ⊗ₘ
          probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z) (measurable_vectorLabeledTerminalLaw N n F hF z)) := by
  have hm : Measurable (fun q : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      Φ (coordinatePairData n (q.1.2,q.2))) :=
    hΦ.comp ((measurable_coordinatePairData n).comp (measurable_fst.snd.prodMk measurable_snd))
  have hi : Integrable (fun q : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      Φ (coordinatePairData n (q.1.2,q.2)))
      (vectorTerminalCoordinateLaw N n b v ⊗ₘ
        probabilityReplicaKernel (vectorLabeledTerminalLaw N n F z) (measurable_vectorLabeledTerminalLaw N n F hF z)) :=
    Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun q => by
      simpa only [Real.norm_eq_abs] using hB _)
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [he] with p hp
  exact referenceReplicaMean_infinite (labeledLeafLaw n p.1)
    (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)) hp
    (fun σ : Fin 2 → LabeledLeaf n => Φ
      (labeledCommonDepth n (σ 0) (σ 1),fun i => (p.2 (edgeAt n (σ 0) i),p.2 (edgeAt n (σ 1) i))))
    (measurable_of_countable _)

theorem vectorTerminal_pair_formula_oai {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ)
    (he : ∀ᵐ p ∂vectorTerminalCoordinateLaw N n b v,
      Integrable (fun α => Real.exp (F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z)))
        (labeledLeafLaw n p.1))
    (Φ : ℕ × (Fin n → (Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hΦ : Measurable Φ)
    {C : ℝ} (hB : ∀ p, |Φ p| ≤ C) :
    vectorTerminalPairMean N n b v F z Φ =
      ∫ α : ℕ → LabeledLeaf n,
        markPairPathMean n (vectorTerminalAncestorKernel N n b v F hF)
          (labeledCommonDepth n (α 0) (α 1)) z z
          (fun w => Φ (labeledCommonDepth n (α 0) (α 1),w)) ∂cascadeReplicaLaw n b := by
  obtain ⟨ψ,hψ,hψlaw,hlaw⟩ := vector_labeled_seed_pair_law hN n b v hb F hF hG
  have hD : Measurable (fun p : VectorTerminalCoordinates N n × (ℕ → LabeledLeaf n) =>
      coordinatePairData n (p.1.2,p.2)) :=
    (measurable_coordinatePairData n).comp (measurable_fst.snd.prodMk measurable_snd)
  have hS : Measurable (fun p : NoiseTree unitInterval n × (ℕ → NoiseLeaf unitInterval n) =>
      noiseReplicaPairData n (fun i => cascadeSeedLeaf n ψ z (p.2 i))) :=
    (measurable_noiseReplicaPairData n).comp (Measurable.of_eval fun i =>
      (measurable_cascadeSeedLeaf n ψ hψ).comp
        (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hi := congrArg (fun μ => ∫ x, Φ x ∂μ) (hlaw z he)
  rw [integral_map hD.aemeasurable hΦ.aestronglyMeasurable,
    integral_map hS.aemeasurable hΦ.aestronglyMeasurable] at hi
  rw [vectorTerminalPairMean_eq_integral N n b v F hF z he Φ hΦ hB,hi,
    seed_pair_mean_integral n b hb ψ hψ z Φ hΦ hB]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  exact seed_shared_kernel n (vectorTerminalAncestorKernel N n b v F hF)
    (fun i => vectorTerminalAncestorKernel_markov hN n b v hb F hF hG i)
    ψ hψ hψlaw (labeledCommonDepth n (α 0) (α 1)) z _
    (hΦ.comp (measurable_const.prodMk measurable_id)) (fun w => hB _)

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.vectorTerminal_pair_formula_oai := @OAI.InvariantIsing.vectorTerminal_pair_formula_oai
