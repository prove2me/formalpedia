-- Prove2me | solution 1 for OAI.IsingPerceptron.enriched_poisson_unshifted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:32.988829+00:00
-- url     : https://prove2.me/submissions/d02b3aa6-5b58-41a4-a431-1e77bf14d24f

import Mathlib
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_IsingPerceptron_enriched_poisson_root_variance

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

lemma gaussian_weighted_sum_law {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasLaw (fun g : ι → ℝ => ∑ i, a i * g i)
      (gaussianReal 0 ((∑ i, a i ^ 2).toNNReal))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i => fun g : ι → ℝ => a i * g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  have hl i : HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw
  have hg := hi.hasGaussianLaw_fun_sum (fun i => (gaussianReal_const_mul (hl i) (a i)).hasGaussianLaw)
  refine ⟨(by fun_prop : Measurable (fun g : ι → ℝ => ∑ i, a i * g i)).aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  congr 1
  · have hI i : Integrable (fun g : ι → ℝ => a i * g i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul (a i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [integral_const_mul]
    have hz i : (∫ g : ι → ℝ, g i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
      simpa using (hl i).integral_eq
    simp [hz]
  · congr 1
    have hv i : Var[fun x : ℝ => a i*x; gaussianReal 0 1] = a i^2 := by
      simpa only [id_eq, variance_id_gaussianReal, NNReal.coe_one, mul_one] using
        (variance_const_mul (a i) id (gaussianReal 0 1))
    have hvsum := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun i x => a i * x) (fun i => (memLp_id_gaussianReal 2).const_mul (a i))
    rw [show (∑ i : ι, fun ω : ι → ℝ => a i * ω i) =
      (fun ω => ∑ i, a i * ω i) from by ext; simp] at hvsum
    simpa only [hv] using hvsum

end IsingPerceptron

end

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

lemma log_sq_le_powers {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    (Real.log x)^2 ≤ (2/r)^2 * (x^r + (x⁻¹)^r) := by
  have he : 0 < r/2 := by positivity
  have hpow (y : ℝ) (hy : 0 ≤ y) : (y^(r/2)/(r/2))^2 = (2/r)^2 * y^r := by
    rw [div_pow, ← Real.rpow_mul_natCast hy]
    norm_num
    field_simp
  by_cases hlog : 0 ≤ Real.log x
  · have h := (sq_le_sq₀ hlog (div_nonneg (Real.rpow_nonneg hx.le _) he.le)).mpr
      (Real.log_le_rpow_div hx.le he)
    rw [hpow x hx.le] at h
    nlinarith [Real.rpow_nonneg (inv_nonneg.mpr hx.le) r, sq_nonneg (2/r)]
  · have hlog' : 0 ≤ Real.log x⁻¹ := by rw [Real.log_inv]; linarith
    have h := (sq_le_sq₀ hlog' (div_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hx.le) _) he.le)).mpr
      (Real.log_le_rpow_div (inv_nonneg.mpr hx.le) he)
    rw [hpow x⁻¹ (inv_nonneg.mpr hx.le), Real.log_inv, neg_sq] at h
    nlinarith [Real.rpow_nonneg hx.le r, sq_nonneg (2/r)]

theorem integrable_log_sq_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (fun ω => X ω ^ r) P)
    (hj : Integrable (fun ω => (X ω)⁻¹ ^ r) P) :
    Integrable (fun ω => (Real.log (X ω))^2) P := by
  apply ((hi.add hj).const_mul ((2/r)^2)).mono' ((hX.log.pow_const 2).aestronglyMeasurable)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_sq_le_powers hω hr

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

theorem rawCascade_total_log_square (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    Integrable (fun T => (Real.log (rawTreeTotal n T).toReal)^2)
      (rawCascadeLaw n b : Measure (RawTree n)) := by
  cases n with
  | zero => simp [rawTreeTotal]
  | succ n =>
    have h := rawCascade_total_moments (n+1) b hb
    have hb0 := hb.1 0 (by omega)
    apply integrable_log_sq_of_moments _ (measurable_rawTreeTotal _).ennreal_toReal _
      (show 0 < b 0/2 by linarith) (h.2.1 _ (by linarith) _) (h.2.2 _ (by linarith))
    · filter_upwards [h.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    · intro i hi
      by_cases h0 : i = 0
      · subst i; linarith
      · have := hb.2 0 i (by omega) hi; linarith

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

namespace IsingPerceptron

lemma integrable_of_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hi : Integrable (fun x => (f x)^2) P) : Integrable f P := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' hf.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  change |f x| ≤ 1+(f x)^2
  have h := sq_nonneg (|f x|-1)
  nlinarith [sq_abs (f x)]

lemma integral_difference_same_law {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (hXL : P.map X = Q) (hYL : P.map Y = Q)
    {g : E → ℝ} (hg : Measurable g) (hg2 : Integrable (fun v => (g v)^2) Q) :
    Integrable (fun ω => g (X ω)-g (Y ω)) P ∧
    (∫ ω, g (X ω)-g (Y ω) ∂P) = 0 ∧
    Integrable (fun ω => (g (X ω)-g (Y ω))^2) P ∧
    (∫ ω, (g (X ω)-g (Y ω))^2 ∂P) ≤ 4 * ∫ v, (g v)^2 ∂Q := by
  have hX2 : Integrable (fun ω => (g (X ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hX.aemeasurable).mp
    rw [hXL]
    exact hg2
  have hY2 : Integrable (fun ω => (g (Y ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hY.aemeasurable).mp
    rw [hYL]
    exact hg2
  have hXi : Integrable (fun ω => g (X ω)) P := integrable_of_square P (hg.comp hX) hX2
  have hYi : Integrable (fun ω => g (Y ω)) P := integrable_of_square P (hg.comp hY) hY2
  have hdiff : Integrable (fun ω => (g (X ω)-g (Y ω))^2) P := by
    apply ((hX2.add hY2).const_mul 2).mono'
      (((hg.comp hX).sub (hg.comp hY)).pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (g (X ω)-g (Y ω))^2 ≤ 2*((g (X ω))^2+(g (Y ω))^2)
    nlinarith [sq_nonneg (g (X ω)+g (Y ω))]
  refine ⟨hXi.sub hYi, ?_, hdiff, ?_⟩
  · rw [integral_sub hXi hYi, ← integral_map hX.aemeasurable hg.aestronglyMeasurable,
      ← integral_map hY.aemeasurable hg.aestronglyMeasurable, hXL, hYL, sub_self]
  · calc
      _ ≤ ∫ ω, 2*((g (X ω))^2+(g (Y ω))^2) ∂P :=
        integral_mono hdiff ((hX2.add hY2).const_mul 2) (fun ω => by
          nlinarith [sq_nonneg (g (X ω)+g (Y ω))])
      _ = 4 * ∫ v, (g v)^2 ∂Q := by
        rw [integral_const_mul, integral_add hX2 hY2,
          ← integral_map hX.aemeasurable (hg.pow_const 2).aestronglyMeasurable,
          ← integral_map hY.aemeasurable (hg.pow_const 2).aestronglyMeasurable, hXL, hYL]
        ring

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_log_ratio (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let L := fun ν : NoiseTree A n =>
      Real.log (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
    Integrable L (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, L ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) = 0 ∧
    Integrable (fun ν => (L ν)^2) (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, (L ν)^2 ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact integral_difference_same_law (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    (rawCascadeLaw n b : Measure (RawTree n))
    (X := noiseTreeDisplace n b μ c u s) (Y := noiseTreeForget A n)
    ((measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id))
    (measurable_noiseTreeForget A n) (noiseTreeDisplace_law n b μ hc hu hcpos hm s)
    (noiseCascadeLaw_forget A n b μ)
    (Real.measurable_log.comp (measurable_rawTreeTotal n).ennreal_toReal)
    (rawCascade_total_log_square n b hb)

lemma measurable_noiseTreeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeFactor n b μ X u p.1 p.2) := by
  induction n generalizing b μ X u with
  | zero => exact (((hX 0).comp measurable_fst).exp).ennreal_ofReal
  | succ n ih =>
    unfold noiseTreeFactor
    apply measurable_sigmaPart_param _ measurable_snd
      (F := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        ENNReal.ofReal (max p.2.1 0) *
          noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)
    exact (by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
      (ℝ × (A × NoiseTree A n)) => ENNReal.ofReal (max p.2.1 0))).mul
        ((ih _ _ (fun i => hX (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop)))

theorem noiseTreeDisplace_total (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) =
      ENNReal.ofReal (Real.exp (-X 0 s)) * noiseTreeFactor n b μ X u s ν := by
  induction n generalizing b μ X u c s with
  | zero =>
    simp only [rawTreeTotal, noiseTreeFactor]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n := fun p =>
      (c 0 (s,p.2.1)*p.1,
        noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul measurable_fst).prodMk
        ((measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    change (∫⁻ p, ENNReal.ofReal (max p.1 0)*rawTreeTotal n p.2 ∂(sigmaPart I ν).map T) = _
    rw [lintegral_map]
    · change (∫⁻ p, ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) *
          rawTreeTotal n (T p).2 ∂sigmaPart I ν) = _
      have he (p : ℝ × (A × NoiseTree A n)) :
          ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) * rawTreeTotal n (T p).2 =
          ENNReal.ofReal (Real.exp (-X 0 s)) * (ENNReal.ofReal (max p.1 0) *
            noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
              (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by
        dsimp only [T]
        rw [ih _ _ (X := fun j => X (j+1)) (fun i => hc (i+1)) (fun i => hu (i+1)) (fun i => htel (i+1)),
          htel 0 s p.2.1]
        have hh (y x : ℝ) : max (Real.exp y*x) 0 = Real.exp y * max x 0 := by
          rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_zero]
        rw [hh, ENNReal.ofReal_mul (Real.exp_pos _).le]
        have hex (y z : ℝ) : ENNReal.ofReal (Real.exp (y-z)) * ENNReal.ofReal (Real.exp (-y)) =
            ENNReal.ofReal (Real.exp (-z)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
        calc
          _ = (ENNReal.ofReal (Real.exp (X 1 (u 0 (s,p.2.1))-X 0 s)) *
              ENNReal.ofReal (Real.exp (-X 1 (u 0 (s,p.2.1))))) *
              (ENNReal.ofReal (max p.1 0) *
                noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
                  (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by ring
          _ = _ := by rw [hex]
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_rawTreeTotal n).comp measurable_snd)
    · exact hT

lemma noiseTreeFactor_total_identity (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = ENNReal.ofReal (Real.exp (X 0 s)) *
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) := by
  rw [noiseTreeDisplace_total n b μ hc hu htel s ν, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

theorem noiseCascade_log_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i))
    (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < noiseTreeFactor n b μ X u s ν ∧ noiseTreeFactor n b μ X u s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = X 0 s ∧
    Integrable (fun ν => (L ν-X 0 s)^2) P ∧
    (∫ ν, (L ν-X 0 s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  dsimp only
  let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
  let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
  let D := fun ν : NoiseTree A n => Real.log
      (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
  have hcpos : ∀ i s a, 0 < c i (s,a) := by intro i s a; rw [htel]; exact Real.exp_pos _
  have hT : Measurable (noiseTreeDisplace n b μ c u s) :=
    (measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id)
  have hgood : ∀ᵐ ν ∂P, 0 < rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) ∧
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) hT.aemeasurable
    rw [show P.map (noiseTreeDisplace n b μ c u s) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseTreeDisplace_law n b μ hc hu hcpos hm s]
    exact (rawCascade_total_moments n b hb).1
  have hden : ∀ᵐ ν ∂P, 0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) (measurable_noiseTreeForget A n).aemeasurable
    rw [show P.map (noiseTreeForget A n) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseCascadeLaw_forget A n b μ]
    exact (rawCascade_total_moments n b hb).1
  have he : L =ᵐ[P] fun ν => X 0 s + D ν := by
    filter_upwards [hgood, hden] with ν hν hνd
    have htpos := ENNReal.toReal_pos hν.1.ne' hν.2.ne
    have hdpos := ENNReal.toReal_pos hνd.1.ne' hνd.2.ne
    dsimp only [L, D]
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_div (mul_pos (Real.exp_pos _) htpos).ne' hdpos.ne',
      Real.log_mul (Real.exp_ne_zero _) htpos.ne', Real.log_exp]
    ring
  have h := noiseTreeDisplace_log_ratio n b hb μ hc hu hcpos hm s
  change Integrable D P ∧ (∫ ν, D ν ∂P) = 0 ∧ Integrable (fun ν => (D ν)^2) P ∧ _ at h
  have hi : Integrable L P := ((integrable_const (X 0 s)).add h.1).congr he.symm
  have hec : (fun ν => L ν-X 0 s) =ᵐ[P] D := by
    filter_upwards [he] with ν hν
    rw [hν]
    ring
  have he2 : (fun ν => (L ν-X 0 s)^2) =ᵐ[P] fun ν => (D ν)^2 :=
    hec.fun_comp (fun x : ℝ => x^2)
  refine ⟨?_, hi, ?_, h.2.2.1.congr he2.symm, ?_⟩
  · filter_upwards [hgood] with ν hν
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν]
    exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hν.1.ne',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2⟩
  · rw [integral_congr_ae he, integral_add (integrable_const _) h.1, integral_const, h.2.1]
    simp [P]
  · rw [integral_congr_ae he2]
    exact h.2.2.2

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.intensityComponents_noAtoms _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

omit [MeasurableSpace S] in
lemma noiseTreeFactor_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (X : ℕ → S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = terminalTreeFactor n b μ u (X n) s ν := by
  induction n generalizing b μ X u s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeFactor terminalTreeFactor
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ _ _ _ _

omit [MeasurableSpace S] in
lemma terminalTreeFactor_update_congr (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) {u v : ℕ → S × A → S} (huv : ∀ i < n, u i = v i)
    (s : S) (ν : NoiseTree A n) :
    terminalTreeFactor n b μ u F s ν = terminalTreeFactor n b μ v F s ν := by
  induction n generalizing b μ u v s with
  | zero => rfl
  | succ n ih =>
    unfold terminalTreeFactor
    rw [huv 0 (by omega)]
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ (fun i hi => huv (i+1) (by omega)) _ _

omit [MeasurableSpace S] in
lemma backwardValue_treeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ (backwardValue n b μ u F) (stoppedUpdate n u) s ν =
      terminalTreeFactor n b μ u F s ν := by
  rw [noiseTreeFactor_terminal, backwardValue_terminal n b μ u F (le_refl n)]
  apply terminalTreeFactor_update_congr
  intro i hi
  funext p
  exact ite_eq_left hi

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

theorem admissible_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A)) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  let X := backwardValue n b μ u F
  let v := stoppedUpdate n u
  let c : ℕ → S × A → ℝ := fun i p => Real.exp (X (i+1) (v i p)-X i p.1)
  have hX : ∀ i, Measurable (X i) := measurable_backwardValue n b μ hu hF
  have hv : ∀ i, Measurable (v i) := measurable_stoppedUpdate n hu
  have hc : ∀ i, Measurable (c i) := fun i =>
    (((hX (i+1)).comp (hv i)).sub ((hX i).comp measurable_fst)).exp
  have hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A)) = 1 :=
    backwardValue_multiplier_moment_admissible n b μ u F (fun i hi => (hb.1 i hi).1) hadm
  have h := noiseCascade_log_integral n b hb μ hc hv (X := X) (fun _ _ _ => rfl) hm s
  have hX0 : X 0 s = cascadeRecursion n b μ u F s := by simp [X, backwardValue]
  simpa only [X, v, backwardValue_treeFactor, hX0] using h

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

namespace IsingPerceptron

variable {S : Type} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

theorem linearGrowth_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure S) (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F) (s : S) :
    let u : ℕ → S × S → S := fun _ p => p.1+p.2
    let P := (noiseCascadeLaw S n b μ : Measure (NoiseTree S n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal S n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact admissible_noiseCascade_recursion n b hb μ (fun _ => measurable_fst.add measurable_snd) hF
    (backwardValue_linearGrowth_moments n b μ hμ hF hG (fun i hi => (hb.1 i hi).1)) s

end IsingPerceptron

namespace IsingPerceptron

lemma logMean_const_add_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {b : ℝ} {F : A → ℝ}
    (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    Integrable (fun a => Real.exp (b*(c+F a))) μ := by
  simpa only [mul_add,Real.exp_add] using hF.const_mul (Real.exp (b*c))

lemma logMean_abs_sub_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) {C : ℝ}
    (h : ∀ a, |F a-G a| ≤ C) : |logMean b μ F-logMean b μ G| ≤ C := by
  apply abs_le.mpr
  have hu : logMean b μ F ≤ C+logMean b μ G := by
    rw [← logMean_const_add μ hb.ne' hG C]
    exact logMean_mono μ hb hF (logMean_const_add_integrable hG C)
      (fun a => by linarith [(abs_le.mp (h a)).2])
  have hl : logMean b μ G ≤ C+logMean b μ F := by
    rw [← logMean_const_add μ hb.ne' hF C]
    exact logMean_mono μ hb hG (logMean_const_add_integrable hF C)
      (fun a => by linarith [(abs_le.mp (h a)).1])
  constructor <;> linarith

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSingletonClass I] in
lemma finiteLogIntegral_eq_logMean (ν : Measure I) (H : I → ℝ) :
    finiteLogIntegral ν H = logMean 1 ν H := by simp [finiteLogIntegral,logMean]

lemma measurable_finiteLogIntegral (ν : Measure I) : Measurable (finiteLogIntegral ν) := by
  unfold finiteLogIntegral
  have hm : Measurable (fun p : (I → ℝ) × I => Real.exp (p.1 p.2)) :=
    measurable_from_prod_countable_left (fun i => (measurable_pi_apply i).exp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable.log

lemma finiteLogIntegral_lipschitz (ν : Measure I) [IsProbabilityMeasure ν] (H G : I → ℝ) :
    |finiteLogIntegral ν H-finiteLogIntegral ν G| ≤ ‖H-G‖ := by
  rw [finiteLogIntegral_eq_logMean,finiteLogIntegral_eq_logMean]
  apply logMean_abs_sub_le ν (by norm_num)
    (show Integrable (fun x => Real.exp (1*H x)) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1*G x)) ν from Integrable.of_finite)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (H-G) x

lemma finiteLogIntegral_linearGrowth (ν : Measure I) [IsProbabilityMeasure ν] :
    HasLinearGrowth (finiteLogIntegral ν) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun H => ?_⟩
  simpa only [finiteLogIntegral,Pi.zero_apply,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero,one_mul,zero_add] using finiteLogIntegral_lipschitz ν H 0

end IsingPerceptron

namespace IsingPerceptron

theorem variance_of_conditional_center {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : ℝ}
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ C+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply Integrable.of_bound (hd.pow 2).integral_prod_right' C
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    all_goals try with_reducible_and_instances rfl
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    ((integrable_const C).add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hX.integrable_sq,integral_const,
    probReal_univ,one_smul] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurable_cascadeEnergyLog (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) : Measurable (fun p : (I → ℝ) × NoiseTree (I → ℝ) n =>
      cascadeEnergyLog n b μ ν p.1 p.2) := by
  have hm := measurable_noiseTreeFactor n b μ
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd)
  simp only [noiseTreeFactor_terminal] at hm
  exact hm.ennreal_toReal.div
    (((measurable_noiseTreeTotal (I → ℝ) n).comp measurable_snd).ennreal_toReal) |>.log

theorem cascadeEnergyLog_conditional (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    let P := (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))
    Integrable (cascadeEnergyLog n b μ ν H) P ∧
      (∫ T, cascadeEnergyLog n b μ ν H T ∂P) = energyRecursion n b μ ν H ∧
      Integrable (fun T => (cascadeEnergyLog n b μ ν H T-energyRecursion n b μ ν H)^2) P ∧
      (∫ T, (cascadeEnergyLog n b μ ν H T-energyRecursion n b μ ν H)^2 ∂P) ≤
        4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact (linearGrowth_noiseCascade_recursion n b hb μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν) H).2

theorem cascadeEnergyLog_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
    MemLp (fun p : Ω × NoiseTree (I → ℝ) n => cascadeEnergyLog n b μ ν (H p.1) p.2) 2
      (P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) ∧
    Var[(fun p : Ω × NoiseTree (I → ℝ) n => cascadeEnergyLog n b μ ν (H p.1) p.2);
      P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))] ≤
        4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
          +Var[(fun ω => energyRecursion n b μ ν (H ω)); P] := by
  exact variance_of_conditional_center P _
    ((measurable_cascadeEnergyLog n b μ ν).comp ((hH.comp measurable_fst).prodMk measurable_snd)) hL
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.2.1)
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.1)
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.2.2)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MemLpOfAbsBound
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedForestCoordinates_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mem Lp Of Abs Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma enrichedIncrementLaw_moments (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    ExponentialNormMoments (enrichedIncrementLaw N n h u i : Measure (Spin N → ℝ)) := by
  apply finite_gaussian_exponentialNormMoments (measurable_enrichedIncrement N n h u i)
    (fun _ => 0) (fun x => (∑ j, (enrichedCoefficientsFin N n h u i x j)^2).toNNReal)
  intro x
  exact (gaussian_weighted_sum_law (enrichedCoefficientsFin N n h u i x)).map_eq

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_enrichedBaseEnergy {N M : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ} (hφ : Measurable φ) :
    Measurable (enrichedBaseEnergy (M := M) n h u φ) := by
  apply Measurable.of_eval
  intro x
  exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hφ).comp
    ((measurable_pi_apply r).comp measurable_snd))).add
    (((measurable_pi_apply x).comp (measurable_enrichedIncrement N n h u 0)).comp measurable_fst)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma measurable_enrichedPoissonBase {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedPoissonBase n h u φ) := by
  apply measurable_from_prod_countable_right
  intro M
  exact (measurable_enrichedBaseEnergy n h u hm).comp
    (measurable_fst.prodMk (Measurable.of_eval (fun index : Fin M =>
      (measurable_pi_apply (index : ℕ)).comp measurable_snd)))

lemma enriched_poisson_unshifted_oai {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    let X := fun p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n =>
      cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2
    MemLp X 2 Q ∧ Var[X;Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  have hr := enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1) hh h0 u hu ν P hm hK hφ r
  have hv := cascadeEnergyLog_variance _ n b hb
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (measurable_enrichedPoissonBase n h u hm) hr.1
  refine ⟨hv.1, ?_⟩
  have hrv : Var[(fun p => energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (enrichedPoissonBase n h u φ p)); _] ≤ N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := hr.2
  linarith [hv.2,hrv]

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.IsingPerceptron.enriched_poisson_unshifted_oai.{u_1} := @OAI.IsingPerceptron.enriched_poisson_unshifted_oai.{u_1}
