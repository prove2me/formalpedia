-- Prove2me | solution 1 for OAI.InvariantIsing.entropyFunctional_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:24.122931+00:00
-- url     : https://prove2.me/submissions/782077d0-34cf-4e52-9b04-432ce2bfbb0a

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

end InvariantIsing

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

lemma measurable_noiseLeafIntegral (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => ∫⁻ v,
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u p.1 v)) ∂noiseLeafKernel A n p.2) :=
  (((measurable_noiseLeafTerminal n hX hu).comp (by fun_prop : Measurable
    (fun p : (S × NoiseTree A n) × NoiseLeaf A n => (p.1.1,p.2)))).exp.ennreal_ofReal).lintegral_kernel_prod_right'
      (κ := (noiseLeafKernel A n).comap Prod.snd measurable_snd)

theorem noiseTreeFactor_leafIntegral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      noiseTreeFactor n b μ X u s ν = noiseTreeTotal A n ν *
        ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v)) ∂noiseLeafKernel A n ν := by
  induction n generalizing b μ X u s with
  | zero =>
    apply ae_of_all
    intro ν
    simp [noiseTreeFactor, noiseTreeTotal, rawTreeTotal, noiseLeafTerminal,
      noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j+1)
    let μt := fun j => μ (j+1)
    let Xt := fun j => X (j+1)
    let ut := fun j => u (j+1)
    let P := (noiseCascadeLaw A n bt μt : Measure (NoiseTree A n))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let E := fun p : ℝ × (A × NoiseTree A n) =>
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 = noiseTreeTotal A n p.2.2 *
      ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n Xt ut (u 0 (s,p.2.1)) v))
        ∂noiseLeafKernel A n p.2.2
    have hme : MeasurableSet {p | E p} := by
      apply measurableSet_eq_fun
      · exact (measurable_noiseTreeFactor n bt μt (fun i => hX (i+1))
          (fun i => hu (i+1))).comp (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))
      · exact ((measurable_noiseTreeTotal A n).comp (by fun_prop)).mul
          ((measurable_noiseLeafIntegral n (fun i => hX (i+1)) (fun i => hu (i+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    have he : ∀ᵐ p ∂I, E p := by
      apply (Measure.ae_prod_iff_ae_ae hme).mpr
      apply ae_of_all
      intro x
      apply (Measure.ae_prod_iff_ae_ae (hme.preimage (measurable_const.prodMk measurable_id))).mpr
      apply ae_of_all
      intro a
      exact ih bt hb.tail μt (fun i => hX (i+1)) (fun i => hu (i+1)) (u 0 (s,a))
    have ha := poissonLaw_ae_intensity I hme he
    have hg := noiseCascade_good A n.succ b hb μ
    have hσ := sigmaPart_eq_ae I
    filter_upwards [ha,hg,hσ] with ν hν hg hσ
    rw [noiseTreeFactor]
    change (∫⁻ p, ENNReal.ofReal (max p.1 0) *
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 ∂sigmaPart I ν) = _
    rw [hσ, noiseLeafKernel_lintegral n ν hg.1
      (F := fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal (n+1) X u s v)))
      (((measurable_noiseLeafTerminal (n+1) hX hu).comp
        (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal)]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hg.1.1.ne' hg.1.2.ne, one_mul]
    apply lintegral_congr_ae
    filter_upwards [hν] with p hp
    rw [hp]
    exact (mul_assoc _ _ _).symm

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

lemma gaussian_prefix_measurePreserving (n : ℕ) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i : Fin n => g i)
      gaussianCoordinates (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have he := hs.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

lemma cylinderField_eq_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) (g : ℕ → ℝ) :
    cylinderField a g = ∑ i : Fin n, a i*g i := by
  classical
  rw [cylinderField, a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*g i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

lemma cylinderField_law (a : ℕ →₀ ℝ) :
    gaussianCoordinates.map (cylinderField a) =
      gaussianReal 0 ((a.sum (fun _ c => c^2)).toNNReal) := by
  classical
  let n := a.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have he : cylinderField a = (fun g : Fin n → ℝ => ∑ i : Fin n, a i*g i) ∘
      (fun g : ℕ → ℝ => fun i : Fin n => g i) := by
    funext g
    exact cylinderField_eq_prefix a ha g
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    (gaussian_prefix_measurePreserving n).map_eq,(gaussian_weighted_sum_law (fun i : Fin n => a i)).map_eq]
  congr 2
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => a i^2) n

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 

lemma partition_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp ((p:ℝ)*H x)) ν) :
    (∫ x, Real.exp (H x) ∂ν)^p ≤ ∫ x, Real.exp ((p:ℝ)*H x) ∂ν := by
  simpa only [Function.comp_def, Real.exp_nat_mul] using
    (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (H x)).le)) h1
      (by simpa only [Function.comp_def, Real.exp_nat_mul] using hp)

lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he

 

lemma partition_inv_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (hH : Integrable H ν)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp (-(p:ℝ)*H x)) ν) :
    ((∫ x, Real.exp (H x) ∂ν)^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H x) ∂ν := by
  have hj := exp_integral_le_partition hH h1
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := (Real.exp_pos _).trans_le hj
  calc
    _ ≤ (Real.exp (∫ x, H x ∂ν)^p)⁻¹ :=
      (inv_le_inv₀ (pow_pos hz _) (pow_pos (Real.exp_pos _) _)).mpr
        (pow_le_pow_left₀ (Real.exp_pos _).le hj _)
    _ = Real.exp (∫ x, -(p:ℝ)*H x ∂ν) := by
      rw [integral_const_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    _ ≤ _ := exp_integral_le_partition (hH.const_mul _) hp

 

lemma gaussian_field_exp_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (t : ℝ) :
    Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) ∧
      (∫ ω, ∫ x, Real.exp (t*H (ω,x)) ∂ν ∂μ) ≤ Real.exp (t^2*K/2) := by
  have he : Measurable (fun z => Real.exp (t*H z)) := hm.const_mul t |>.exp
  have hsec : ∀ x, Integrable (fun ω => Real.exp (t*H (ω,x))) μ := by
    intro x
    have hx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
    apply (integrable_map_measure (g := fun y : ℝ => Real.exp (t*y)) (μ := μ) (by fun_prop) hx.aemeasurable).mp
    rw [hg x]
    exact integrable_exp_mul_gaussianReal t
  have hb (x : X) : (∫ ω, Real.exp (t*H (ω,x)) ∂μ) ≤ Real.exp (t^2*K/2) := by
    have h := mgf_gaussianReal (X := fun ω => H (ω, x))
      (hg x) t
    simp only [mgf, zero_mul, zero_add] at h
    rw [h]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hv x) (sq_nonneg t)]
  have hi : Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) := by
    apply (integrable_prod_iff' he.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
    apply Integrable.of_bound he.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      (Real.exp (t^2*K/2))
    refine Filter.Eventually.of_forall fun x => ?_
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (integral_nonneg (μ := μ) (f := fun ω : Ω => Real.exp (t*H (ω,x))) (fun ω => (Real.exp_pos _).le))] using hb x
  refine ⟨hi, ?_⟩
  rw [integral_integral_swap hi]
  calc
    _ ≤ ∫ _ : X, Real.exp (t^2*K/2) ∂ν :=
      integral_mono hi.integral_prod_right (integrable_const _) hb
    _ = _ := by simp

lemma abs_le_exp_add_exp_neg (x : ℝ) : |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [Real.add_one_le_exp x, Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]
    linarith [Real.add_one_le_exp (-x), Real.exp_pos x]

lemma gaussian_field_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) : Integrable H (μ.prod ν) := by
  have hp := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  have hn := (gaussian_field_exp_integrable (ν := ν) hm hg hv (-1:ℝ)).1
  apply (hp.add hn).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Pi.add_apply, Real.norm_eq_abs, one_mul, neg_one_mul] using abs_le_exp_add_exp_neg (H z)

 

lemma gaussian_partition_moments {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (p : ℕ) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧
      (∫ ω, Z ω^p ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) ∧
      (∫ ω, (Z ω^p)⁻¹ ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  change Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧ _
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have h1 := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  simp only [one_mul] at h1
  obtain ⟨hip, hbp⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (p:ℝ)
  obtain ⟨hin, hbn⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (-(p:ℝ))
  have hp : ∀ᵐ ω ∂μ, Z ω^p ≤ ∫ x, Real.exp ((p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [h1.prod_right_ae, hip.prod_right_ae] with ω hω hωp
    exact partition_pow_le p hω hωp
  have hn : ∀ᵐ ω ∂μ, (Z ω^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [hH.prod_right_ae, h1.prod_right_ae, hin.prod_right_ae] with ω hω hω1 hωn
    exact partition_inv_pow_le p hω hω1 hωn
  have hz (ω) : 0 ≤ Z ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hpint : Integrable (fun ω => Z ω^p) μ := by
    apply hip.integral_prod_left.mono' (hmZ.pow_const p).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hz _) _)] using hp
  have hnint : Integrable (fun ω => (Z ω^p)⁻¹) μ := by
    apply hin.integral_prod_left.mono' ((hmZ.pow_const p).inv).aestronglyMeasurable
    simpa only [Pi.inv_apply, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (hz _) _))] using hn
  refine ⟨hpint, hnint, (integral_mono_ae hpint hip.integral_prod_left hp).trans hbp, ?_⟩
  simpa only [neg_sq] using (integral_mono_ae hnint hin.integral_prod_left hn).trans hbn

lemma log_square_le_partition_moments {x : ℝ} (hx : 0 < x) :
    (Real.log x)^2 ≤ 2*(x^2+(x^2)⁻¹) := by
  have hp := Real.log_le_sub_one_of_pos hx
  have hn := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hn
  have hB : |Real.log x| ≤ x+x⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith [inv_pos.mpr hx]
  have hs := pow_le_pow_left₀ (abs_nonneg (Real.log x)) hB 2
  rw [sq_abs] at hs
  rw [← inv_pow]
  nlinarith [sq_nonneg (x-x⁻¹)]

 

lemma gaussian_log_partition_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => (Real.log (Z ω))^2) μ ∧
    (∫ ω, (Real.log (Z ω))^2 ∂μ) ≤ 4*Real.exp (2*K) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨hip,hin,hbp,hbn⟩ := gaussian_partition_moments (ν := ν) hm hg hv 2
  change Integrable (fun ω => Z ω^2) μ at hip
  change Integrable (fun ω => (Z ω^2)⁻¹) μ at hin
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have he := (gaussian_field_exp_integrable (ν := ν) hm hg hv 1).1
  simp only [one_mul] at he
  have hb : ∀ᵐ ω ∂μ, (Real.log (Z ω))^2 ≤ 2*(Z ω^2+(Z ω^2)⁻¹) := by
    filter_upwards [hH.prod_right_ae, he.prod_right_ae] with ω hω hωe
    apply log_square_le_partition_moments
    exact (Real.exp_pos _).trans_le (exp_integral_le_partition hω hωe)
  have hi : Integrable (fun ω => (Real.log (Z ω))^2) μ := by
    apply ((hip.add hin).const_mul 2).mono' (hmZ.log.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (Z ω)))] using hω
  refine ⟨hi, (integral_mono_ae hi ((hip.add hin).const_mul 2) hb).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add hip hin]
  have hx : (2:ℝ)^2*K/2 = 2*K := by ring
  simp only [Nat.cast_ofNat] at hbp hbn
  rw [hx] at hbp hbn
  linarith



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NormalizedRestrictionPi
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma joint_integrable_square_of_uniform_conditionals {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] {P : Measure Ω} {Q : Measure Γ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {F : Ω × Γ → ℝ}
    (hm : Measurable F) {C : ℝ}
    (hi : ∀ ω, Integrable (fun g => F (ω,g)^2) Q)
    (hb : ∀ ω, (∫ g, F (ω,g)^2 ∂Q) ≤ C) :
    Integrable (fun z => F z^2) (P.prod Q) := by
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  apply integrable_of_measurable_abs_le
    ((hm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact hb ω

lemma integrable_exp_of_integer_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (hm : Measurable Y)
    (he : ∀ n : ℤ, Integrable (fun x => Real.exp ((n:ℝ)*Y x)) ν) (t : ℝ) :
    Integrable (fun x => Real.exp (t*Y x)) ν := by
  obtain ⟨n,hn⟩ := exists_nat_gt |t|
  have hp := he (n:ℤ)
  have hm' := he (-(n:ℤ))
  apply (hp.add hm').mono' (hm.const_mul t |>.exp.aestronglyMeasurable)
  refine ae_of_all _ fun x => ?_
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Int.cast_natCast,Int.cast_neg]
  by_cases hy : 0 ≤ Y x
  · have h : t*Y x ≤ (n:ℝ)*Y x := mul_le_mul_of_nonneg_right ((le_abs_self t).trans hn.le) hy
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have h : t*Y x ≤ -(n:ℝ)*Y x := mul_le_mul_of_nonpos_right (by linarith [neg_abs_le t]) (le_of_not_ge hy)
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

lemma random_cylinder_all_exp_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) :
    ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ t : ℝ,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
  let κ : Kernel (Ω × (ℕ → ℝ)) X := ⟨fun z => ν z.1,hν.comp measurable_fst⟩
  have : IsMarkovKernel κ := ⟨fun z => by
    change IsProbabilityMeasure (ν z.1)
    infer_instance⟩
  have hi (t : ℝ) : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
    have hm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
        Real.exp (t*cylinderField (a p.2) p.1.2)) :=
      ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t |>.exp
    have hs : MeasurableSet {z : Ω × (ℕ → ℝ) |
        Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1)} :=
      ProbabilityTheory.measurableSet_kernel_integrable (κ := κ) hm.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    refine ae_of_all _ fun ω => ?_
    have hv (x : X) : (((a x).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ K := by
      rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact ha x
    exact (gaussian_field_exp_integrable (ν := ν ω) (measurable_cylinderFields a)
      (fun x => cylinderField_law (a x)) hv t).1.prod_right_ae
  have hn : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ n : ℤ,
      Integrable (fun x => Real.exp ((n:ℝ)*cylinderField (a x) z.2)) (ν z.1) :=
    ae_all_iff.mpr (fun n => hi (n:ℝ))
  filter_upwards [hn] with z hz
  exact integrable_exp_of_integer_exp (measurable_of_countable _) hz

lemma measurable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) (t : ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact (measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    (((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t)).log

lemma cylinder_scaled_law {X : Type*} (a : X → ℕ →₀ ℝ) (x : X) (t : ℝ) :
    gaussianCoordinates.map (fun g => t*cylinderField (a x) g) =
      gaussianReal 0 (⟨t^2,sq_nonneg t⟩*(((a x).sum (fun _ c => c^2)).toNNReal)) := by
  have hm := measurable_cylinderField (a x)
  rw [show (fun g => t*cylinderField (a x) g) = (fun y : ℝ => t*y) ∘ cylinderField (a x) from rfl,
    ← Measure.map_map (by fun_prop) hm,cylinderField_law,gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 2

lemma cylinder_cgf_second {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun g => (cgf (fun x => cylinderField (a x) g) ν t)^2) gaussianCoordinates ∧
      (∫ g, (cgf (fun x => cylinderField (a x) g) ν t)^2 ∂gaussianCoordinates) ≤
        4*Real.exp (2*(t^2*K)) := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (a z.2) z.1) :=
    (measurable_cylinderFields a).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((a x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((a x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (ha x) (sq_nonneg _)
  exact gaussian_log_partition_second (ν := ν) hm (fun x => cylinder_scaled_law a x t) hv

lemma integrable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t)
      (P.prod gaussianCoordinates) := by
  have hm := measurable_random_cylinder_cgf hν a t
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).1)
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
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

lemma cylinderField_smul (a : ℕ →₀ ℝ) (t : ℝ) (g : ℕ → ℝ) :
    cylinderField (t • a) g = t*cylinderField a g := by
  simp only [cylinderField]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma cylinderCross_self (a : ℕ →₀ ℝ) : cylinderCross a a = a.sum (fun _ c => c^2) := by
  simp only [cylinderCross,Finsupp.sum,pow_two]

end IsingPerceptron

namespace IsingPerceptron

lemma cylinderCross_zero_left (b : ℕ →₀ ℝ) : cylinderCross 0 b = 0 := by
  simp [cylinderCross]
lemma cylinderCross_add_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a+b) c = cylinderCross a c+cylinderCross b c := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
lemma cylinderCross_single_left (i : ℕ) (c : ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (Finsupp.single i c) b = c*b i := by
  exact Finsupp.sum_single_index (zero_mul _)
lemma cylinderCross_finset_left {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (∑ i ∈ s, a i) b = ∑ i ∈ s, cylinderCross (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderCross_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,cylinderCross_add_left,ih]

lemma featureCoefficients_apply {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) (j : ℕ) :
    featureCoefficients tag c j = ∑ i, if tag i = j then c i else 0 := by
  classical
  simp only [featureCoefficients,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma featureCoefficients_cross {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℕ) (u : J → ℕ) (a : I → ℝ) (b : J → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, ∑ j, if t i = u j then a i*b j else 0 := by
  classical
  rw [featureCoefficients,cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_single_left,featureCoefficients_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : t i = u j
  · simp [h]
  · simp only [Ne.symm h,h,ite_false, if_false,mul_zero]

lemma featureCoefficients_diagonal {I : Type*} [Fintype I]
    (t : I → ℕ) (u : I → ℕ)
    (hcross : ∀ i j, t i = u j → i = j) (a b : I → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, if t i = u i then a i*b i else 0 := by
  classical
  rw [featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact ite_eq_right (fun h => hji (hcross i j h).symm)
  · simp

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

lemma labeledCommonDepth_self (n : ℕ) (v : LabeledLeaf n) : labeledCommonDepth n v v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledCommonDepth,ite_true, if_true,ih]

lemma labeled_prefix_eq_iff (n : ℕ) (v w : LabeledLeaf n) {d : ℕ} (hd : d ≤ n) :
    (labeledAddress n v).take d = (labeledAddress n w).take d ↔ d ≤ labeledCommonDepth n v w := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    simp [labeledAddress,labeledCommonDepth]
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [labeledAddress,List.take_succ_cons,List.cons.injEq]
      rw [ih _ _ (by omega)]
      dsimp only [labeledCommonDepth]
      by_cases h : v.1 = w.1
      · simp only [h,ite_true, if_true,true_and,Nat.add_le_add_iff_right]
      · simp [h]

lemma treeFeatureTag_cross {J : Type*} [Encodable J] (n : ℕ) (v w : LabeledLeaf n)
    (i j : Fin (n+1) × J) :
    treeFeatureTag n v i = treeFeatureTag n w j ↔
      i = j ∧ i.1.1 ≤ labeledCommonDepth n v w := by
  unfold treeFeatureTag
  rw [Encodable.encode_inj]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hi,haddr,hj⟩
    have he : i = j := Prod.ext (Fin.ext hi) hj
    subst j
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mp haddr⟩
  · rintro ⟨rfl,hd⟩
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mpr hd,rfl⟩

lemma treeFieldCoefficients_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) (a b : Fin (n+1) → ℝ) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v a c) (treeFieldCoefficients n w b e) =
      (∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n v w then a i*b i else 0) *
        (∑ j, c j*e j) := by
  classical
  rw [treeFieldCoefficients,treeFieldCoefficients,featureCoefficients_diagonal
    (treeFeatureTag n v) (treeFeatureTag n w)
    (fun i j h => ((treeFeatureTag_cross n v w i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.1 ≤ labeledCommonDepth n v w
  · simp only [h,ite_true, if_true] <;> ring
  · simp only [h,ite_false, if_false,zero_mul]

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

lemma pathIncrement_sum (q : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range (r+1), pathIncrement q i = q r := by
  induction r with
  | zero => simp [pathIncrement]
  | succ r ih => rw [Finset.sum_range_succ,ih,pathIncrement]; ring

lemma pathIncrement_prefix (q : ℕ → ℝ) (n r : ℕ) (hr : r ≤ n) :
    (∑ i : Fin (n+1), if (i : ℕ) ≤ r then pathIncrement q i else 0) = q r := by
  classical
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i ≤ r then pathIncrement q i else 0)]
  have he : (∑ i ∈ Finset.range (n+1), if i ≤ r then pathIncrement q i else 0) =
      ∑ i ∈ Finset.range (r+1), pathIncrement q i := by
    symm
    calc
      _ = ∑ i ∈ Finset.range (r+1), if i ≤ r then pathIncrement q i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).symm
      _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr)) (by
        intro i _ hi
        exact ite_eq_right (by simp only [Finset.mem_range,not_lt] at hi; omega))
  rw [he,pathIncrement_sum]

lemma treeField_path_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v (fun i => pathAmplitude q i) c)
      (treeFieldCoefficients n w (fun i => pathAmplitude q i) e) =
      q (labeledCommonDepth n v w) * (∑ j, c j*e j) := by
  rw [treeFieldCoefficients_cross]
  simp_rw [← pow_two,pathAmplitude_sq hq h0]
  rw [pathIncrement_prefix q n _ (labeledCommonDepth_le n v w)]

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

lemma spinValue_sq (x : Fin 2) : spinValue x ^ 2 = 1 := by
  simp only [spinValue]; split_ifs <;> norm_num

lemma spinCoordinate_cross {N : ℕ} (x y : Spin N) :
    (∑ i, spinCoordinate x i * spinCoordinate y i) = spinOverlap x y := by
  simp only [spinCoordinate,div_mul_div_comm,← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N),← Finset.sum_div,spinOverlap]

lemma spinOverlap_self {N : ℕ} (hN : 0 < N) (x : Spin N) : spinOverlap x x = 1 := by
  simp only [spinOverlap,← pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hN.ne')

lemma monomialPath_monotone (n d : ℕ) : Monotone (monomialPath n d) := by
  intro i j hij
  apply pow_le_pow_left₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)

lemma monomialPath_nonneg (n d i : ℕ) : 0 ≤ monomialPath n d i :=
  pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma monomialPath_diag_le_one (n d : ℕ) : monomialPath n d n ≤ 1 := by
  apply pow_le_one₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact Nat.cast_le.mpr (Nat.le_succ n)

lemma monomialCoefficients_cross {N : ℕ} (n p d : ℕ)
    (s t : Spin N × LabeledLeaf n) :
    cylinderCross (monomialCoefficients n p d s) (monomialCoefficients n p d t) =
      spinOverlap s.1 t.1 ^ p * treeOverlap n s.2 t.2 ^ d := by
  unfold monomialCoefficients
  rw [treeField_path_cross n s.2 t.2 (monomialPath_monotone n d)
    (monomialPath_nonneg n d 0),tensorFeature_cross,spinCoordinate_cross]
  exact mul_comm _ _

lemma monomialCoefficients_variance {N : ℕ} (hN : 0 < N) (n p d : ℕ)
    (s : Spin N × LabeledLeaf n) :
    (monomialCoefficients n p d s).sum (fun _ c => c^2) = monomialPath n d n := by
  rw [← cylinderCross_self,monomialCoefficients_cross,spinOverlap_self hN,one_pow,one_mul]
  simp only [treeOverlap,labeledCommonDepth_self,monomialPath]

lemma monomialCoefficients_variance_le {N : ℕ} (hN : 0 < N) (n p d : ℕ)
    (s : Spin N × LabeledLeaf n) :
    (monomialCoefficients n p d s).sum (fun _ c => c^2) ≤ 1 := by
  rw [monomialCoefficients_variance hN]
  exact monomialPath_diag_le_one _ _

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

theorem cascadeRecursion_lipschitz {S : Type*} [SeminormedAddCommGroup S]
    [MeasurableSpace S] [MeasurableAdd₂ S]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {L : ℝ} (hLip : ∀ x y, |F x-F y| ≤ L*‖x-y‖)
    (hb : ∀ i < n, 0 < b i) :
    ∀ x y, |cascadeRecursion n b μ (fun _ p => p.1+p.2) F x-
      cascadeRecursion n b μ (fun _ p => p.1+p.2) F y| ≤ L*‖x-y‖ := by
  induction n generalizing b μ with
  | zero => exact hLip
  | succ n ih =>
    let G := cascadeRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) (fun _ p => p.1+p.2) F
    have hGm : Measurable G := measurable_cascadeRecursion n _ _
      (fun _ => measurable_fst.add measurable_snd) hF
    have hGG : HasLinearGrowth G := cascadeRecursion_linearGrowth n _ _
      (fun i hi => hμ (i+1) (by omega)) hF hG (fun i hi => hb (i+1) (by omega))
    have hGi (x : S) : Integrable (fun a => Real.exp (b 0*G (x+a))) (μ 0 : Measure S) :=
      integrable_exp_of_linearGrowth _ (hμ 0 (by omega))
        (hGm.comp (measurable_const.add measurable_id)) (hGG.add_left x) _
    intro x y
    apply logMean_abs_sub_le _ (hb 0 (by omega)) (hGi x) (hGi y)
    intro a
    simpa only [add_sub_add_right_eq_sub] using ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) (x+a) (y+a)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
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

lemma measurable_energyRecursion (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) :
    Measurable (energyRecursion n b μ ν) :=
  measurable_cascadeRecursion n b μ (fun _ => measurable_fst.add measurable_snd)
    (measurable_finiteLogIntegral ν)

lemma energyRecursion_lipschitz (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (H G : I → ℝ) :
    |energyRecursion n b μ ν H-energyRecursion n b μ ν G| ≤ ‖H-G‖ := by
  simpa only [one_mul,energyRecursion] using cascadeRecursion_lipschitz n b μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν)
    (L := 1) (fun H G => by simpa only [one_mul] using finiteLogIntegral_lipschitz ν H G) hb H G

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

namespace IsingPerceptron

lemma pair_left_injective (j : ℕ) : Function.Injective (Nat.pair j) := by
  intro a b h
  have := congrArg Nat.unpair h
  simpa only [Nat.unpair_pair,Prod.mk.injEq,true_and] using this

lemma tagCoefficients_other {j k : ℕ} (hjk : j ≠ k) (a : ℕ →₀ ℝ) (i : ℕ) :
    tagCoefficients j a (Nat.pair k i) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨v,hv⟩
  have := congrArg Nat.unpair hv
  simp only [Nat.unpair_pair,Prod.mk.injEq] at this
  exact hjk this.1

lemma cylinderCross_tag (j k : ℕ) (a b : ℕ →₀ ℝ) :
    cylinderCross (tagCoefficients j a) (tagCoefficients k b) =
      if j = k then cylinderCross a b else 0 := by
  classical
  unfold cylinderCross tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]
  by_cases h : j = k
  · subst k
    simp only [ite_true, if_true,Finsupp.mapDomain_apply (pair_left_injective j)]
  · simp only [h,ite_false, if_false]
    change a.sum (fun i c => c*tagCoefficients k b (Nat.pair j i)) = 0
    simp only [tagCoefficients_other (Ne.symm h),mul_zero]
    simp [Finsupp.sum]

lemma cylinderCross_smul (r t : ℝ) (a b : ℕ →₀ ℝ) :
    cylinderCross (r • a) (t • b) = r*t*cylinderCross a b := by
  unfold cylinderCross
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cylinderCross_sum_right {ι : Type*} (s : Finset ι) (a : ℕ →₀ ℝ) (b : ι → ℕ →₀ ℝ) :
    cylinderCross a (∑ i ∈ s, b i) = ∑ i ∈ s, cylinderCross a (b i) := by
  classical
  simp only [cylinderCross,Finsupp.finsetSum_apply,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma cylinderCross_tagged_sum {m : ℕ} (a b : Fin m → ℕ →₀ ℝ) :
    cylinderCross (∑ i : Fin m, tagCoefficients i (a i)) (∑ i : Fin m, tagCoefficients i (b i)) =
      ∑ i, cylinderCross (a i) (b i) := by
  classical
  rw [cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_sum_right]
  simp only [cylinderCross_tag,Fin.val_inj]
  simp

lemma externalFieldCoefficients_variance {N : ℕ} (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (s : Spin N × LabeledLeaf n) :
    (externalFieldCoefficients n h s).sum (fun _ c => c^2) = N*h n := by
  rw [← cylinderCross_self,externalFieldCoefficients,treeField_path_cross n _ _ hh h0,
    labeledCommonDepth_self]
  simp only [← pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

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
lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma enrichedCoefficients_variance_le {N : ℕ} (hN : 0 < N) (n : ℕ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (s : Spin N × LabeledLeaf n) :
    (enrichedCoefficients n h u s).sum (fun _ c => c^2) ≤
      N*h n+4*N*(perturbationScale N)^2 := by
  rw [← cylinderCross_self,enrichedCoefficients,cylinderCross_tagged_sum,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ]
  simp_rw [cylinderCross_smul]
  simp_rw [cylinderCross_self]
  rw [externalFieldCoefficients_variance n hh h0]
  apply add_le_add_right
  calc
    _ ≤ ∑ j : Fin N, (4*N*(perturbationScale N)^2)*perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hv := monomialCoefficients_variance_le hN n (monomialIndex j).1 (monomialIndex j).2 s
      have hw := perturbationWeight_nonneg j
      have hw1 := perturbationWeight_le_one j
      have hu2 : (u j)^2 ≤ 4 := by
        have hab := abs_le.mp (hu j)
        nlinarith
      have hs : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      have ho : (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) *
          (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) =
          N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by
        calc
          _ = (Real.sqrt N)^2*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by ring
          _ = _ := by rw [hs]
      rw [ho]
      calc
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 :=
          mul_le_of_le_one_right (by positivity) hv
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*4 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ (4*N*(perturbationScale N)^2)*perturbationWeight j := by
          have hww : (perturbationWeight j)^2 ≤ perturbationWeight j := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hww (show 0 ≤ 4*N*(perturbationScale N)^2 by positivity)]
    _ = (4*N*(perturbationScale N)^2)*(1-(1/2 : ℝ)^N) := by
      rw [← Finset.mul_sum,perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (by linarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N])

lemma spinValue_abs (x : Fin 2) : |spinValue x| = 1 := by
  simp only [spinValue]
  split_ifs <;> norm_num

lemma spinCoordinate_abs {N : ℕ} (x : Spin N) (i : Fin N) :
    |spinCoordinate x i| = 1/Real.sqrt N := by
  simp only [spinCoordinate,abs_div,spinValue_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma tensorFeature_spin_abs {N p : ℕ} (x : Spin N) (i : Fin p → Fin N) :
    |tensorFeature p (spinCoordinate x) i| = (1/Real.sqrt N)^p := by
  simp only [tensorFeature,Finset.abs_prod,spinCoordinate_abs,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

lemma enrichedLevelCoefficient_abs {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (i : ℕ) (x y : Spin N) (j : EnrichedBlock N) :
    |enrichedLevelCoefficient n h u i x j| = |enrichedLevelCoefficient n h u i y j| := by
  rcases j with j | ⟨j,t⟩
  · simp only [enrichedLevelCoefficient,abs_mul,spinValue_abs]
  · simp only [enrichedLevelCoefficient,abs_mul,tensorFeature_spin_abs]

lemma sum_scaled_cross {J : Type*} [Fintype J] (c : ℝ) (v w : J → ℝ) :
    (∑ j, (c*v j)*(c*w j)) = c^2*(∑ j, v j*w j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma enrichedLevelCoefficient_cross {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x y : Spin N) :
    (∑ j : EnrichedBlock N, enrichedLevelCoefficient n h u i x j * enrichedLevelCoefficient n h u i y j) =
      N*pathIncrement h i*spinOverlap x y +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i * (spinOverlap x y)^(monomialIndex j).1 := by
  classical
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedLevelCoefficient]
  rw [sum_scaled_cross,pathAmplitude_sq hh h0]
  have he : (∑ j : Fin N, spinValue (x j)*spinValue (y j)) = N*spinOverlap x y := by
    rw [spinOverlap,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
  rw [he]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [sum_scaled_cross,tensorFeature_cross,spinCoordinate_cross,mul_pow,
      pathAmplitude_sq (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]

lemma enrichedLevelCoefficient_variance {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x : Spin N) :
    (∑ j : EnrichedBlock N, (enrichedLevelCoefficient n h u i x j)^2) =
      N*pathIncrement h i +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i := by
  simpa only [← pow_two,spinOverlap_self hN,one_pow,mul_one] using
    enrichedLevelCoefficient_cross hN n hh h0 u i x x

lemma enrichedRoot_envelope_sq {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (x : Spin N) :
    (∑ j : EnrichedBlock N, |enrichedLevelCoefficient n h u 0 x j|^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
  simp only [sq_abs,enrichedLevelCoefficient_variance hN n hh h0 u 0 x,pathIncrement]
  apply add_le_add_right
  calc
    _ ≤ ∑ j : Fin N, (4*N*(perturbationScale N)^2)*perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hv : monomialPath n (monomialIndex j).2 0 ≤ 1 :=
        (monomialPath_monotone n (monomialIndex j).2 (Nat.zero_le n)).trans
          (monomialPath_diag_le_one n (monomialIndex j).2)
      have hw := perturbationWeight_nonneg j
      have hw1 := perturbationWeight_le_one j
      have hu2 : (u j)^2 ≤ 4 := by
        have hab := abs_le.mp (hu j)
        nlinarith
      have he : (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 =
          N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by
        simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
      rw [he]
      calc
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 :=
          mul_le_of_le_one_right (by positivity) hv
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*4 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ (4*N*(perturbationScale N)^2)*perturbationWeight j := by
          have hww : (perturbationWeight j)^2 ≤ perturbationWeight j := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hww (show 0 ≤ 4*N*(perturbationScale N)^2 by positivity)]
    _ = (4*N*(perturbationScale N)^2)*(1-(1/2 : ℝ)^N) := by
      rw [← Finset.mul_sum,perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N])

lemma variance_le_square_about_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) (a : ℝ) :
    Var[F; μ] ≤ ∫ x, (F x-a)^2 ∂μ := by
  have hs := variance_eq_sub (hF.sub (memLp_const a))
  simp only [Pi.sub_apply, Pi.pow_apply] at hs
  change Var[fun x => F x-a; μ] = _ at hs
  rw [variance_sub_const hF.aestronglyMeasurable a] at hs
  linarith [sq_nonneg (∫ x, F x-a ∂μ)]

lemma gaussian_coord_memLp {n : ℕ} {F : (Fin n → ℝ) → ℝ} {c : Fin n → ℝ}
    (hm : Measurable F)
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) (p : ℝ≥0) :
    MemLp F p (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hcoord (i : Fin n) : MemLp (fun x : Fin n → ℝ => c i*|x i|) p
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    have h := (memLp_id_gaussianReal p).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)
    simpa only [Function.comp_def, id_eq, Pi.abs_apply] using h.abs.const_mul (c i)
  have hb := (memLp_const |F 0|).add (memLp_finsetSum Finset.univ (fun i _ => hcoord i))
  apply hb.mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [Pi.zero_apply, sub_zero] at hx
  simp only [Pi.add_apply, Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma gaussian_variance_of_slope {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) : Var[F; gaussianReal 0 1] ≤ c^2 := by
  have hLp : MemLp F 2 (gaussianReal 0 1) := by
    apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal 2).abs.const_mul c)).mono'
      hm.aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    have hx := hl x 0
    simp only [sub_zero] at hx
    simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
    linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]
  have hsq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    simpa only [variance_id_gaussianReal, NNReal.coe_one, integral_id_gaussianReal,
      sq, mul_zero, sub_zero, Pi.pow_apply, id_eq] using h.symm
  calc
    _ ≤ ∫ x, (F x-F 0)^2 ∂gaussianReal 0 1 := variance_le_square_about_const hLp _
    _ ≤ ∫ x : ℝ, c^2*x^2 ∂gaussianReal 0 1 := by
      apply integral_mono (hLp.sub (memLp_const _)).integrable_sq
        ((memLp_id_gaussianReal 2).integrable_sq.const_mul _)
      intro x
      have hx := hl x 0
      simp only [sub_zero] at hx
      have hh := pow_le_pow_left₀ (abs_nonneg (F x-F 0)) hx 2
      simpa only [sq_abs, mul_pow, Pi.sub_apply, id_eq] using hh
    _ = c^2 := by rw [integral_const_mul, hsq, mul_one]

lemma gaussian_slope_memLp {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) (p : ℝ≥0) :
    MemLp F p (gaussianReal 0 1) := by
  apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal p).abs.const_mul c)).mono'
    hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [sub_zero] at hx
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma variance_prod_le_fiber {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hLp : MemLp F 2 (μ.prod ν))
    (hsecLp : ∀ b, MemLp (fun a => F (a,b)) 2 μ)
    (hGLp : MemLp (fun b => ∫ a, F (a,b) ∂μ) 2 ν) {C : ℝ}
    (hvar : ∀ b, Var[fun a => F (a,b); μ] ≤ C) :
    Var[F; μ.prod ν] ≤ C + Var[fun b => ∫ a, F (a,b) ∂μ; ν] := by
  have hsec : ∀ b, (∫ a, F (a,b)^2 ∂μ) ≤ C + (∫ a, F (a,b) ∂μ)^2 := by
    intro b
    have h := hvar b
    rw [variance_eq_sub (hsecLp b)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const C).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

theorem gaussian_variance_coordinate_bound (n : ℕ) {F : (Fin n → ℝ) → ℝ}
    (hm : Measurable F) {c : Fin n → ℝ}
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) :
    Var[F; Measure.pi (fun _ : Fin n => gaussianReal 0 1)] ≤ ∑ i, (c i)^2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using
          (measurable_fst : Measurable (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)))
    have hFm : Measurable (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hsm (x : Fin n → ℝ) : Measurable (fun a => F (Fin.cons a x)) :=
      hFm.comp (measurable_id.prodMk measurable_const)
    have hsl (x : Fin n → ℝ) : ∀ a b,
        |F (Fin.cons a x)-F (Fin.cons b x)| ≤ c 0*|a-b| := by
      intro a b
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        sub_self, abs_zero, mul_zero, Finset.sum_const_zero, add_zero] using
        hl (Fin.cons a x) (Fin.cons b x)
    have hsi (x : Fin n → ℝ) : Integrable (fun a => F (Fin.cons a x)) μ :=
      (gaussian_slope_memLp (hsm x) (hsl x) 1).integrable (by norm_num)
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGl : ∀ x y, |(∫ a, F (Fin.cons a x) ∂μ)-(∫ a, F (Fin.cons a y) ∂μ)| ≤
        ∑ i : Fin n, c i.succ*|x i-y i| := by
      intro x y
      rw [← integral_sub (hsi x) (hsi y)]
      have hB (a : ℝ) : |F (Fin.cons a x)-F (Fin.cons a y)| ≤
          ∑ i : Fin n, c i.succ*|x i-y i| := by
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          sub_self, abs_zero, mul_zero, zero_add] using hl (Fin.cons a x) (Fin.cons a y)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := μ)
          (f := fun a => F (Fin.cons a x)-F (Fin.cons a y))
          (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hB a)))
    have hGLp := gaussian_coord_memLp hGm hGl 2
    have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
    have hLp : MemLp (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) 2 (μ.prod ν) := by
      have h := (gaussian_coord_memLp hm hl 2).comp_measurePreserving hpres
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove,
        cast_eq, ENNReal.coe_ofNat, ν] using h
    have hprod := variance_prod_le_fiber hLp
      (fun x => gaussian_slope_memLp (hsm x) (hsl x) 2) hGLp
      (fun x => gaussian_variance_of_slope (hsm x) (hsl x))
    have heq : Var[fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2); μ.prod ν] =
        Var[F; Measure.pi (fun _ : Fin (n+1) => μ)] := by
      have h := hpres.variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    have ht := ih hGm hGl
    rw [Fin.sum_univ_succ]
    change _ ≤ c 0 ^ 2 + Var[(fun b => ∫ a, F (Fin.cons a b) ∂μ); ν] at hprod
    dsimp only [ν, μ] at hprod ht ⊢
    linarith

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
lemma memLp_of_abs_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasure μ] {F : A → ℝ} (hm : Measurable F) {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) (p : ℝ≥0∞) : MemLp F p μ :=
  MemLp.of_bound hm.aestronglyMeasurable K
    (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a))

lemma integral_abs_le_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) : |∫ a, F a ∂μ| ≤ K := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := K)
      (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a)))

lemma variance_le_of_oscillation {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ a, |F a| ≤ K) (hc : 0 ≤ c) (ho : ∀ a b, |F a - F b| ≤ c) :
    variance F μ ≤ c ^ 2 := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ)
  have hi := hLp.integrable (by norm_num)
  have hcenter : ∀ a, |F a - ∫ b, F b ∂μ| ≤ c := by
    intro a
    have h := integral_abs_le_bound (μ := μ) (F := fun b => F a - F b) (ho a)
    simpa only [integral_sub (integrable_const _) hi, integral_const,
      probReal_univ, one_smul] using h
  rw [variance_eq_integral hm.aemeasurable]
  have hisq := (hLp.sub (memLp_const (∫ a, F a ∂μ))).integrable_sq
  have h := integral_mono hisq (integrable_const (c ^ 2)) (fun a =>
    sq_le_sq.mpr (by simpa only [abs_of_nonneg hc, Pi.sub_apply] using hcenter a))
  simpa using h

lemma variance_prod_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hm : Measurable F) {K c : ℝ} (hb : ∀ z, |F z| ≤ K)
    (hc : 0 ≤ c) (ho : ∀ b a a', |F (a, b) - F (a', b)| ≤ c) :
    variance F (μ.prod ν) ≤ c ^ 2 + variance (fun b => ∫ a, F (a, b) ∂μ) ν := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ.prod ν)
  have hGm : Measurable (fun b => ∫ a, F (a, b) ∂μ) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb : ∀ b, |∫ a, F (a, b) ∂μ| ≤ K := fun b =>
    integral_abs_le_bound (fun a => hb (a, b))
  have hGLp := memLp_of_abs_bound hGm hGb 2 (μ := ν)
  have hsec : ∀ b, (∫ a, F (a, b) ^ 2 ∂μ) ≤ c ^ 2 + (∫ a, F (a, b) ∂μ) ^ 2 := by
    intro b
    have hm' : Measurable (fun a => F (a, b)) := hm.comp (measurable_id.prodMk measurable_const)
    have h := variance_le_of_oscillation (μ := μ) hm' (fun a => hb (a, b)) hc (ho b)
    rw [variance_eq_sub (memLp_of_abs_bound hm' (fun a => hb (a, b)) 2)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const (c ^ 2)).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

lemma variance_pi_boundedDifferences {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ)
    {F : (Fin n → A) → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ x, |F x| ≤ K) (hc : 0 ≤ c)
    (ho : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c) :
    variance F (Measure.pi (fun _ : Fin n => μ)) ≤ n * c ^ 2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : A × (Fin n → A) => (Fin.cons z.1 z.2 : Fin (n + 1) → A)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : A × (Fin n → A) → A))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : A × (Fin n → A) → (Fin n → A)))
    have hFm : Measurable (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hGb : ∀ x, |∫ a, F (Fin.cons a x) ∂μ| ≤ K := fun x =>
      integral_abs_le_bound (fun a => hb (Fin.cons a x))
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGosc : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) →
        |(∫ a, F (Fin.cons a x) ∂μ) - ∫ a, F (Fin.cons a y) ∂μ| ≤ c := by
      intro i x y hxy
      have hmsec : ∀ x : Fin n → A, Measurable (fun a => F (Fin.cons a x)) :=
        fun x => hFm.comp (measurable_id.prodMk measurable_const)
      have hisec : ∀ x : Fin n → A, Integrable (fun a => F (Fin.cons a x)) μ :=
        fun x => (memLp_of_abs_bound (hmsec x) (fun a => hb (Fin.cons a x)) 1).integrable le_rfl
      have h := integral_abs_le_bound (μ := μ) (F := fun a => F (Fin.cons a x) - F (Fin.cons a y))
        (fun a => ho i.succ (Fin.cons a x) (Fin.cons a y) (fun j => by
          refine Fin.cases ?_ (fun l => ?_) j
          · intro _; simp
          · intro hl
            simp only [Fin.cons_succ]
            exact hxy l (fun h => hl (congrArg Fin.succ h))))
      simpa only [integral_sub (hisec x) (hisec y)] using h
    have hsec : ∀ (x : Fin n → A) a a', |F (Fin.cons a x) - F (Fin.cons a' x)| ≤ c := by
      intro x a a'
      apply ho 0
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; simp
    have hprod := variance_prod_le (μ := μ) (ν := ν) hFm
      (fun z => hb (Fin.cons z.1 z.2)) hc hsec
    have htail := ih hGm hGb hGosc
    have heq : variance (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) (μ.prod ν) =
        variance F (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
      have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp only [ν] at hprod
    nlinarith

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma finite_linear_vector_bound {m : ℕ} {a : I → Fin m → ℝ} {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    ‖(fun x => ∑ j, a x j * g j) - (fun x => ∑ j, a x j * g' j)‖ ≤
      ∑ j, c j * |g j-g' j| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (abs_nonneg _)))).mpr
  intro x
  simp only [Pi.sub_apply,Real.norm_eq_abs,← Finset.sum_sub_distrib,← mul_sub]
  exact (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum (fun j _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (ha x j) (abs_nonneg _))

lemma measurable_rootEnergy (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) :
    Measurable (rootEnergy n b μ ν H a) := by
  apply (measurable_energyRecursion n b μ ν).comp
  fun_prop

lemma rootEnergy_gaussian_slope (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν H a g'| ≤ ∑ j, c j*|g j-g' j| := by
  refine (energyRecursion_lipschitz n b μ ν hμ hb _ _).trans ?_
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => H x+∑ j, a x j*g' j) =
      (fun x => ∑ j, a x j*g j) - (fun x => ∑ j, a x j*g' j) := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_left_eq_sub]
  rw [heq]
  exact finite_linear_vector_bound hc ha g g'

theorem rootEnergy_gaussian_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) :
    Var[rootEnergy n b μ ν H a; Measure.pi (fun _ : Fin m => gaussianReal 0 1)] ≤ ∑ j, (c j)^2 :=
  gaussian_variance_coordinate_bound m (measurable_rootEnergy n b μ ν H a)
    (rootEnergy_gaussian_slope n b μ ν hμ hb H a c hc ha)

lemma rootEnergy_base_lipschitz (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H G : I → ℝ) (a : I → Fin m → ℝ) (g : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν G a g| ≤ ‖H-G‖ := by
  have he := energyRecursion_lipschitz n b μ ν hμ hb
    (fun x => H x+∑ j, a x j*g j) (fun x => G x+∑ j, a x j*g j)
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => G x+∑ j, a x j*g j) = H-G := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_right_eq_sub]
  rw [heq] at he
  exact he

variable {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_bound {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (y : Fin M → A) : ‖patternBase φ y‖ ≤ M*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hK)).mpr
  intro x
  simp only [patternBase,Real.norm_eq_abs]
  calc
    _ ≤ ∑ r : Fin M, |φ (y r) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin M, K := Finset.sum_le_sum (fun r _ => hφ (y r) x)
    _ = _ := by simp

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_one_change {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (i : Fin M) (y y' : Fin M → A)
    (he : ∀ j, j ≠ i → y j=y' j) : ‖patternBase φ y-patternBase φ y'‖ ≤ 2*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hK)).mpr
  intro x
  have hsum : (∑ r : Fin M, (φ (y r) x-φ (y' r) x)) = φ (y i) x-φ (y' i) x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [he j hji,sub_self]
    · simp
  simp only [Pi.sub_apply,patternBase,Real.norm_eq_abs,← Finset.sum_sub_distrib,hsum]
  linarith [abs_sub (φ (y i) x) (φ (y' i) x),hφ (y i) x,hφ (y' i) x]

theorem pattern_root_energy_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    Var[(fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1);
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))]
      ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have hfl (y : Fin M → A) : MemLp (fun g => F (g,y)) 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν (patternBase φ y) a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb (patternBase φ y) a c hc ha) 2
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  let G : (Fin M → A) → ℝ := fun y => ∫ g, F (g,y) ∂γ
  have hGm : Measurable G := hFm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb (y : Fin M → A) : |G y| ≤ |∫ g, F₀ g ∂γ|+M*K := by
    have hh := integral_abs_le_bound (μ := γ) (fun g => hdiff g y)
    rw [integral_sub ((hfl y).integrable (by norm_num)) (h0l.integrable (by norm_num))] at hh
    dsimp only [G]
    linarith [abs_sub_abs_le_abs_sub (∫ g, F (g,y) ∂γ) (∫ g, F₀ g ∂γ)]
  have hGLp : MemLp G 2 ρ := memLp_of_abs_bound hGm hGb 2
  have hosc (i : Fin M) (y y' : Fin M → A) (he : ∀ j, j ≠ i → y j=y' j) :
      |G y-G y'| ≤ 2*K := by
    have hd (g : Fin m → ℝ) : |F (g,y)-F (g,y')| ≤ 2*K :=
      (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) (patternBase φ y') a g).trans
        (patternBase_one_change hK hφ i y y' he)
    have hh := integral_abs_le_bound (μ := γ) hd
    simpa only [integral_sub ((hfl y).integrable (by norm_num))
      ((hfl y').integrable (by norm_num)),G] using hh
  have hv := variance_prod_le_fiber hLp hfl hGLp
    (fun y => rootEnergy_gaussian_variance n b μ ν hμ hb (patternBase φ y) a c hc ha)
  have hbvar := variance_pi_boundedDifferences P M hGm hGb (by positivity : 0 ≤ 2*K) hosc
  change Var[F; γ.prod ρ] ≤ _
  change Var[G; ρ] ≤ _ at hbvar
  linarith

end IsingPerceptron

namespace IsingPerceptron

lemma enrichedIncrementLaw_moments (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    ExponentialNormMoments (enrichedIncrementLaw N n h u i : Measure (Spin N → ℝ)) := by
  apply finite_gaussian_exponentialNormMoments (measurable_enrichedIncrement N n h u i)
    (fun _ => 0) (fun x => (∑ j, (enrichedCoefficientsFin N n h u i x j)^2).toNNReal)
  intro x
  exact (gaussian_weighted_sum_law (enrichedCoefficientsFin N n h u i x)).map_eq

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A]

lemma pattern_root_energy_memLp (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1) 2
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  exact hLp

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

lemma memLp_variance_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} {C : ℝ}
    (h : MemLp X 2 P ∧ Var[X;P] ≤ C) (c : ℝ) :
    MemLp (fun ω => X ω-c) 2 P ∧ Var[(fun ω => X ω-c);P] ≤ C := by
  refine ⟨h.1.sub (memLp_const _), ?_⟩
  rw [variance_sub_const h.1.aestronglyMeasurable]
  exact h.2

lemma poissonMass_succ (r : ℝ≥0) (n : ℕ) :
    poissonMass r (n+1) * (n+1) = r * poissonMass r n := by
  unfold poissonMass
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma poisson_first_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * n) (r : ℝ) := by
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have he : (fun n : ℕ => poissonMass r (n+1) * (n+1)) =
      fun n => (r : ℝ) * poissonMass r n := funext (poissonMass_succ r)
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)) (r : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    rw [he]
    simpa only [mul_one,poissonMass] using hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * n) 1).mp hs'
  simpa [poissonMass] using h

lemma poisson_second_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * (n : ℝ)^2) ((r : ℝ)^2+r) := by
  have hs := ((poisson_first_hasSum r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have he (n : ℕ) : poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2 =
      (r : ℝ) * (poissonMass r n * n + poissonMass r n) := by
    push_cast
    calc
      _ = (poissonMass r (n+1) * (n+1)) * (n+1) := by ring
      _ = _ := by rw [poissonMass_succ]; ring
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2)
      ((r : ℝ) * (r+1)) := by
    simp_rw [he]
    exact hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * (n : ℝ)^2) 1).mp hs'
  simpa [poissonMass, pow_two, mul_add] using h

lemma poisson_cast_memLp (r : ℝ≥0) : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq (Measurable.of_discrete.aestronglyMeasurable)).mpr
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs, abs_sq, poissonMass] using
    (poisson_second_hasSum r).summable

lemma poisson_cast_mean (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  exact (poisson_first_hasSum r).tsum_eq

lemma poisson_cast_second (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2+r := by
  rw [integral_poissonMeasure]
  exact (poisson_second_hasSum r).tsum_eq

lemma poisson_cast_variance (r : ℝ≥0) : Var[(fun n : ℕ => (n : ℝ)); poissonMeasure r] = r := by
  rw [variance_eq_sub (poisson_cast_memLp r)]
  simp only [Pi.pow_apply, poisson_cast_second, poisson_cast_mean]
  ring

lemma integral_prod_sub_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ p : Ω × Ω, (X p.1-X p.2)^2 ∂P.prod P) = 2*Var[X;P] := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLp : MemLp (fun p : Ω × Ω => X p.1-X p.2) 2 (P.prod P) :=
    (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  rw [integral_prod _ hLp.integrable_sq]
  have he (x : Ω) : (∫ y, (X x-X y)^2 ∂P) =
      (X x)^2-2*X x*(∫ y, X y ∂P)+(∫ y, (X y)^2 ∂P) := by
    simp_rw [sub_sq]
    rw [integral_add (f := fun y => (X x)^2-2*X x*X y) (g := fun y => (X y)^2)
      ((integrable_const _).sub (hi.const_mul _)) hX.integrable_sq,
      integral_sub (f := fun _ => (X x)^2) (g := fun y => 2*X x*X y)
      (integrable_const _) (hi.const_mul _), integral_const,
      integral_const_mul, probReal_univ, one_smul]
  simp_rw [he]
  rw [integral_add (f := fun x => (X x)^2-2*X x*(∫ y, X y ∂P))
    (g := fun _ => ∫ y, (X y)^2 ∂P)
    (hX.integrable_sq.sub ((hi.const_mul 2).mul_const _)) (integrable_const _),
    integral_sub (f := fun x => (X x)^2) (g := fun x => 2*X x*(∫ y, X y ∂P))
      hX.integrable_sq ((hi.const_mul 2).mul_const _),integral_const,
    integral_mul_const,integral_const_mul,probReal_univ,one_smul,
    variance_eq_sub hX]
  simp only [Pi.pow_apply]
  ring

lemma variance_of_distance_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {K : ℝ} (_hK : 0 ≤ K) (h : ∀ x y, |X x-X y| ≤ K*|Y x-Y y|) :
    Var[X;P] ≤ K^2 * Var[Y;P] := by
  have hDX := (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have hDY := (hY.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hY.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have he := integral_mono hDX.integrable_sq (hDY.integrable_sq.const_mul (K^2))
    (show ∀ p : Ω × Ω, (X p.1-X p.2)^2 ≤ K^2*(Y p.1-Y p.2)^2 from fun p => by
      simpa only [mul_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h p.1 p.2) 2)
  simp only [Pi.sub_apply,Function.comp_apply] at he
  rw [integral_const_mul,integral_prod_sub_sq P hX,integral_prod_sub_sq P hY] at he
  linarith

lemma nat_abs_step_bound {F : ℕ → ℝ} {K : ℝ} (h : ∀ m, |F (m+1)-F m| ≤ K) :
    ∀ m n, |F m-F n| ≤ K*|(m : ℝ)-n| := by
  have hle (n d : ℕ) : |F (n+d)-F n| ≤ K*d := by
    induction d with
    | zero => simp
    | succ d ih =>
      calc
        _ ≤ |F (n+d+1)-F (n+d)|+|F (n+d)-F n| := by
          simpa only [Nat.add_assoc] using abs_sub_le (F (n+d+1)) (F (n+d)) (F n)
        _ ≤ K+K*d := add_le_add (h (n+d)) ih
        _ = K*(d+1 : ℕ) := by push_cast <;> ring
  intro m n
  rcases le_total n m with hnm | hmn
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hnm
    simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)] using hle n d
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [abs_sub_comm (F m) (F (m+d)),show (m : ℝ)-(m+d : ℕ) = -(d : ℝ) by push_cast; ring]
    simp only [abs_neg,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    exact hle m d

lemma nat_step_memLp {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP : MemLp (fun n : ℕ => (n : ℝ)) 2 P) {F : ℕ → ℝ} {K : ℝ}
    (h : ∀ m, |F (m+1)-F m| ≤ K) : MemLp F 2 P := by
  apply ((hP.const_mul K).add (memLp_const |F 0|)).mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro m
  have hh := nat_abs_step_bound h m 0
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)] at hh
  simp only [Pi.add_apply,Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F m) (F 0)]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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

theorem variance_of_conditional_center_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : A → ℝ} (hC : Integrable C μ)
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C a) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ (∫ a, C a ∂μ)+Var[X; μ] := by
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
    apply hC.mono' (hd.pow 2).integral_prod_right'
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C a
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
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C a+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    (hC.add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add hC hX.integrable_sq] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

theorem poisson_count_variance {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (r : ℝ≥0) {F : ℕ × Ω → ℝ} (hF : Measurable F)
    (hL : ∀ m, MemLp (fun ω => F (m,ω)) 2 Q) {C D K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ m, Var[(fun ω => F (m,ω)); Q] ≤ C+D*m)
    (hs : ∀ m, |(∫ ω, F (m+1,ω) ∂Q)-(∫ ω, F (m,ω) ∂Q)| ≤ K) :
    MemLp F 2 ((poissonMeasure r).prod Q) ∧
      Var[F; (poissonMeasure r).prod Q] ≤ C+D*r+K^2*r := by
  let X := fun m => ∫ ω, F (m,ω) ∂Q
  have hx : MemLp X 2 (poissonMeasure r) := nat_step_memLp (poisson_cast_memLp r) hs
  have hc : Integrable (fun m : ℕ => C+D*m) (poissonMeasure r) :=
    (integrable_const C).add (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D)
  have hh := variance_of_conditional_center_bound (poissonMeasure r) Q hF hx
    (fun m => ((hL m).sub (memLp_const (X m))).integrable_sq) (fun _ => rfl) hc
    (fun m => by
      rw [← variance_eq_integral (hL m).aemeasurable]
      exact hv m)
  refine ⟨hh.1, ?_⟩
  have hhx := variance_of_distance_bound (poissonMeasure r) hx (poisson_cast_memLp r) hK
    (nat_abs_step_bound hs)
  rw [poisson_cast_variance] at hhx
  have hmean : (∫ m : ℕ, C+D*m ∂poissonMeasure r) = C+D*r := by
    rw [integral_add (integrable_const C)
      (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D),
      integral_const,probReal_univ,one_smul,integral_const_mul,poisson_cast_mean]
  rw [hmean] at hh
  linarith [hh.2]

lemma infinite_prefix_preserving {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (fun y : ℕ → A => fun i : Fin M => y i)
      (Measure.infinitePi (fun _ : ℕ => P)) (Measure.pi (fun _ : Fin M => P)) := by
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (index : ℕ)), ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

lemma rootPrefix_preserving {m : ℕ} {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (rootPrefix (m := m) (A := A) M)
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P)))
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) :=
  (MeasurePreserving.id _).prod (infinite_prefix_preserving P M)

lemma patternBase_prefix_succ {I A : Type*} [Fintype I] (φ : A → I → ℝ)
    (y : ℕ → A) (M : ℕ) :
    patternBase φ (fun i : Fin (M+1) => y i) = patternBase φ (fun i : Fin M => y i)+φ (y M) := by
  ext x
  simp only [patternBase,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,Pi.add_apply]

lemma rootEnergy_prefix_step {I A : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (p : InfiniteRootData m A) (M : ℕ) :
    |rootEnergy n b μ ν (patternBase φ (fun i : Fin (M+1) => p.2 i)) a p.1-
      rootEnergy n b μ ν (patternBase φ (fun i : Fin M => p.2 i)) a p.1| ≤ K := by
  apply (rootEnergy_base_lipschitz n b μ ν hμ hb _ _ a p.1).trans
  rw [patternBase_prefix_succ,add_sub_cancel_left]
  exact (pi_norm_le_iff_of_nonneg hK).mpr (fun x => by simpa only [Real.norm_eq_abs] using hφ (p.2 M) x)

lemma integral_difference_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    {K : ℝ} (h : ∀ ω, |X ω-Y ω| ≤ K) : |(∫ ω, X ω ∂P)-(∫ ω, Y ω ∂P)| ≤ K := by
  rw [← integral_sub hX hY,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => X ω-Y ω) (C := K)
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using h ω))

lemma cascadeEnergyLog_total_mean {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
    (∫ p : Ω × NoiseTree (I → ℝ) n, cascadeEnergyLog n b μ ν (H p.1) p.2
      ∂P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) =
      ∫ ω, energyRecursion n b μ ν (H ω) ∂P := by
  have hi := (cascadeEnergyLog_variance P n b hb μ ν hμ hH hL).1.integrable (by norm_num)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.1)

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable [MeasurableSpace A]

lemma measurable_infinitePatternRoot (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} (hm : Measurable φ) :
    Measurable (infinitePatternRoot n b μ ν a φ) := by
  apply measurable_from_prod_countable_right
  intro M
  apply (measurable_energyRecursion n b μ ν).comp
  apply Measurable.of_eval
  intro x
  exact (Finset.measurable_sum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    ((measurable_pi_apply x).comp hm).comp
    ((measurable_pi_apply (i : ℕ)).comp measurable_snd))).add
    (by fun_prop : Measurable (fun p : InfiniteRootData m A => ∑ j, a x j*p.1 j))

lemma infinitePatternRoot_fixed_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (M : ℕ) :
    let Q := (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P))
    MemLp (fun p => infinitePatternRoot n b μ ν a φ (M,p)) 2 Q ∧
      Var[(fun p => infinitePatternRoot n b μ ν a φ (M,p));Q] ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  have hL := pattern_root_energy_memLp n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hv := pattern_root_energy_variance n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hp := rootPrefix_preserving (m := m) P M
  constructor
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      hL.comp_measurePreserving hp
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      (hp.variance_fun_comp hL.aemeasurable).le.trans hv

theorem infinitePatternRoot_poisson_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    MemLp (infinitePatternRoot n b μ ν a φ) 2 Q ∧
      Var[infinitePatternRoot n b μ ν a φ;Q] ≤ (∑ j, (c j)^2)+(2*K)^2*r+K^2*r := by
  have hh := infinitePatternRoot_fixed_variance n b μ ν hμ hb a c hc ha P hm hK hφ
  apply poisson_count_variance _ r (measurable_infinitePatternRoot n b μ ν a hm)
    (fun M => (hh M).1) hK
  · intro M
    simpa only [mul_comm (M : ℝ)] using (hh M).2
  · intro M
    apply integral_difference_bound _ ((hh (M+1)).1.integrable (by norm_num))
      ((hh M).1.integrable (by norm_num))
    exact fun p => rootEnergy_prefix_step n b μ ν hμ hb a hK hφ p M

end IsingPerceptron

namespace IsingPerceptron

lemma enriched_poisson_root_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : ∀ i < n, 0 < b i) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    let X := infinitePatternRoot n b μ ν (enrichedCoefficientsFin N n h u 0) φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  let x₀ : Spin N := fun _ => 0
  let c := fun j => |enrichedCoefficientsFin N n h u 0 x₀ j|
  have H := infinitePatternRoot_poisson_variance n b
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1)) hb
    (enrichedCoefficientsFin N n h u 0) c (fun _ => abs_nonneg _)
    (fun x j => (enrichedLevelCoefficient_abs n h u 0 x x₀ _).le) P hm hK hφ r
  have hc : (∑ j, (c j)^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
    have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
      (fun j => |enrichedLevelCoefficient n h u 0 x₀ j|^2)
    change (∑ j, |enrichedLevelCoefficient n h u 0 x₀ ((Fintype.equivFin _).symm j)|^2) ≤ _
    rw [he]
    exact enrichedRoot_envelope_sq hN n hh h0 u hu x₀
  refine ⟨H.1, ?_⟩
  linarith [H.2]

lemma measurable_enrichedPoissonBase {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedPoissonBase n h u φ) := by
  apply measurable_from_prod_countable_right
  intro M
  exact (measurable_enrichedBaseEnergy n h u hm).comp
    (measurable_fst.prodMk (Measurable.of_eval (fun index : Fin M =>
      (measurable_pi_apply (index : ℕ)).comp measurable_snd)))

lemma enriched_poisson_unshifted {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
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

theorem enriched_poisson_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
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
    MemLp (enrichedPoissonLog n b h u ν φ) 2 Q ∧ Var[enrichedPoissonLog n b h u ν φ;Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  exact memLp_variance_shift _
    (enriched_poisson_unshifted hN n b hb hh h0 u hu ν P hm hK hφ r) (N*h n/2)

lemma perturbationScale_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast hN
  · norm_num

lemma perturbationScale_nonneg (N : ℕ) : 0 ≤ perturbationScale N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma field_cap_arithmetic {N : ℕ} (hN : 0 < N) {C H h₀ e K r α : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (he1 : e ≤ 1) (hh : h₀ ≤ H)
    (hr : r ≤ α*N) :
    (C+N*h₀+4*N*e^2+5*K^2*r) / (N:ℝ)^2 ≤ (C+H+4+5*K^2*α)/N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hc : C ≤ N*C := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hh hn.le
  have he' : 4*N*e^2 ≤ 4*N := by
    have : e^2 ≤ 1 := by nlinarith
    nlinarith
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5*K^2 by positivity)
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  have hid : (C+H+4+5*K^2*α)/N*(N:ℝ)^2 = (C+H+4+5*K^2*α)*N := by
    field_simp
  rw [hid]
  nlinarith

theorem enriched_field_cap_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := fun p => enrichedPoissonLog n b h u ν φ p / N
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enriched_poisson_variance hN n b hb hh h0 u hu ν P hm hK hφ r
  refine ⟨by simpa only [div_eq_mul_inv] using hv.1.mul_const ((N:ℝ)⁻¹), ?_⟩
  simp only [div_eq_mul_inv, variance_mul_const]
  have hh' : h 0 ≤ H := (hh (Nat.zero_le n)).trans hH
  have hc : 0 ≤ 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
    positivity
  have ha := field_cap_arithmetic hN hc (perturbationScale_nonneg N)
    (perturbationScale_le_one hN) hh' hr (K := K)
  have ha' : (4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r)*(N:ℝ)⁻¹^2 ≤
      (4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +H+4+5*K^2*α)*(N:ℝ)⁻¹ := by
    simpa only [div_eq_mul_inv, inv_pow] using ha
  exact (mul_le_mul_of_nonneg_right hv.2 (sq_nonneg _)).trans ha'

end IsingPerceptron

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

lemma cascadeEnergyLog_eq_leaf_integral (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) (H : I → ℝ) :
    ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      cascadeEnergyLog n b μ ν H T =
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1 + p.2) H v) ∂noiseLeafKernel (I → ℝ) n T) := by
  have hfac := noiseTreeFactor_leafIntegral n b hb μ
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  have htot : ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  filter_upwards [hfac,htot] with T hfac ht
  simp only [noiseTreeFactor_terminal] at hfac
  unfold cascadeEnergyLog
  rw [hfac, ENNReal.toReal_mul]
  have ht0 : (noiseTreeTotal (I → ℝ) n T).toReal ≠ 0 :=
    (ENNReal.toReal_pos ht.1.ne' ht.2.ne).ne'
  rw [mul_div_cancel_left₀ _ ht0]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun v => (Real.exp_pos _).le))
    (((measurable_noiseLeafTerminal n (fun _ => measurable_finiteLogIntegral ν)
      (fun _ => measurable_fst.add measurable_snd)).comp
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

theorem labeledEnergyLog_eq_cascade (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν] (H : I → ℝ) :
    ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)),
      labeledEnergyLog n ν H p =
        cascadeEnergyLog n b μ ν H (labeledNoiseJoin (I → ℝ) n p) := by
  have hgood : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)), GoodNoiseTree (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) := by
    apply ae_of_ae_map (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    exact noiseCascade_good (I → ℝ) n b hb μ
  have htot : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      0 < noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) ∧
      noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) < ∞ := by
    apply ae_of_ae_map (p := fun T : NoiseTree (I → ℝ) n =>
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞)
      (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  have he : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      cascadeEnergyLog n b μ ν H (labeledNoiseJoin (I → ℝ) n p) =
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1+p.2) H v) ∂noiseLeafKernel (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p)) := by
    apply ae_of_ae_map (p := fun T : NoiseTree (I → ℝ) n =>
      cascadeEnergyLog n b μ ν H T = Real.log (∫ v, Real.exp (noiseLeafTerminal n
        (fun _ => finiteLogIntegral ν) (fun _ p => p.1+p.2) H v) ∂noiseLeafKernel (I → ℝ) n T))
      (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    exact cascadeEnergyLog_eq_leaf_integral n b hb μ ν H
  filter_upwards [hgood,htot,he] with p hg ht he
  rw [he,labeledEnergyLog_eq_leaf]
  congr 1
  have hm := labeled_terminal_integral n p.1 p.2 hg ht
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  simpa only [labeledEnergy_terminal] using hm

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_enrichedForest (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) :
    Measurable (enrichedForest N n h u) := by
  apply (measurable_markForestOfCoords (Spin N → ℝ) n).comp
  exact Measurable.of_eval (fun vertex =>
    (measurable_enrichedIncrement N n h u (forestVertexDepth n vertex+1)).comp (measurable_pi_apply vertex))

theorem enrichedForest_law (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) :
    (enrichedForestCoordinates N n).map (enrichedForest N n h u) =
      markForestLaw (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1)) := by
  change (enrichedForestCoordinates N n).map
    ((markForestOfCoords (Spin N → ℝ) n) ∘
      (fun g v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v))) = _
  have hm : Measurable (fun g : ForestVertex n → Fin (EnrichedRootSize N) → ℝ =>
      fun v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v)) := by
    exact Measurable.of_eval (fun vertex =>
      (measurable_enrichedIncrement N n h u (forestVertexDepth n vertex+1)).comp (measurable_pi_apply vertex))
  rw [← Measure.map_map (measurable_markForestOfCoords (Spin N → ℝ) n) hm]
  unfold enrichedForestCoordinates
  rw [Measure.infinitePi_map_pi _ (fun v => measurable_enrichedIncrement N n h u (forestVertexDepth n v+1))]
  exact markForestOfCoords_law (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1))

theorem labeledEnrichedCoordinates_law (N n : ℕ) (b h : ℕ → ℝ) (u : Fin N → ℝ) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (enrichedForestCoordinates N n)).map
      (fun p => labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2)) =
      noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1)) := by
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
    (show MeasurePreserving (enrichedForest N n h u) (enrichedForestCoordinates N n)
      (markForestLaw (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1))) from
        ⟨measurable_enrichedForest N n h u, enrichedForest_law N n h u⟩)
  change _ = _
  rw [show (fun p => labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2)) =
    (labeledNoiseJoin (Spin N → ℝ) n) ∘ Prod.map id (enrichedForest N n h u) from rfl,
    ← Measure.map_map (measurable_labeledNoiseJoin (Spin N → ℝ) n) hp.measurable,
    hp.map_eq, labeledNoiseJoin_law]

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurable_labeledEnergyLog (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν] :
    Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
      labeledEnergyLog n ν p.1 p.2) := by
  let κ : Kernel ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) (LabeledLeaf n) :=
    ⟨fun p => labeledLeafLaw n p.2.1,(measurable_labeledLeafLaw n).comp (by fun_prop)⟩
  have : IsMarkovKernel κ := ⟨fun _ => labeledLeafLaw_probability _ _⟩
  have hm : Measurable (fun p : ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) × LabeledLeaf n =>
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.1.2.2 p.2 p.1.1))) := by
    apply measurable_swap_iff.mp
    apply measurable_from_prod_countable_right
    intro γ
    exact ((measurable_finiteLogIntegral ν).comp
      ((measurable_labeledEnergy n γ).comp
        (show Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
          (p.2.2,p.1)) from by fun_prop))).exp
  simpa only [labeledEnergyLog_eq_leaf, κ, Kernel.coe_mk] using
    (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.log

theorem labeledEnergyLog_eq_cascade_random {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    {H : Ω → I → ℝ} (hmH : Measurable H) :
    ∀ᵐ p ∂P.prod ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      labeledEnergyLog n ν (H p.1) p.2 =
        cascadeEnergyLog n b μ ν (H p.1) (labeledNoiseJoin (I → ℝ) n p.2) := by
  have hbase : Measurable (fun p : Ω × (LabeledTree n × MarkForest (I → ℝ) n) =>
      (H p.1,p.2)) := (hmH.comp measurable_fst).prodMk measurable_snd
  have hjoin : Measurable (fun p : Ω × (LabeledTree n × MarkForest (I → ℝ) n) =>
      (H p.1,labeledNoiseJoin (I → ℝ) n p.2)) :=
    (hmH.comp measurable_fst).prodMk ((measurable_labeledNoiseJoin (I → ℝ) n).comp measurable_snd)
  have hl := (measurable_labeledEnergyLog n ν).comp hbase
  have hr := (measurable_cascadeEnergyLog n b μ ν).comp hjoin
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hl hr)).mpr
    (ae_of_all _ (fun ω => labeledEnergyLog_eq_cascade n b hb μ ν (H ω)))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
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
namespace IsingPerceptron

lemma enrichedToNoise_preserving {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) :
    MeasurePreserving (enrichedToNoise (A := A) n h u) (enrichedCoordinateLaw P r N n b)
      (((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (Measure.infinitePi (fun _ : ℕ => P)))).prod
          (noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1)))) := by
  have hf : Measurable (fun p : LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) =>
      (p.1,enrichedForest N n h u p.2)) :=
    measurable_fst.prodMk ((measurable_enrichedForest N n h u).comp measurable_snd)
  have hp : MeasurePreserving
      (fun p : LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) =>
        labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2))
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n))
      (noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1))) :=
    ⟨(measurable_labeledNoiseJoin (Spin N → ℝ) n).comp hf,
      labeledEnrichedCoordinates_law N n b h u⟩
  exact (MeasurePreserving.id _).prod hp

 

theorem enrichedCoordinatePressure_eq_noise {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (hb : CascadeExponents n b) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    enrichedCoordinatePressure n h u ν φ =ᵐ[enrichedCoordinateLaw P r N n b]
      (fun p => enrichedPoissonLog n b h u ν φ (enrichedToNoise n h u p) / N) := by
  let Q := (poissonMeasure r).prod
    ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
  let μ := fun i => enrichedIncrementLaw N n h u (i+1)
  have hpF : MeasurePreserving (enrichedForest N n h u) (enrichedForestCoordinates N n)
      (markForestLaw (Spin N → ℝ) n μ) :=
    ⟨measurable_enrichedForest N n h u,enrichedForest_law N n h u⟩
  have hpT := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod hpF
  have hp := (MeasurePreserving.id Q).prod hpT
  have he := labeledEnergyLog_eq_cascade_random Q n b hb μ ν (measurable_enrichedPoissonBase n h u hm)
  have he' : ∀ᵐ p ∂enrichedCoordinateLaw P r N n b,
      labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1)
        (p.2.1,enrichedForest N n h u p.2.2) =
      cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1)
        (labeledNoiseJoin (Spin N → ℝ) n (p.2.1,enrichedForest N n h u p.2.2)) := by
    apply ae_of_ae_map (p := fun p : EnrichedPoissonRoot N A ×
        (LabeledTree n × MarkForest (Spin N → ℝ) n) =>
      labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1) p.2 =
        cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1)
          (labeledNoiseJoin (Spin N → ℝ) n p.2)) hp.measurable.aemeasurable
    rw [show enrichedCoordinateLaw P r N n b = Q.prod
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n)) from rfl,
      hp.map_eq]
    exact he
  filter_upwards [he'] with p he
  unfold enrichedCoordinatePressure enrichedPoissonLog enrichedToNoise
  dsimp only
  rw [he]

 

theorem enrichedCoordinatePressure_field_cap {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let Q := enrichedCoordinateLaw P r N n b
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := enrichedCoordinatePressure n h u ν φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enriched_field_cap_variance hN n b hb hh h0 hH u hu ν P hm hK hφ r hr
  have hp := enrichedToNoise_preserving P r n b h u
  have he := enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm
  have hL := hv.1.comp_measurePreserving hp
  refine ⟨MemLp.ae_eq he.symm hL, ?_⟩
  have ht := variance_map (X := fun p => enrichedPoissonLog n b h u ν φ p / N)
    (hp.map_eq.symm ▸ hv.1.aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at ht
  simp only [Function.comp_def] at ht
  rw [variance_congr he, ← ht]
  exact hv.2

end IsingPerceptron

 

 

 

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


lemma enrichedNodeTag_injective (N n : ℕ) :
    Function.Injective (fun p : Option (ForestVertex n) × EnrichedBlock N => enrichedNodeTag p.1 p.2) := by
  rintro ⟨v,a⟩ ⟨w,b⟩ h
  cases a with
  | inl a => cases b with
    | inl b =>
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      have hv : v = w := nodeAddress_injective n (congrArg (fun p => p.2.1) he)
      have hab : a = b := congrArg (fun p => p.2.2) he
      subst w; subst b; rfl
    | inr b =>
      have h' := (Nat.pair_eq_pair.mp h).1
      omega
  | inr a => cases b with
    | inl b =>
      have h' := (Nat.pair_eq_pair.mp h).1
      omega
    | inr b =>
      rcases a with ⟨j,t⟩
      rcases b with ⟨k,s⟩
      have hj : j = k := Fin.ext (by have h' := (Nat.pair_eq_pair.mp h).1; exact Nat.add_right_cancel h')
      subst k
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      have hv : v = w := nodeAddress_injective n (congrArg (fun p => p.2.1) he)
      have hts : t = s := congrArg (fun p => p.2.2) he
      subst w; subst s; rfl



lemma measurable_enrichedGaussianNodes (N n : ℕ) :
    Measurable (enrichedGaussianNodes N n) := by
  unfold enrichedGaussianNodes
  fun_prop

theorem enrichedGaussianNodes_law (N n : ℕ) :
    gaussianCoordinates.map (enrichedGaussianNodes N n) =
      Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)) := by
  let t : Option (ForestVertex n) × Fin (EnrichedRootSize N) → ℕ :=
    fun p => enrichedNodeTag p.1 ((Fintype.equivFin (EnrichedBlock N)).symm p.2)
  have ht : Function.Injective t := by
    intro p q h
    have he := @enrichedNodeTag_injective N n
      (p.1,(Fintype.equivFin (EnrichedBlock N)).symm p.2)
      (q.1,(Fintype.equivFin (EnrichedBlock N)).symm q.2) h
    have he' := Prod.mk.inj he
    exact Prod.ext he'.1 ((Fintype.equivFin (EnrichedBlock N)).symm.injective he'.2)
  have hp := gaussian_pullback_measurePreserving t ht
  change gaussianCoordinates.map
    ((MeasurableEquiv.curry (Option (ForestVertex n)) (Fin (EnrichedRootSize N)) ℝ) ∘
      (fun g => fun p => g (t p))) = _
  rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable,hp.map_eq,
    Measure.infinitePi_map_curry (fun (_ : Option (ForestVertex n)) (_ : Fin (EnrichedRootSize N)) => gaussianReal 0 1)]
  simp only [Measure.infinitePi_eq_pi]

 
theorem enrichedGaussianRootForest_law (N n : ℕ) :
    gaussianCoordinates.map (fun g =>
      (enrichedGaussianNodes N n g none, fun v => enrichedGaussianNodes N n g (some v))) =
      (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (enrichedForestCoordinates N n) := by
  change gaussianCoordinates.map
    ((fun q : Option (ForestVertex n) → Fin (EnrichedRootSize N) → ℝ =>
      (q none,fun v => q (some v))) ∘ enrichedGaussianNodes N n) = _
  rw [← Measure.map_map (by fun_prop) (measurable_enrichedGaussianNodes N n),enrichedGaussianNodes_law]
  have he := infinitePi_option_split
    (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
    (fun _ : ForestVertex n => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
  have hc : (fun i : Option (ForestVertex n) => i.elim
      (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
      (fun _ => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))) =
      (fun _ => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)) := by
    funext i; cases i <;> rfl
  simpa only [hc,enrichedForestCoordinates] using he

lemma cylinderField_tag (j : ℕ) (a : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients j a) g = cylinderField a (fun i => g (Nat.pair j i)) := by
  unfold cylinderField tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]

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

lemma labeledEnergy_node_sum {I : Type} (n : ℕ) (g : Option (ForestVertex n) → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n (fun v => g (some v))) γ (H+g none) x =
      H x + ∑ i : Fin (n+1), g (nodeAt n γ i) x := by
  rw [labeledEnergy_edge_sum,Fin.sum_univ_succ]
  simp only [nodeAt_zero,nodeAt_succ,Pi.add_apply]
  ring

lemma enrichedIncrement_nodes (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ)
    (g : ℕ → ℝ) (v : Option (ForestVertex n)) (x : Spin N) :
    enrichedIncrement N n h u i (enrichedGaussianNodes N n g v) x =
      ∑ a : EnrichedBlock N, enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag v a) := by
  unfold enrichedIncrement enrichedCoefficientsFin enrichedGaussianNodes
  exact (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
    (fun a => enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag v a))

lemma cylinderField_external_nodes {N : ℕ} (n : ℕ) (h : ℕ → ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients 0 (externalFieldCoefficients n h (x,γ))) g =
      ∑ i : Fin (n+1), ∑ a : Fin N,
        pathAmplitude h i * spinValue (x a) * g (enrichedNodeTag (nodeAt n γ i) (.inl a)) := by
  rw [cylinderField_tag,externalFieldCoefficients,treeFieldCoefficients,cylinderField_feature,
    Fintype.sum_prod_type]
  simp only [enrichedNodeTag]
  simp_rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp only [treeFeatureTag]

lemma cylinderField_monomial_nodes {N : ℕ} (n : ℕ) (j : Fin N) (c : ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients (j+1) (c • monomialCoefficients n (monomialIndex j).1
      (monomialIndex j).2 (x,γ))) g =
      ∑ i : Fin (n+1), ∑ a : Fin (monomialIndex j).1 → Fin N,
        (c * pathAmplitude (monomialPath n (monomialIndex j).2) i *
          tensorFeature (monomialIndex j).1 (spinCoordinate x) a) *
            g (enrichedNodeTag (nodeAt n γ i) (.inr ⟨j,a⟩)) := by
  rw [cylinderField_tag,cylinderField_smul,monomialCoefficients,treeFieldCoefficients,
    cylinderField_feature,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [enrichedNodeTag]
  simp_rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp only [treeFeatureTag]
  ring

lemma cylinderField_enriched_nodes {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (enrichedCoefficients n h u (x,γ)) g =
      ∑ i : Fin (n+1), ∑ a : EnrichedBlock N,
        enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag (nodeAt n γ i) a) := by
  classical
  rw [enrichedCoefficients,cylinderField_finset_sum,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ,
    cylinderField_external_nodes,cylinderField_monomial_nodes]
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,enrichedLevelCoefficient,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

 

theorem enrichedEnergy_eq_cylinder {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (g : ℕ → ℝ) (H : Spin N → ℝ) (x : Spin N) (γ : LabeledLeaf n) :
    labeledEnergy n (enrichedForest N n h u
      (fun v => enrichedGaussianNodes N n g (some v))) γ
      (H+enrichedIncrement N n h u 0 (enrichedGaussianNodes N n g none)) x =
      H x + cylinderField (enrichedCoefficients n h u (x,γ)) g := by
  let F : Option (ForestVertex n) → Spin N → ℝ := fun v =>
    enrichedIncrement N n h u (nodeAddress n v).length (enrichedGaussianNodes N n g v)
  have he := labeledEnergy_node_sum n F γ H x
  have hf : (fun v => F (some v)) =
      (fun v => enrichedIncrement N n h u (forestVertexDepth n v+1)
        (enrichedGaussianNodes N n g (some v))) := by
    funext v
    simp only [F,nodeAddress_length_some]
  have h0 : F none = enrichedIncrement N n h u 0 (enrichedGaussianNodes N n g none) := by
    simp only [F,nodeAddress,List.length_nil]
  rw [hf,h0] at he
  rw [cylinderField_enriched_nodes]
  simpa only [F,nodeAddress_nodeAt_length,enrichedIncrement_nodes,enrichedForest] using he

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

private lemma preserving_three_rotate {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun p : (A × B) × C => (p.1.1,(p.2,p.1.2)))
      ((μ.prod ν).prod ρ) (μ.prod (ρ.prod ν)) :=
  ((MeasurePreserving.id μ).prod Measure.measurePreserving_swap).comp
    (measurePreserving_prodAssoc μ ν ρ)

private lemma preserving_four_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (ρ.prod τ)) ((μ.prod ρ).prod (ν.prod τ)) := by
  have h1 := (measurePreserving_prodAssoc (μ.prod ν) ρ τ).symm MeasurableEquiv.prodAssoc
  have h2 := ((measurePreserving_prodAssoc μ ρ ν).symm MeasurableEquiv.prodAssoc).comp
    (preserving_three_rotate μ ν ρ)
  exact (measurePreserving_prodAssoc (μ.prod ρ) ν τ).comp
    ((h2.prod (MeasurePreserving.id τ)).comp h1)

theorem enrichedCylinderToCoordinates_preserving {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (N n : ℕ) (b : ℕ → ℝ) :
    MeasurePreserving (enrichedCylinderToCoordinates (A := A) N n)
      (enrichedCylinderLaw P r n b) (enrichedCoordinateLaw P r N n b) := by
  let μ := poissonMeasure r
  let ν := Measure.infinitePi (fun _ : ℕ => P)
  let ρ := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let γ := Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)
  let τ := enrichedForestCoordinates N n
  have hn : MeasurePreserving (fun g =>
      (enrichedGaussianNodes N n g none,fun v => enrichedGaussianNodes N n g (some v)))
      gaussianCoordinates (γ.prod τ) :=
    ⟨(by unfold enrichedGaussianNodes; fun_prop),enrichedGaussianRootForest_law N n⟩
  have h1 := (MeasurePreserving.id ((μ.prod ν).prod ρ)).prod hn
  have h2 := preserving_four_shuffle (μ.prod ν) ρ γ τ
  have h3 := (preserving_three_rotate μ ν γ).prod (MeasurePreserving.id (ρ.prod τ))
  exact h3.comp (h2.comp h1)



theorem enrichedCylinderPressure_eq_coordinates {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N))
    (φ : A → Spin N → ℝ) (p : EnrichedCylinderData n A) :
    enrichedCylinderPressure n h u ν φ p =
      enrichedCoordinatePressure n h u ν φ (enrichedCylinderToCoordinates N n p) := by
  unfold enrichedCylinderPressure enrichedCoordinatePressure enrichedCylinderToCoordinates
    labeledEnergyLog enrichedPoissonBase enrichedBaseEnergy rootPrefix
  dsimp only
  congr 3
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  exact (enrichedEnergy_eq_cylinder n h u p.2
    (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i)) s.1 s.2).symm

 

theorem enrichedCylinderPressure_field_cap {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let Q := enrichedCylinderLaw P r n b
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := enrichedCylinderPressure n h u ν φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enrichedCoordinatePressure_field_cap hN n b hb hh h0 hH u hu ν P hm hK hφ r hr
  have hp := enrichedCylinderToCoordinates_preserving P r N n b
  have he : enrichedCylinderPressure n h u ν φ =
      (enrichedCoordinatePressure n h u ν φ) ∘ enrichedCylinderToCoordinates N n := by
    funext p
    exact enrichedCylinderPressure_eq_coordinates n h u ν φ p
  have hL := hv.1.comp_measurePreserving hp
  refine ⟨he ▸ hL, ?_⟩
  have ht := variance_map (X := enrichedCoordinatePressure n h u ν φ)
    (hp.map_eq.symm ▸ hv.1.aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at ht
  rw [he, ← ht]
  exact hv.2

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NamespaceSplit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Namespace Split. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_gaussianNamespaceSplit (j : ℕ) : Measurable (gaussianNamespaceSplit j) := by
  unfold gaussianNamespaceSplit
  fun_prop

lemma gaussianNamespaceSplit_law (j : ℕ) :
    gaussianCoordinates.map (gaussianNamespaceSplit j) =
      gaussianCoordinates.prod (otherNamespacesLaw j) := by
  let e := Equiv.optionSubtypeNe j
  let t : Option {k : ℕ // k ≠ j} × ℕ → ℕ := fun p => Nat.pair (e p.1) p.2
  have ht : Function.Injective t := by
    intro p q h
    have he := Nat.pair_eq_pair.mp h
    exact Prod.ext (e.injective he.1) he.2
  have hp := gaussian_pullback_measurePreserving t ht
  let F : (ℕ → ℝ) → Option {k : ℕ // k ≠ j} → ℕ → ℝ := fun g k i => g (t (k,i))
  have hmF : Measurable F := by unfold F; fun_prop
  have hF : gaussianCoordinates.map F = Measure.infinitePi
      (fun _ : Option {k : ℕ // k ≠ j} => gaussianCoordinates) := by
    change gaussianCoordinates.map
      ((MeasurableEquiv.curry (Option {k : ℕ // k ≠ j}) ℕ ℝ) ∘
        (fun g => fun p => g (t p))) = _
    rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable,hp.map_eq,
      Measure.infinitePi_map_curry (fun (_ : Option {k : ℕ // k ≠ j}) (_ : ℕ) => gaussianReal 0 1)]
    rfl
  have hs := infinitePi_option_split gaussianCoordinates
    (fun _ : {k : ℕ // k ≠ j} => gaussianCoordinates)
  have hc : (fun i : Option {k : ℕ // k ≠ j} =>
      i.elim gaussianCoordinates (fun _ => gaussianCoordinates)) = (fun _ => gaussianCoordinates) := by
    funext i; cases i <;> rfl
  rw [hc] at hs
  have he : gaussianNamespaceSplit j =
      (fun q : Option {k : ℕ // k ≠ j} → ℕ → ℝ => (q none,fun k => q (some k))) ∘ F := by
    rfl
  rw [he,← Measure.map_map (by fun_prop) hmF,hF]
  exact hs

end IsingPerceptron

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

lemma integrable_exp_bounded_add {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {H B : X → ℝ} (he : Integrable (fun x => Real.exp (H x)) ν)
    (hB : Measurable B) {K : ℝ} (hbound : ∀ x, B x ≤ K) :
    Integrable (fun x => Real.exp (B x+H x)) ν := by
  have hm : AEStronglyMeasurable (fun x => Real.exp (H x)*Real.exp (B x)) ν :=
    he.aestronglyMeasurable.mul hB.exp.aestronglyMeasurable
  apply (he.const_mul (Real.exp K)).mono'
  · simpa only [Real.exp_add,mul_comm,Pi.mul_apply] using hm
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_add]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound x)) (Real.exp_pos _).le)

lemma cgf_fold {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H Y : X → ℝ) (t : ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (het : Integrable (fun x => Real.exp (H x+t*Y x)) ν) :
    cgf Y (gibbsProbability ν H) t =
      Real.log (referencePartition ν (fun x => H x+t*Y x)) - Real.log (referencePartition ν H) := by
  rw [gibbsProbability_eq_tilted _ _ he]
  unfold cgf mgf
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  rw [Real.log_div (ne_of_gt (_root_.MeasureTheory.integral_exp_pos het))
    (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))]
  rfl

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_labeledSpinReference {N : ℕ} (n : ℕ) (ν : Measure (Spin N))
    [IsProbabilityMeasure ν] : Measurable (labeledSpinReference n ν) := by
  let κ : Kernel (LabeledTree n) (LabeledLeaf n) :=
    ⟨labeledLeafLaw n,measurable_labeledLeafLaw n⟩
  have : IsMarkovKernel κ := ⟨fun T => by
    change IsProbabilityMeasure (labeledLeafLaw n T)
    infer_instance⟩
  have he : (fun T => ((Kernel.const (LabeledTree n) ν).prod κ) T) =
      labeledSpinReference n ν := by
    funext T
    rw [Kernel.prod_apply,Kernel.const_apply]
    rfl
  rw [← he]
  exact ((Kernel.const (LabeledTree n) ν).prod κ).measurable

lemma measurable_patternBase_infinite {N : ℕ} {A : Type*} [MeasurableSpace A]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (fun p : (ℕ × (ℕ → A)) × Spin N =>
      patternBase φ (fun i : Fin p.1.1 => p.1.2 i) p.2) := by
  have hφm : Measurable (fun p : A × Spin N => φ p.1 p.2) :=
    measurable_from_prod_countable_left (fun x => (measurable_pi_apply x).comp hm)
  let F : ℕ × ((ℕ → A) × Spin N) → ℝ := fun p =>
    patternBase φ (fun i : Fin p.1 => p.2.1 i) p.2.2
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro M
    change Measurable (fun p : (ℕ → A) × Spin N => ∑ i : Fin M, φ (p.1 i) p.2)
    apply Finset.measurable_sum
    intro i _
    have hi : Measurable (fun p : (ℕ → A) × Spin N => (p.1 (i:ℕ),p.2)) := by fun_prop
    exact hφm.comp hi
  exact hF.comp (show Measurable (fun p : (ℕ × (ℕ → A)) × Spin N =>
    (p.1.1,(p.1.2,p.2))) from by fun_prop)

lemma enrichedCylinder_exp_ae {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    ∀ᵐ p ∂enrichedCylinderLaw P r n b,
      Integrable (fun s => Real.exp
        (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1 +
        cylinderField (enrichedCoefficients n h u s) p.2)) (labeledSpinReference n ν p.1.2) := by
  have he := random_cylinder_all_exp_ae (P := enrichedCylinderBaseLaw P r n b)
    (ν := fun p : EnrichedCylinderBase n A => labeledSpinReference n ν p.2)
    ((measurable_labeledSpinReference n ν).comp measurable_snd)
    (enrichedCoefficients n h u) (enrichedCoefficients_variance_le hN n hh h0 u hu)
  filter_upwards [he] with p hp
  apply integrable_exp_bounded_add (by simpa using hp 1) (measurable_of_countable _)
    (K := (p.1.1.1:ℝ)*K)
  intro s
  let y : Fin p.1.1.1 → A := fun i => p.1.1.2 i
  have hb : |patternBase φ y s.1| ≤ ‖patternBase φ y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (patternBase φ y) s.1
  exact (le_abs_self _).trans (hb.trans (patternBase_bound hK hφ y))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedCGF
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma integral_comp_preserving_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    {F : B → ℝ} (hF : AEStronglyMeasurable F ν) :
    (∫ x, F (f x) ∂μ) = ∫ y, F y ∂ν := by
  have h := integral_map hf.measurable.aemeasurable (hf.map_eq.symm ▸ hF)
  rw [hf.map_eq] at h
  exact h.symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma cylinder_weighted_variant_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j))
    (c : ι → ℝ) :
    (∑ i, c i • a i).sum (fun _ v => v^2) = (∑ i, c i • b i).sum (fun _ v => v^2) := by
  classical
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,hc]

lemma dual_cylinderField {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    L (fun i => cylinderField (a i) g) =
      cylinderField (∑ i, L (Pi.single i 1) • a i) g := by
  have hv : (fun i => cylinderField (a i) g) =
      ∑ i, cylinderField (a i) g • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv,map_sum,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,cylinderField_smul,smul_eq_mul,mul_comm]

 

lemma cylinder_finite_law_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j)) :
    gaussianCoordinates.map (fun g i => cylinderField (a i) g) =
      gaussianCoordinates.map (fun g i => cylinderField (b i) g) := by
  classical
  have ha : Measurable (fun g i => cylinderField (a i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))
  have hb : Measurable (fun g i => cylinderField (b i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,integral_map ha.aemeasurable (by fun_prop),
    integral_map hb.aemeasurable (by fun_prop)]
  simp only [dual_cylinderField]
  rw [← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    ← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    cylinderField_law,cylinderField_law,cylinder_weighted_variant_eq a b hc]

 

theorem cylinder_fields_law_eq {X : Type*}
    (a b : X → ℕ →₀ ℝ) (hc : ∀ x y, cylinderCross (a x) (a y) = cylinderCross (b x) (b y)) :
    gaussianCoordinates.map (fun g x => cylinderField (a x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (b x) g) := by
  classical
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))).aemeasurable
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))).aemeasurable).mpr
  intro I
  exact cylinder_finite_law_eq (fun i : I => a i) (fun i : I => b i) (fun i j => hc i j)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianPair_preserving : MeasurePreserving gaussianPair gaussianCoordinates
    (gaussianCoordinates.prod gaussianCoordinates) := by
  have hs : MeasurePreserving (gaussianNamespaceSplit 0) gaussianCoordinates
      (gaussianCoordinates.prod (otherNamespacesLaw 0)) :=
    ⟨measurable_gaussianNamespaceSplit 0,gaussianNamespaceSplit_law 0⟩
  have he := measurePreserving_eval_infinitePi
    (fun _ : {k : ℕ // k ≠ 0} => gaussianCoordinates) ⟨1,by decide⟩
  exact ((MeasurePreserving.id gaussianCoordinates).prod he).comp hs

lemma gaussianSumCoefficients_field {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x : X) (g : ℕ → ℝ) :
    cylinderField (gaussianSumCoefficients a b t x) g =
      cylinderField (a x) (gaussianPair g).1 + t*cylinderField (b x) (gaussianPair g).2 := by
  unfold gaussianSumCoefficients
  rw [cylinderField_finset_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderField_tag,cylinderField_smul,gaussianPair]

lemma gaussianSumCoefficients_cross {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x y : X) :
    cylinderCross (gaussianSumCoefficients a b t x) (gaussianSumCoefficients a b t y) =
      cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y) := by
  unfold gaussianSumCoefficients
  rw [cylinderCross_tagged_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderCross_smul,pow_two]

 

theorem cylinder_independent_sum_law {X : Type*} (a b c : X → ℕ →₀ ℝ) (t : ℝ)
    (hc : ∀ x y, cylinderCross (c x) (c y) = cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y)) :
    (gaussianCoordinates.prod gaussianCoordinates).map
      (fun g x => cylinderField (a x) g.1+t*cylinderField (b x) g.2) =
      gaussianCoordinates.map (fun g x => cylinderField (c x) g) := by
  rw [← gaussianPair_preserving.map_eq,Measure.map_map (by
    apply Measurable.of_eval; intro x
    exact ((measurable_cylinderField (a x)).comp measurable_fst).add
      (((measurable_cylinderField (b x)).comp measurable_snd).const_mul t)) gaussianPair_preserving.measurable]
  have he : (fun g x => cylinderField (a x) (gaussianPair g).1+t*cylinderField (b x) (gaussianPair g).2) =
      (fun g x => cylinderField (gaussianSumCoefficients a b t x) g) := by
    funext g x; exact (gaussianSumCoefficients_field a b t x g).symm
  change gaussianCoordinates.map (fun g x => cylinderField (a x) (gaussianPair g).1+
    t*cylinderField (b x) (gaussianPair g).2) = _
  rw [he]
  exact cylinder_fields_law_eq _ _ (fun x y => (gaussianSumCoefficients_cross a b t x y).trans (hc x y).symm)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Derivative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_sum_identDistrib {Ω X : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (a b c : X → ℕ →₀ ℝ) (t : ℝ)
    (hc : ∀ x y, cylinderCross (c x) (c y) = cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y)) :
    IdentDistrib
      (fun z : (Ω × (ℕ → ℝ)) × (ℕ → ℝ) =>
        (z.1.1,fun x => cylinderField (a x) z.1.2+t*cylinderField (b x) z.2))
      (fun z : Ω × (ℕ → ℝ) => (z.1,fun x => cylinderField (c x) z.2))
      ((P.prod gaussianCoordinates).prod gaussianCoordinates) (P.prod gaussianCoordinates) := by
  let f : ((ℕ → ℝ) × (ℕ → ℝ)) → (X → ℝ) :=
    fun z x => cylinderField (a x) z.1+t*cylinderField (b x) z.2
  let g : (ℕ → ℝ) → (X → ℝ) := fun z x => cylinderField (c x) z
  have hf : Measurable f := by
    unfold f; apply Measurable.of_eval; intro x
    exact ((measurable_cylinderField (a x)).comp measurable_fst).add
      (((measurable_cylinderField (b x)).comp measurable_snd).const_mul t)
  have hg : Measurable g := by unfold g; apply Measurable.of_eval; intro x; exact measurable_cylinderField _
  have hp : MeasurePreserving (MeasurableEquiv.prodAssoc : ((Ω × (ℕ → ℝ)) × (ℕ → ℝ)) → Ω × ((ℕ → ℝ) × (ℕ → ℝ)))
      ((P.prod gaussianCoordinates).prod gaussianCoordinates) (P.prod (gaussianCoordinates.prod gaussianCoordinates)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod⟩
  refine ⟨((measurable_id.prodMap hf).comp hp.measurable).aemeasurable,
    (measurable_id.prodMap hg).aemeasurable,?_⟩
  change ((P.prod gaussianCoordinates).prod gaussianCoordinates).map
    ((Prod.map id f) ∘ MeasurableEquiv.prodAssoc) =
      (P.prod gaussianCoordinates).map (Prod.map id g)
  rw [← Measure.map_map (measurable_id.prodMap hf) hp.measurable,hp.map_eq,
    ← Measure.map_prod_map P (gaussianCoordinates.prod gaussianCoordinates) measurable_id hf,
    ← Measure.map_prod_map P gaussianCoordinates measurable_id hg]
  rw [show (gaussianCoordinates.prod gaussianCoordinates).map f = gaussianCoordinates.map g from
    cylinder_independent_sum_law a b c t hc]

lemma random_cgf_insertion_eq {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (b : X → ℕ →₀ ℝ) {K : ℝ} (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    ∀ᵐ z ∂P.prod gaussianCoordinates,
      cgf (fun x => cylinderField (b x) z.2) (gibbsProbability (ν z.1) (fun x => H (z.1,x))) t =
        Real.log (∫ x, Real.exp (H (z.1,x)+t*cylinderField (b x) z.2) ∂ν z.1)-
          Real.log (∫ x, Real.exp (H (z.1,x)) ∂ν z.1) := by
  have hη := measurable_gibbsProbability hν hH
  have ht := random_cylinder_all_exp_ae (P := P) hη b hb
  have he' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := gaussianCoordinates)).tendsto_ae.eventually he
  filter_upwards [ht,he'] with z ht he
  have hi := ht t
  rw [gibbsProbability_eq_tilted _ _ he,integrable_tilted_iff he] at hi
  have hisum : Integrable (fun x => Real.exp (H (z.1,x)+t*cylinderField (b x) z.2)) (ν z.1) := by
    simpa only [smul_eq_mul,← Real.exp_add] using hi
  exact cgf_fold _ _ _ _ he hisum

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma externalFieldCoefficients_cross {N : ℕ} (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (s t : Spin N × LabeledLeaf n) :
    cylinderCross (externalFieldCoefficients n h s) (externalFieldCoefficients n h t) =
      h (labeledCommonDepth n s.2 t.2) * ∑ i, spinValue (s.1 i)*spinValue (t.1 i) := by
  exact treeField_path_cross n s.2 t.2 hh h0 _ _

lemma monotone_field_add {h l : ℕ → ℝ} (hh : Monotone h) (hl : Monotone l)
    {a : ℝ} (ha : 0 ≤ a) : Monotone (fun i => h i+a*l i) := by
  intro i j hij
  exact add_le_add (hh hij) (mul_le_mul_of_nonneg_left (hl hij) ha)

lemma field_add_nonneg {h l : ℕ → ℝ} (h0 : 0 ≤ h 0) (l0 : 0 ≤ l 0)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ h 0+a*l 0 := add_nonneg h0 (mul_nonneg ha l0)

lemma enrichedCoefficients_field_add_cross {N : ℕ} (n : ℕ) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a) (s t : Spin N × LabeledLeaf n) :
    cylinderCross (enrichedCoefficients n (fun i => h i+a*l i) u s)
        (enrichedCoefficients n (fun i => h i+a*l i) u t) =
      cylinderCross (enrichedCoefficients n h u s) (enrichedCoefficients n h u t) +
        a*cylinderCross (externalFieldCoefficients n l s) (externalFieldCoefficients n l t) := by
  unfold enrichedCoefficients
  rw [cylinderCross_tagged_sum,cylinderCross_tagged_sum]
  simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]
  rw [externalFieldCoefficients_cross n (monotone_field_add hh hl ha) (field_add_nonneg h0 l0 ha),
    externalFieldCoefficients_cross n hh h0,externalFieldCoefficients_cross n hl l0]
  ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_enrichedHamiltonian {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ}
    (hm : Measurable φ) :
    Measurable (fun p : EnrichedCylinderData n A × (Spin N × LabeledLeaf n) =>
      enrichedHamiltonian n h u φ p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  unfold enrichedHamiltonian
  have hg : Measurable (fun p : EnrichedCylinderData n A => (p.1.1,s.1)) :=
    measurable_fst.fst.prodMk measurable_const
  exact ((measurable_patternBase_infinite hm).comp hg).add
    ((measurable_cylinderField (enrichedCoefficients n h u s)).comp measurable_snd)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_enrichedFieldFunctional {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (d : ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedFieldFunctional n d ν φ) := by
  have hH : Measurable (fun p : (EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      patternBase φ (fun i : Fin p.1.1.1.1 => p.1.1.1.2 i) p.2.1 + p.1.2 p.2) := by
    apply measurable_from_prod_countable_left
    intro s
    have hp : Measurable (fun p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ) => (p.1.1,s.1)) :=
      measurable_fst.fst.prodMk measurable_const
    exact ((measurable_patternBase_infinite hm).comp hp).add
      ((measurable_pi_apply s).comp measurable_snd)
  exact (((measurable_random_referencePartition
    (ν := fun p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ) => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd) hH).log).sub_const _).div_const _

lemma measurable_enrichedGibbsReference {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) : Measurable (enrichedGibbsReference n h u ν φ) :=
  measurable_gibbsProbability
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)

lemma enrichedFieldInsertedPressure_law {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ)
    {h l : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν] {φ : A → Spin N → ℝ}
    (hm : Measurable φ) {a : ℝ} (ha : 0 ≤ a) :
    IdentDistrib (enrichedFieldInsertedPressure n h l u ν φ a)
      (enrichedCylinderPressure n (fun i => h i+a*l i) u ν φ)
      ((enrichedCylinderLaw P r n b).prod gaussianCoordinates) (enrichedCylinderLaw P r n b) := by
  have he := gaussian_sum_identDistrib (enrichedCylinderBaseLaw P r n b)
    (enrichedCoefficients n h u) (externalFieldCoefficients n l)
    (enrichedCoefficients n (fun i => h i+a*l i) u) (Real.sqrt a) (fun s t => by
      rw [Real.sq_sqrt ha]
      exact enrichedCoefficients_field_add_cross n hh h0 hl l0 u ha s t)
  exact he.comp (measurable_enrichedFieldFunctional n (h n+a*l n) ν hm)

lemma enrichedField_cgf_eq {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h l : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) (a : ℝ) :
    ∀ᵐ z ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates,
      enrichedFieldInsertedPressure n h l u ν φ a z =
        enrichedCylinderPressure n h u ν φ z.1 +
        (cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
          (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a))/N-a*l n/2 := by
  have he := random_cgf_insertion_eq
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)
    (enrichedCylinder_exp_ae hN n b hh h0 u hu ν P hK hφ r)
    (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) (Real.sqrt a)
  filter_upwards [he] with z hz
  change cgf _ (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a) = _ at hz
  rw [hz]
  unfold enrichedFieldInsertedPressure enrichedFieldFunctional enrichedCylinderPressure enrichedHamiltonian
  simp only [add_assoc]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedMeanPressure_field_insert {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    enrichedMeanPressure P r n b (fun i => h i+a*l i) u ν φ =
      enrichedMeanPressure P r n b h u ν φ +
      (∫ z : EnrichedCylinderData n A × (ℕ → ℝ),
        cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
          (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a)
        ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates)/N-a*l n/2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hib := (enrichedCylinderPressure_field_cap hN n b hb hh h0 (le_refl (h n)) u hu ν P hm hK hφ r
    (α := (r:ℝ)/N) (by rw [div_mul_cancel₀ _ hn])).1.integrable (by norm_num)
  have hib' := hib.comp_fst gaussianCoordinates
  have hic := integrable_random_cylinder_cgf (P := enrichedCylinderLaw P r n b)
    (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) (Real.sqrt a)
  change Integrable (fun p : EnrichedCylinderData n A × (ℕ → ℝ) =>
    enrichedCylinderPressure n h u ν φ p.1) ((enrichedCylinderLaw P r n b).prod gaussianCoordinates) at hib'
  change (∫ z, enrichedCylinderPressure n (fun i => h i+a*l i) u ν φ z ∂enrichedCylinderLaw P r n b) = _
  rw [← (enrichedFieldInsertedPressure_law P r n b hh h0 hl l0 u ν hm ha).integral_eq,
    integral_congr_ae (enrichedField_cgf_eq hN n b hh h0 hl l0 u hu ν P hm hK hφ r a)]
  have hs := integral_sub (hib'.add (hic.div_const (N:ℝ))) (integrable_const (a*l n/2))
  simp only [Pi.add_apply] at hs
  rw [hs]
  have hadd := integral_add hib' (hic.div_const (N:ℝ))
  rw [hadd,integral_div]
  rw [integral_fun_fst (fun p : EnrichedCylinderData n A => enrichedCylinderPressure n h u ν φ p)]
  simp [enrichedMeanPressure]

end IsingPerceptron

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
namespace IsingPerceptron

lemma gaussian_log_partition_mean_bounds {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    0 ≤ (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ∧
      (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ≤ K/2 := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hiH := gaussian_field_integrable (ν := ν) hm hg hv
  have hexp := gaussian_field_exp_integrable (ν := ν) hm hg hv 1
  simp only [one_mul,one_pow] at hexp
  have hZ : Integrable Z μ := hexp.1.integral_prod_left
  have hpos : ∀ᵐ ω ∂μ, 0 < Z ω := by
    filter_upwards [hexp.1.prod_right_ae] with ω hω
    exact MeasureTheory.integral_exp_pos hω
  have hiLog : Integrable (fun ω => Real.log (Z ω)) μ :=
    ((memLp_two_iff_integrable_sq hmZ.log.aestronglyMeasurable).2
      (gaussian_log_partition_second hm hg hv).1).integrable (by norm_num)
  have hexplog : Integrable (fun ω => Real.exp (Real.log (Z ω))) μ := by
    apply hZ.congr
    filter_upwards [hpos] with ω hω
    exact (Real.exp_log hω).symm
  have hmean : (∫ ω, ∫ x, H (ω,x) ∂ν ∂μ) = 0 := by
    rw [integral_integral_swap (f := fun ω x => H (ω,x)) hiH]
    have hz : ∀ x, (∫ ω, H (ω,x) ∂μ) = 0 := by
      intro x
      have hmx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
      have he := integral_map hmx.aemeasurable (measurable_id.aestronglyMeasurable :
        AEStronglyMeasurable (fun y : ℝ => y) (μ.map (fun ω => H (ω,x))))
      simp only [hg x,id_eq,integral_id_gaussianReal] at he
      exact he.symm
    simp_rw [hz]
    simp
  refine ⟨?_, ?_⟩
  · rw [← hmean]
    apply integral_mono_ae hiH.integral_prod_left hiLog
    filter_upwards [hiH.prod_right_ae,hexp.1.prod_right_ae,hpos] with ω hω heω hpω
    exact Real.exp_le_exp.mp (by
      rw [Real.exp_log hpω]
      exact exp_integral_le_partition hω heω)
  · apply Real.exp_le_exp.mp
    calc
      _ ≤ ∫ ω, Real.exp (Real.log (Z ω)) ∂μ := exp_integral_le_partition hiLog hexplog
      _ = ∫ ω, Z ω ∂μ := integral_congr_ae (hpos.mono (fun _ h => Real.exp_log h))
      _ ≤ _ := hexp.2

lemma cylinder_cgf_mean_bounds {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    0 ≤ (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ∧
      (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ≤ t^2*K/2 := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (A z.2) z.1) :=
    (measurable_cylinderFields A).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((A x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((A x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg _)
  exact gaussian_log_partition_mean_bounds (ν := ν) hm (fun x => cylinder_scaled_law A x t) hv

lemma random_cylinder_cgf_mean_bounds {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    let F := fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (A x) z.2) (ν z.1) t
    0 ≤ (∫ z, F z ∂P.prod gaussianCoordinates) ∧
      (∫ z, F z ∂P.prod gaussianCoordinates) ≤ t^2*K/2 := by
  have hi := integrable_random_cylinder_cgf (P := P) hν A hA t
  dsimp only
  rw [integral_prod _ hi]
  refine ⟨integral_nonneg (fun ω => (cylinder_cgf_mean_bounds (ν ω) A hA t).1), ?_⟩
  calc
    _ ≤ ∫ _ : Ω, t^2*K/2 ∂P := integral_mono hi.integral_prod_left
      (integrable_const _) (fun ω => (cylinder_cgf_mean_bounds (ν ω) A hA t).2)
    _ = _ := by simp



end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityQuadraticResidualGibbs_probability _root_.OAI.InvariantIsing.cavityQuadraticResidualKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualBaseKernel_markov _root_.OAI.InvariantIsing.cavityRootedResidualKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.InvariantIsing.rootedResidualPrior_markov
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
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
namespace IsingPerceptron

theorem enrichedMeanPressure_recursion {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b h u ν φ =
      ((∫ p, energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
          (enrichedPoissonBase n h u φ p)
        ∂(poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
          (Measure.infinitePi (fun _ : ℕ => P)))) - N*h n/2)/N := by
  let μ := fun i => enrichedIncrementLaw N n h u (i+1)
  let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
    (Measure.infinitePi (fun _ : ℕ => P)))
  let R := Q.prod (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
  have hL := (enriched_poisson_variance hN n b hb hh h0 u hu ν P hm hK hφ r).1
  have hLd : MemLp (fun p => enrichedPoissonLog n b h u ν φ p / N) 2 R := by
    simpa only [div_eq_mul_inv] using hL.mul_const (N:ℝ)⁻¹
  have hco := hLd.comp_measurePreserving (enrichedToNoise_preserving P r n b h u)
  have hco' := MemLp.ae_eq (enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm).symm hco
  unfold enrichedMeanPressure
  simp_rw [enrichedCylinderPressure_eq_coordinates]
  rw [integral_comp_preserving_ae (enrichedCylinderToCoordinates_preserving P r N n b)
    hco'.aestronglyMeasurable]
  rw [integral_congr_ae (enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm)]
  rw [integral_comp_preserving_ae (enrichedToNoise_preserving P r n b h u) hLd.aestronglyMeasurable]
  rw [integral_div]
  change (∫ p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n,
    (cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2-(N:ℝ)*h n/2) ∂ R)/(N:ℝ) = _
  rw [integral_sub ((enriched_poisson_unshifted hN n b hb hh h0 u hu ν P hm hK hφ r).1.integrable (by norm_num))
    (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  congr 1
  congr 1
  exact cascadeEnergyLog_total_mean Q n b hb μ ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (measurable_enrichedPoissonBase n h u hm)
    (enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1) hh h0 u hu ν P hm hK hφ r).1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma spinSign_integral (z : ℝ) :
    (∫ x : Fin 2, Real.exp (z*spinValue x) ∂(PMF.uniformOfFintype (Fin 2)).toMeasure) = Real.cosh z := by
  rw [integral_fintype (Integrable.of_finite),Fin.sum_univ_two]
  simp only [measureReal_def,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,spinValue]
  norm_num
  rw [Real.cosh_eq]
  ring

lemma finiteLogIntegral_magnetic {N : ℕ} (z : Fin N → ℝ) :
    finiteLogIntegral (spinLaw N) (magneticEnergy z) = ∑ i, Real.log (Real.cosh (z i)) := by
  unfold finiteLogIntegral magneticEnergy spinLaw
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (z i*spinValue x))]
  simp only [spinSign_integral]
  rw [Real.log_prod (fun i _ => (Real.cosh_pos _).ne')]

lemma logMean_independent_sum {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (F : ι → ℝ → ℝ)
    {b : ℝ} (_hb : b ≠ 0)
    (_hF : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (fun x => Real.exp (b*F i x)) (μ i)) :
    logMean b (Measure.pi μ) (fun z => ∑ i, F i (z i)) = ∑ i, logMean b (μ i) (F i) := by
  have hp (i : ι) : 0 < ∫ x, Real.exp (b*F i x) ∂μ i :=
    integral_exp_pos (μ i) (F i) (hi i)
  unfold logMean
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (b*F i x)),Real.log_prod (fun i _ => (hp i).ne'),Finset.sum_div]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticEnergy_add {N : ℕ} (z w : Fin N → ℝ) :
    magneticEnergy (z+w) = magneticEnergy z+magneticEnergy w := by
  ext x
  simp [magneticEnergy,add_mul,Finset.sum_add_distrib]

lemma enrichedIncrement_zero {N n : ℕ} (h : ℕ → ℝ) (i : ℕ)
    (g : Fin (Fintype.card (EnrichedBlock N)) → ℝ) :
    enrichedIncrement N n h 0 i g =
      magneticEnergy (fun j => pathAmplitude h i*g ((Fintype.equivFin (EnrichedBlock N)) (.inl j))) := by
  ext x
  unfold enrichedIncrement enrichedCoefficientsFin
  have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
    (fun j => enrichedLevelCoefficient n h 0 i x j*g ((Fintype.equivFin (EnrichedBlock N)) j))
  simp only [Equiv.apply_symm_apply] at he
  rw [he]
  simp only [Fintype.sum_sum_type,enrichedLevelCoefficient,Pi.zero_apply,mul_zero,
    zero_mul,Finset.sum_const_zero,add_zero, magneticEnergy]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma enrichedIncrementLaw_zero (N n : ℕ) (h : ℕ → ℝ) (i : ℕ) :
    enrichedIncrementLaw N n h 0 i = magneticIncrementLaw N (pathAmplitude h i) := by
  let e := Fintype.equivFin (EnrichedBlock N)
  let tag : Fin N → ℕ := fun j => (e (.inl j)).val
  have ht : Function.Injective tag := fun j k hjk => Sum.inl_injective (e.injective (Fin.ext hjk))
  have hf := gaussian_pullback_measurePreserving (fun j : Fin (Fintype.card (EnrichedBlock N)) => j.val)
    Fin.val_injective
  have hg := gaussian_pullback_measurePreserving tag ht
  rw [Measure.infinitePi_eq_pi] at hf hg
  apply Subtype.ext
  change (Measure.pi _).map (enrichedIncrement N n h 0 i) = (Measure.pi _).map _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun j => pathAmplitude h i*z j)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [← hf.map_eq,← hg.map_eq,Measure.map_map (measurable_enrichedIncrement N n h 0 i)
     hf.measurable,Measure.map_map hm hg.measurable]
  congr 1
  ext g x
  rw [Function.comp_apply,Function.comp_apply,enrichedIncrement_zero]

lemma logMean_magneticIncrement {N : ℕ} (a b : ℝ) (F : (Spin N → ℝ) → ℝ)
    (hF : Measurable F) :
    logMean b (magneticIncrementLaw N a : Measure (Spin N → ℝ)) F =
      logMean b (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
        (fun z => F (magneticEnergy (fun i => a*z i))) := by
  unfold logMean
  change Real.log (∫ H, Real.exp (b*F H) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
    (fun z => magneticEnergy (fun i => a*z i)))/b = _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => a*z i)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [integral_map hm.aemeasurable
    ((hF.const_mul b).exp.aestronglyMeasurable)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticRecursion_growth (n : ℕ) (a b : ℕ → ℝ) (hb : ∀ i < n, 0 < b i) :
    Measurable (magneticRecursion n a b) ∧ HasLinearGrowth (magneticRecursion n a b) := by
  induction n generalizing a b with
  | zero => exact ⟨measurable_logCosh,logCosh_linearGrowth⟩
  | succ n ih =>
    have H := ih (fun i => a (i+1)) (fun i => b (i+1)) (fun i hi => hb (i+1) (by omega))
    exact ⟨measurable_gaussianTransform H.1 _ _,gaussianTransform_positive_linearGrowth H.1 H.2 _ (hb 0 (by omega))⟩

lemma magneticRecursion_eq_fold (n : ℕ) (a b : ℕ → ℝ) :
    magneticRecursion n a b =
      (List.ofFn (fun i : Fin n => ((a i)^2,b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) := by
  induction n generalizing a b with
  | zero => simp [magneticRecursion]
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    simp only [magneticRecursion,ih,Fin.val_zero,Fin.val_succ]

lemma energyRecursion_magnetic (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N) (magneticEnergy z) =
      ∑ i, magneticRecursion n a b (z i) := by
  induction n generalizing a b z with
  | zero => exact finiteLogIntegral_magnetic z
  | succ n ih =>
    let U := magneticRecursion n (fun i => a (i+1)) (fun i => b (i+1))
    have hU := magneticRecursion_growth n (fun i => a (i+1)) (fun i => b (i+1))
      (fun i hi => hb (i+1) (by omega))
    change logMean (b 0) (magneticIncrementLaw N (a 0) : Measure (Spin N → ℝ))
      (fun H => energyRecursion n (fun i => b (i+1)) (fun i => magneticIncrementLaw N (a (i+1)))
        (spinLaw N) (magneticEnergy z+H)) = _
    have hm : Measurable (fun H : Spin N → ℝ => energyRecursion n (fun i => b (i+1))
        (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N) (magneticEnergy z+H)) :=
      (measurable_energyRecursion _ _ _ _).comp (measurable_const.add measurable_id)
    rw [logMean_magneticIncrement _ _ _ hm]
    have H (g : Fin N → ℝ) : energyRecursion n (fun i => b (i+1))
      (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N)
        (magneticEnergy z+magneticEnergy (fun i => a 0*g i)) = ∑ i, U (z i+a 0*g i) := by
      rw [← magneticEnergy_add]
      exact ih _ _ (fun i hi => ha (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) _
    simp_rw [H]
    rw [logMean_independent_sum (fun _ : Fin N => gaussianReal 0 1)
      (fun i t => U (z i+a 0*t)) (hb 0 (by omega)).ne']
    · apply Finset.sum_congr rfl
      intro i _
      simp only [magneticRecursion,gaussianTransform,(hb 0 (by omega)).ne',ite_false, if_false,
        Real.sqrt_sq (ha 0 (by omega)),logMean,U]
    · intro i
      exact hU.1.comp (measurable_const.add (measurable_id.const_mul _))
    · intro i
      exact integrable_exp_of_linearGrowth (gaussianReal 0 1)
        (gaussianReal_exponentialNormMoments _ _)
        (hU.1.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hU.2.add_left (z i)).scale_argument (a 0)) _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_linearGrowth_integrable {F : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (m : ℝ) (v : ℝ≥0) : Integrable F (gaussianReal m v) := by
  obtain ⟨C,L,hC,hL,h⟩ := hG
  have hi : Integrable (fun x : ℝ => C+L*‖x‖) (gaussianReal m v) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl).norm.const_mul L)
  exact hi.mono' hF.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using h x))

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
namespace IsingPerceptron



lemma integral_magnetic_energyRecursion (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (a₀ : ℝ) :
    (∫ z, energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N)
       (magneticEnergy (fun i => a₀*z i)) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (N:ℝ)*(∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) := by
  have hU := magneticRecursion_growth n a b hb
  have hm : Measurable (fun z : ℝ => magneticRecursion n a b (a₀*z)) :=
    hU.1.comp (measurable_id.const_mul _)
  have hi := gaussian_linearGrowth_integrable hm (hU.2.scale_argument a₀) 0 1
  have hpi (i : Fin N) : Integrable (fun z : Fin N → ℝ => magneticRecursion n a b (a₀*z i))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
      (g := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable).mpr hi
  simp_rw [energyRecursion_magnetic N n a b ha hb]
  rw [integral_finsetSum _ (fun i _ => hpi i)]
  have he (i : Fin N) :
    (∫ z : Fin N → ℝ, magneticRecursion n a b (a₀*z i) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) :=
    integral_comp_preserving_ae (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)
      (F := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

 

theorem enrichedMeanPressure_initial_zero {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) :
    enrichedMeanPressure P 0 n b h 0 (spinLaw N) φ = magneticFieldValue n b h := by
  have hu : ∀ j : Fin N, |(0 : Fin N → ℝ) j| ≤ 2 := by intro j; norm_num
  let μ := fun i => enrichedIncrementLaw N n h 0 (i+1)
  let γ := Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)
  let ρ := Measure.infinitePi (fun _ : ℕ => P)
  have hL := (enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1)
    hh h0 0 hu (spinLaw N) P hm hK hφ 0).1
  have hi : Integrable (fun p => energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p))
      ((poissonMeasure 0).prod (γ.prod ρ)) := hL.integrable (by norm_num)
  rw [enrichedMeanPressure_recursion hN n b hb hh h0 0 hu (spinLaw N) P hm hK hφ 0]
  change ((∫ p, energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p)
    ∂(poissonMeasure 0).prod (γ.prod ρ))-(N:ℝ)*h n/2)/(N:ℝ) = _
  rw [integral_prod _ hi,poissonMeasure_zero_eq_dirac,integral_dirac]
  have hbase (p : (Fin (EnrichedRootSize N) → ℝ) × (ℕ → A)) :
      enrichedPoissonBase n h 0 φ (0,p) = enrichedIncrement N n h 0 0 p.1 := by
    ext x
    simp [enrichedPoissonBase,enrichedBaseEnergy,rootPrefix,patternBase]
  simp_rw [hbase]
  rw [integral_fun_fst (fun z => energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z))]
  simp only [probReal_univ,one_smul]
  have hmap : (∫ z, energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z) ∂γ) =
      ∫ H, energyRecursion n b μ (spinLaw N) H ∂(enrichedIncrementLaw N n h 0 0 : Measure (Spin N → ℝ)) := by
    symm
    exact integral_map (measurable_enrichedIncrement N n h 0 0).aemeasurable
      (measurable_energyRecursion _ _ _ _).aestronglyMeasurable
  rw [hmap]
  dsimp only [μ]
  simp_rw [enrichedIncrementLaw_zero]
  have hmag : (∫ H, energyRecursion n b
        (fun i => magneticIncrementLaw N (pathAmplitude h (i+1))) (spinLaw N) H
      ∂(magneticIncrementLaw N (pathAmplitude h 0) : Measure (Spin N → ℝ))) =
      (N:ℝ)*(∫ z, magneticRecursion n (fun i => pathAmplitude h (i+1)) b (pathAmplitude h 0*z)
        ∂gaussianReal 0 1) := by
    change (∫ H, energyRecursion n b (fun i => magneticIncrementLaw N (pathAmplitude h (i+1)))
      (spinLaw N) H ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
        (fun z => magneticEnergy (fun i => pathAmplitude h 0*z i))) = _
    have hme : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => pathAmplitude h 0*z i)) :=
      (measurable_magneticEnergy N).comp (by fun_prop)
    rw [integral_map hme.aemeasurable (measurable_energyRecursion _ _ _ _).aestronglyMeasurable]
    exact integral_magnetic_energyRecursion N n _ b (fun i _ => Real.sqrt_nonneg _)
      (fun i hi => (hb.1 i hi).1) _
  rw [hmag]
  unfold magneticFieldValue
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalFiniteness
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Finiteness. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTransform_zero_variance (d : ℝ) (U : ℝ → ℝ) :
    gaussianTransform 0 d U = U := by
  ext x
  by_cases hd : d = 0
  · simp [gaussianTransform, hd]
  · simp [gaussianTransform, hd]

lemma magneticRecursion_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticRecursion n (fun _ => 0) b = fun x => Real.log (Real.cosh x) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [magneticRecursion, ih, zero_pow (by decide : 2 ≠ 0),
      gaussianTransform_zero_variance]

lemma magneticFieldValue_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticFieldValue n b (fun _ => 0) = 0 := by
  simp [magneticFieldValue, pathAmplitude, pathIncrement, magneticRecursion_zero]

 
lemma enrichedMeanPressure_field_add_le {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b (fun i => h i + l i) u ν φ ≤
      enrichedMeanPressure P r n b h u ν φ := by
  have he := enrichedMeanPressure_field_insert hN n b hb hh h0 hl l0 u hu ν P hm hK hφ r
    (a := 1) zero_le_one
  simp only [one_mul, Real.sqrt_one] at he
  have hc := (random_cylinder_cgf_mean_bounds (P := enrichedCylinderLaw P r n b)
    (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) 1).2
  simp only [one_pow, one_mul] at hc
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' : (∫ z : EnrichedCylinderData n A × (ℕ → ℝ),
      cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
        (enrichedGibbsReference n h u ν φ z.1) 1
        ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates) / (N : ℝ) ≤ l n / 2 :=
    (div_le_iff₀ hn).mpr (hc.trans_eq (by ring))
  rw [he]
  linarith

lemma magneticFieldValue_nonpos (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) :
    magneticFieldValue n b h ≤ 0 := by
  let P : Measure Unit := Measure.dirac ()
  let φ : Unit → Spin 1 → ℝ := fun _ _ => 0
  have hm : Measurable φ := measurable_const
  have hφ : ∀ y x, |φ y x| ≤ (0 : ℝ) := by intros; simp [φ]
  have hu : ∀ j : Fin 1, |(0 : Fin 1 → ℝ) j| ≤ 2 := by simp
  have he := enrichedMeanPressure_field_add_le (N := 1) (by decide) n b hb
    (h := fun _ => 0) monotone_const le_rfl hh h0 0 hu (spinLaw 1) P hm le_rfl hφ 0
  simp only [zero_add] at he
  rw [enrichedMeanPressure_initial_zero (by decide) n b hb hh h0 P hm le_rfl hφ,
    enrichedMeanPressure_initial_zero (by decide) n b hb monotone_const le_rfl P hm le_rfl hφ,
    magneticFieldValue_zero] at he
  exact he

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldBounds
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma heightSequence_mono (h : FieldStep) : Monotone (heightSequence h) := by
  intro i j hij
  apply h.ordered_height
  exact min_le_min_right h.depth hij

lemma heightSequence_nonneg (h : FieldStep) (i : ℕ) : 0 ≤ heightSequence h i :=
  h.nonneg _

lemma heightSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth) :
    heightSequence h i = h.height ⟨i, by omega⟩ := by
  simp only [heightSequence, min_eq_left hi]

/-- Equality with the scalar recursion, including its root Gaussian average
and diagonal covariance subtraction. -/
lemma fieldValue_eq_magneticFieldValue (h : FieldStep) :
    fieldValue h 0 = IsingPerceptron.magneticFieldValue h.depth
      (IsingPerceptron.chainExponent h.cut) (heightSequence h) := by
  let w := heightSequence h
  have hw : Monotone w := heightSequence_mono h
  have hw0 : 0 ≤ w 0 := heightSequence_nonneg h 0
  have htail : List.ofFn (fun i : Fin h.depth =>
      ((fieldIncrement h i.succ).2, (fieldIncrement h i.succ).1)) =
      List.ofFn (fun i : Fin h.depth =>
        ((IsingPerceptron.pathAmplitude w (i + 1)) ^ 2,
          IsingPerceptron.chainExponent h.cut i)) := by
    apply congrArg List.ofFn
    funext i
    rw [IsingPerceptron.pathAmplitude_sq hw hw0]
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false,
      Nat.add_sub_cancel, IsingPerceptron.pathIncrement,
      IsingPerceptron.chainExponent_apply h.cut i.isLt]
    congr 1
    change h.height i.succ - h.height ⟨i.val, by omega⟩ =
      heightSequence h (i.val + 1) - heightSequence h i.val
    rw [heightSequence_eq h _ (by omega), heightSequence_eq h _ (by omega)]
    rfl
  have hfold : (List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z)) =
      IsingPerceptron.magneticRecursion h.depth
        (fun i => IsingPerceptron.pathAmplitude w (i + 1))
        (IsingPerceptron.chainExponent h.cut) := by
    simp_rw [gaussianOperator_eq_transform]
    rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
      (g := fun sd f => IsingPerceptron.gaussianTransform sd.1 sd.2 f)]
    rw [List.map_ofFn]
    simp only [Function.comp_def]
    rw [htail]
    exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
      (fun i => IsingPerceptron.pathAmplitude w (i + 1))
      (IsingPerceptron.chainExponent h.cut)).symm
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    dsimp only [fieldIncrement]
    simp [h.first]
  have hzero : w 0 = h.height 0 := heightSequence_eq h 0 (Nat.zero_le _)
  have hlast : w h.depth = h.height (Fin.last h.depth) := heightSequence_eq h _ le_rfl
  have hamp : IsingPerceptron.pathAmplitude w 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, hzero]
  rw [fieldValue, List.ofFn_succ, List.foldr_cons, hfold, hroot]
  simp only [gaussianOperator, ite_true, if_true, zero_add, IsingPerceptron.magneticFieldValue]
  dsimp only [w] at hamp hlast ⊢
  rw [hamp, hlast]

lemma fieldValue_nonpos (h : FieldStep) : fieldValue h 0 ≤ 0 := by
  rw [fieldValue_eq_magneticFieldValue]
  exact IsingPerceptron.magneticFieldValue_nonpos _ _
    (IsingPerceptron.chainExponent_admissible h.ordered_cut h.first h.last)
    (heightSequence_mono h) (heightSequence_nonneg h 0)

lemma entropyFunctional_zero_oai : entropyFunctional (constantPath 0 (by constructor <;> norm_num)) = 0 := by
  apply le_antisymm _ (entropyFunctional_nonneg _)
  apply iSup_le
  intro h
  have hp : fieldPairing (constantPath 0 (by constructor <;> norm_num)) h = 0 := by
    simp [fieldPairing, constantPath]
  simp only [hp, zero_div, add_zero]
  exact_mod_cast fieldValue_nonpos h

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.entropyFunctional_zero_oai := @OAI.InvariantIsing.entropyFunctional_zero_oai
