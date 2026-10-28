-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:20:27.352511+00:00
-- url     : https://prove2.me/submissions/fd57181f-07f0-4251-ac30-4d1f13d28ce7

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section
-- module Solutions.OAIQ061_PF.Compat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CountableGaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma gaussianCoordinatePrefix_measurePreserving (n : ℕ) :
    MeasurePreserving (gaussianCoordinatePrefix n) countableGaussianLaw
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  refine ⟨by unfold gaussianCoordinatePrefix; fun_prop,?_⟩
  change Measure.map (fun g : ℕ → ℝ => fun i : Fin n => g i.val)
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)=_
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

variable {S : Type*}

lemma sum_range_cutoff (a : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range n, if i < m then a i else 0)=∑ i ∈ Finset.range (min n m), a i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      by_cases h : n < m
      · have hn : min n m=n := min_eq_left (by omega)
        have hn' : min (n+1) m=n+1 := min_eq_left (by omega)
        rw [hn,hn',ite_eq_left h,Finset.sum_range_succ]
      · have hn : min n m=m := min_eq_right (by omega)
        have hn' : min (n+1) m=m := min_eq_right (by omega)
        rw [hn,hn',ite_eq_right h,add_zero]

lemma truncatedCountableGaussianField_eq (v : ℕ → S → ℝ) (L : S → ℕ)
    (n : ℕ) (g : ℕ → ℝ) (x : S) :
    truncatedCountableGaussianField v L n g x=gaussianPrefixField v (min n (L x)) g x := by
  unfold truncatedCountableGaussianField gaussianPrefixField
  rw [Fin.sum_univ_eq_sum_range (fun i => g i * maskedGaussianCoefficient v L i x) n,
    Fin.sum_univ_eq_sum_range (fun i => g i * v i x) (min n (L x))]
  have he (i : ℕ) : g i*maskedGaussianCoefficient v L i x=
      if i<L x then g i*v i x else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  exact sum_range_cutoff _ n (L x)

lemma truncatedCountableGaussianField_eventually_eq (v : ℕ → S → ℝ) (L : S → ℕ)
    (x : S) : ∀ᶠ n in atTop, ∀ g,
      truncatedCountableGaussianField v L n g x=countableGaussianField v L g x := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn g
  rw [truncatedCountableGaussianField_eq,min_eq_right hn]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_FiniteOverlap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma poisson_power_integral (r : ℝ≥0) (a : ℝ) :
    ∫ n, a ^ n ∂poissonMeasure r = Real.exp ((r : ℝ) * (a - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial * a^n) =
        Real.exp (-(r : ℝ)) * ∑' n : ℕ, ((r : ℝ) * a)^n / n.factorial := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      rw [mul_pow]
      ring
    _ = Real.exp ((r : ℝ) * (a-1)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*a)).tsum_eq]
      rw [← Real.exp_eq_exp_ℝ,← Real.exp_add]
      congr 1
      ring

lemma expNegENNReal_bound (u : ℝ≥0∞) : 0 ≤ expNegENNReal u ∧ expNegENNReal u ≤ 1 := by
  have hu : EReal.exp (-(u : EReal)) ≤ 1 :=
    EReal.exp_le_one_iff.mpr (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg u))
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hu)⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_PoissonLaplace
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.countablePoissonIntensity_sfinite _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma expNegENNReal_finite {u : ℝ≥0∞} (hu : u ≠ ⊤) :
    expNegENNReal u = Real.exp (-u.toReal) := by
  unfold expNegENNReal
  rw [← EReal.coe_ennreal_toReal hu,← EReal.coe_neg,EReal.exp_coe,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma poissonLaplace_measurable {S : Type*} [MeasurableSpace S]
    {f : S → ℝ} (hf : Measurable f) : Measurable (poissonLaplace f) :=
  expNegENNReal_continuous.measurable.comp (Measure.measurable_lintegral hf.ennreal_ofReal)

lemma poissonLaplace_bounds {S : Type*} [MeasurableSpace S]
    (f : S → ℝ) (η : Measure S) : 0 ≤ poissonLaplace f η ∧ poissonLaplace f η ≤ 1 :=
  expNegENNReal_bound _

lemma poissonLaplace_finitePointMeasure {S : Type*} [MeasurableSpace S]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (n : ℕ) (x : Fin n → S) :
    poissonLaplace f (finitePointMeasure n x) = ∏ i : Fin n, Real.exp (-f (x i)) := by
  simp only [poissonLaplace,finitePointMeasure,lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac' _ hf.ennreal_ofReal]
  rw [expNegENNReal_finite (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)),ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (hf0 _)]
  rw [← Finset.sum_neg_distrib,Real.exp_sum]

lemma finitePoissonLaw_laplace {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂finitePoissonLaw r ν =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-f x) ∂ν) - 1)) := by
  have hi : Integrable (poissonLaplace f) (finitePoissonLaw r ν) := by
    apply Integrable.of_bound (poissonLaplace_measurable hf).aestronglyMeasurable 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds f η).1]
      exact (poissonLaplace_bounds f η).2
  rw [finitePoissonLaw,integral_sum_measure hi]
  simp_rw [integral_smul_measure]
  have hlocal (n : ℕ) :
      ∫ η, poissonLaplace f η ∂((Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) =
        (∫ x, Real.exp (-f x) ∂ν)^n := by
    rw [integral_map (finitePointMeasure_measurable n).aemeasurable
      (poissonLaplace_measurable hf).aestronglyMeasurable]
    simp_rw [poissonLaplace_finitePointMeasure hf hf0]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (x : S) => Real.exp (-f x))]
    simp
  simp_rw [hlocal,smul_eq_mul]
  have hp := poisson_power_integral r (∫ x, Real.exp (-f x) ∂ν)
  rw [integral_poissonMeasure] at hp
  simpa only [measureReal_def,← poissonMeasure_real_singleton,smul_eq_mul] using hp

lemma expNegENNReal_add (u v : ℝ≥0∞) :
    expNegENNReal (u+v) = expNegENNReal u * expNegENNReal v := by
  by_cases hu : u = ⊤
  · simp [hu]
  by_cases hv : v = ⊤
  · simp [hv]
  rw [expNegENNReal_finite (ENNReal.add_ne_top.mpr ⟨hu,hv⟩),
    expNegENNReal_finite hu,expNegENNReal_finite hv,ENNReal.toReal_add hu hv,
    neg_add,Real.exp_add]

lemma expNegENNReal_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    expNegENNReal (∑ i ∈ s, a i) = ∏ i ∈ s, expNegENNReal (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,expNegENNReal_add,ih]

lemma measureSum_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (fun η : ℕ → Measure S => Measure.sum η) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

lemma poissonLaplace_finsetSum {S : Type*} [MeasurableSpace S]
    (f : S → ℝ) (s : Finset ℕ) (η : ℕ → Measure S) :
    poissonLaplace f (∑ i ∈ s, η i) = ∏ i ∈ s, poissonLaplace f (η i) := by
  simp only [poissonLaplace,lintegral_finsetSum_measure,expNegENNReal_sum]

lemma poissonLaplace_sum_tendsto {S : Type*} [MeasurableSpace S]
    (f : S → ℝ) (η : ℕ → Measure S) :
    Tendsto (fun n => poissonLaplace f (∑ i ∈ Finset.range n, η i)) atTop
      (𝓝 (poissonLaplace f (Measure.sum η))) := by
  simp only [poissonLaplace,lintegral_sum_measure,lintegral_finsetSum_measure]
  exact expNegENNReal_continuous.continuousAt.tendsto.comp
    (ENNReal.summable.hasSum.tendsto_sum_nat)

lemma finitePoissonLaw_laplace_nonneg {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂finitePoissonLaw r ν =
      expNegENNReal (ENNReal.ofReal ((r : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν)) := by
  have hib : Integrable (fun x => Real.exp (-f x)) ν := by
    apply Integrable.of_bound (hf.neg.exp.aestronglyMeasurable) 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x))
  have hn : 0 ≤ (r : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν := by
    apply mul_nonneg r.coe_nonneg
    apply integral_nonneg
    intro x
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x)))
  rw [finitePoissonLaw_laplace r ν hf hf0,expNegENNReal_finite ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hn,integral_sub (integrable_const 1) hib]
  simp only [integral_const,probReal_univ,one_smul]
  congr 1
  ring

lemma countablePoissonLaw_laplace {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂countablePoissonLaw r ν =
      expNegENNReal (∑' i, ENNReal.ofReal ((r i : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν i)) := by
  let Q := Measure.infinitePi fun i => finitePoissonLaw (r i) (ν i)
  let a (i : ℕ) := ENNReal.ofReal ((r i : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν i)
  have hm (n : ℕ) : Measurable (fun η : ℕ → Measure S =>
      poissonLaplace f (∑ i ∈ Finset.range n, η i)) := by
    apply (poissonLaplace_measurable hf).comp
    fun_prop
  have he (n : ℕ) :
      ∫ η, poissonLaplace f (∑ i ∈ Finset.range n, η i) ∂Q =
        expNegENNReal (∑ i ∈ Finset.range n, a i) := by
    simp_rw [poissonLaplace_finsetSum]
    have he' : (fun η : ℕ → Measure S => ∏ i ∈ Finset.range n, poissonLaplace f (η i)) =
        (fun η : ℕ → Measure S => ∏ i : (Finset.range n),
          poissonLaplace f ((Finset.range n).restrict η i)) := by
      funext η
      exact (Finset.prod_coe_sort (Finset.range n) (fun i => poissonLaplace f (η i))).symm
    rw [he']
    rw [integral_restrict_infinitePi (μ := fun i => finitePoissonLaw (r i) (ν i))
      (f := fun η : (i : Finset.range n) → Measure S => ∏ i, poissonLaplace f (η i))
      (by exact (Finset.measurable_prod _ (fun i _ => (poissonLaplace_measurable hf).comp
        (measurable_pi_apply i))).aestronglyMeasurable)]
    rw [integral_fintype_prod_eq_prod (fun (i : Finset.range n) (η : Measure S) =>
      poissonLaplace f η)]
    simp_rw [finitePoissonLaw_laplace_nonneg _ _ hf hf0]
    rw [expNegENNReal_sum]
    exact Finset.prod_coe_sort (Finset.range n) (fun i => expNegENNReal (a i))
  have ht : Tendsto (fun n => ∫ η, poissonLaplace f (∑ i ∈ Finset.range n, η i) ∂Q)
      atTop (𝓝 (∫ η, poissonLaplace f (Measure.sum η) ∂Q)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => (hm n).aestronglyMeasurable) (integrable_const 1)
    · intro n
      exact ae_of_all _ fun η => by
        rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds _ _).1]
        exact (poissonLaplace_bounds _ _).2
    · exact ae_of_all _ (poissonLaplace_sum_tendsto f)
  simp_rw [he] at ht
  have ht' : Tendsto (fun n => expNegENNReal (∑ i ∈ Finset.range n, a i)) atTop
      (𝓝 (expNegENNReal (∑' i, a i))) :=
    expNegENNReal_continuous.continuousAt.tendsto.comp ENNReal.summable.hasSum.tendsto_sum_nat
  rw [countablePoissonLaw, integral_map measureSum_measurable.aemeasurable
    (poissonLaplace_measurable hf).aestronglyMeasurable]
  exact tendsto_nhds_unique ht ht'

lemma measure_eq_of_additive_test_family {X M : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddMonoid M] (g : M → X →ᵇ ℝ)
    (g0 : g 0 = 1) (gadd : ∀ a b, g (a+b) = g a * g b)
    (gsep : ∀ x y : X, x ≠ y → ∃ a, g a x ≠ g a y)
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (heq : ∀ a, ∫ x, g a x ∂P = ∫ x, g a x ∂Q) : P = Q := by
  let K : Submonoid (X →ᵇ ℝ) :=
    { carrier := Set.range g
      one_mem' := ⟨0,g0⟩
      mul_mem' := by
        rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
        exact ⟨a+b,gadd a b⟩ }
  let A : StarSubalgebra ℝ (X →ᵇ ℝ) :=
    { toSubalgebra := Algebra.adjoin ℝ (K : Set (X →ᵇ ℝ))
      star_mem' := fun {f} hf => by
        have hstar : star f = f := by ext x; simp
        rwa [hstar] }
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨a,ha⟩ := gsep x y hxy
    use g a
    simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
      SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
    refine ⟨⟨g a,?_,rfl⟩,ha⟩
    exact Algebra.subset_adjoin (show g a ∈ K from ⟨a,rfl⟩)
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  let V : Submodule ℝ (X →ᵇ ℝ) :=
    { carrier := {f | ∫ x, f x ∂P = ∫ x, f x ∂Q}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change ∫ x, a x + b x ∂P = ∫ x, a x + b x ∂Q
        rw [integral_add (a.integrable P) (b.integrable P),
          integral_add (a.integrable Q) (b.integrable Q),ha,hb]
      smul_mem' := by
        intro c f hf
        change ∫ x, c * f x ∂P = ∫ x, c * f x ∂Q
        rw [integral_const_mul,integral_const_mul,hf] }
  have hspan : Submodule.span ℝ (K : Set (X →ᵇ ℝ)) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact heq a
  apply hspan
  change f ∈ (Algebra.adjoin ℝ (K : Set (X →ᵇ ℝ))).toSubmodule at hf
  rw [Algebra.adjoin_eq_span,Submonoid.closure_eq] at hf
  exact hf

lemma expNegENNReal_injective : Function.Injective expNegENNReal := by
  intro u v huv
  have hfinite (w : ℝ≥0∞) : EReal.exp (-(w : EReal)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (EReal.exp_le_one_iff.mpr
      (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg w))) ENNReal.one_lt_top)
  have he := (ENNReal.toReal_eq_toReal_iff' (hfinite u) (hfinite v)).mp huv
  have hn := EReal.expOrderIso.injective he
  exact EReal.coe_ennreal_injective (by simpa using congrArg Neg.neg hn)

lemma laplaceTest_add {ι : Type*} [Fintype ι] (a b : ι → ℝ≥0) :
    laplaceTest (a+b) = laplaceTest a * laplaceTest b := by
  ext x
  simp only [laplaceTest,BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk,Pi.add_apply,ENNReal.coe_add,add_mul,
    Finset.sum_add_distrib,expNegENNReal_add,BoundedContinuousFunction.mul_apply]

lemma laplaceTest_separates {ι : Type*} [Fintype ι] (x y : ι → ℝ≥0∞) (hxy : x ≠ y) :
    ∃ a : ι → ℝ≥0, laplaceTest a x ≠ laplaceTest a y := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  refine ⟨Pi.single i 1,?_⟩
  simpa [laplaceTest,Pi.single_apply,apply_ite,ite_mul] using expNegENNReal_injective.ne hi

lemma measure_eq_of_laplace_tests {ι : Type*} [Fintype ι]
    (P Q : Measure (ι → ℝ≥0∞)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (heq : ∀ a : ι → ℝ≥0, ∫ x, laplaceTest a x ∂P = ∫ x, laplaceTest a x ∂Q) : P = Q :=
  measure_eq_of_additive_test_family laplaceTest laplaceTest_zero laplaceTest_add
    laplaceTest_separates P Q heq

lemma measure_eq_of_map_eq_comap {X Y : Type*} [mX : MeasurableSpace X]
    [mY : MeasurableSpace Y] (f : X → Y) (h : mX = mY.comap f)
    (P Q : Measure X) (heq : P.map f = Q.map f) : P = Q := by
  have hf : Measurable f := Measurable.of_comap_le h.ge
  ext s hs
  rw [h] at hs
  obtain ⟨t,ht,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  rw [← Measure.map_apply hf ht,← Measure.map_apply hf ht,heq]

lemma measureLaw_eval_comap {S : Type*} [MeasurableSpace S] :
    (inferInstance : MeasurableSpace (Measure S)) = MeasurableSpace.comap
      (fun η : Measure S => fun s : {s : Set S // MeasurableSet s} => η s.val)
      inferInstance := by
  apply le_antisymm
  · change (⨆ (s : Set S) (hs : MeasurableSet s),
      MeasurableSpace.comap (fun η : Measure S => η s) (borel ℝ≥0∞)) ≤ _
    apply iSup₂_le
    intro s hs
    exact MeasurableSpace.comap_le_comap_pi (g := fun t : {s : Set S // MeasurableSet s} =>
      fun η : Measure S => η t.val) ⟨s,hs⟩
  · apply Measurable.comap_le
    apply Measurable.of_eval
    intro s
    exact Measure.measurable_coe s.property

lemma laplaceTest_eval_eq {S ι : Type*} [MeasurableSpace S] [Fintype ι]
    (s : ι → Set S) (hs : ∀ i, MeasurableSet (s i)) (a : ι → ℝ≥0) (η : Measure S) :
    laplaceTest a (fun i => η (s i)) =
      poissonLaplace (fun x => ∑ i, (s i).indicator (fun _ => (a i : ℝ)) x) η := by
  classical
  have h0 (i : ι) (x : S) : 0 ≤ (s i).indicator (fun _ => (a i : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => (a i).coe_nonneg) x
  have he (x : S) : ENNReal.ofReal (∑ i, (s i).indicator (fun _ => (a i : ℝ)) x) =
      ∑ i, (s i).indicator (fun _ => (a i : ℝ≥0∞)) x := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i x)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ s i <;> simp [hx]
  change expNegENNReal (∑ i, (a i : ℝ≥0∞) * η (s i)) = _
  simp only [poissonLaplace,he]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hs i))]
  simp_rw [lintegral_indicator (hs _),setLIntegral_const]

lemma measureLaw_eq_of_laplace {S : Type*} [MeasurableSpace S]
    (P Q : Measure (Measure S)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (heq : ∀ f : S → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      ∫ η, poissonLaplace f η ∂P = ∫ η, poissonLaplace f η ∂Q) : P = Q := by
  classical
  let J := {s : Set S // MeasurableSet s}
  let E (η : Measure S) (s : J) : ℝ≥0∞ := η s.val
  have hE : Measurable E := Measurable.of_eval fun event => Measure.measurable_coe event.property
  apply measure_eq_of_map_eq_comap E measureLaw_eval_comap
  apply IsProjectiveLimit.unique (P := fun I : Finset J => (Q.map E).map I.restrict)
    (hν := fun _ => rfl)
  intro I
  have hI : Measurable (I.restrict (π := fun _ => ℝ≥0∞)) :=
    Measurable.of_eval fun index => measurable_pi_apply index.val
  change (P.map E).map I.restrict = (Q.map E).map I.restrict
  rw [Measure.map_map hI hE,Measure.map_map hI hE]
  apply measure_eq_of_laplace_tests
  intro a
  have hm : Measurable (I.restrict ∘ E) := hI.comp hE
  rw [integral_map hm.aemeasurable (laplaceTest a).continuous.measurable.aestronglyMeasurable,
    integral_map hm.aemeasurable (laplaceTest a).continuous.measurable.aestronglyMeasurable]
  have hid (η : Measure S) : laplaceTest a ((I.restrict ∘ E) η) =
      poissonLaplace (fun x => ∑ i : I, i.val.val.indicator (fun _ => (a i : ℝ)) x) η :=
    laplaceTest_eval_eq (fun i : I => i.val.val) (fun i => i.val.property) a η
  simp_rw [hid]
  apply heq
  · exact Finset.measurable_sum _ fun i _ => measurable_const.indicator i.val.property
  · intro x
    exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => (a i).coe_nonneg) x

lemma countablePoissonLaw_laplace_intensity {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂countablePoissonLaw r ν =
      expNegENNReal (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-f x)) ∂countablePoissonIntensity r ν) := by
  rw [countablePoissonLaw_laplace r ν hf hf0]
  congr 1
  rw [countablePoissonIntensity,lintegral_sum_measure]
  apply tsum_congr
  intro i
  rw [lintegral_smul_measure,ENNReal.ofReal_mul (r i).coe_nonneg,ENNReal.ofReal_coe_nnreal]
  congr 1
  apply ofReal_integral_eq_lintegral_ofReal
  · apply Integrable.of_bound (measurable_const.sub hf.neg.exp).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      have h0 := Real.exp_pos (-f x)
      have h1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x))
      change |1 - Real.exp (-f x)| ≤ 1
      rw [abs_of_nonneg (sub_nonneg.mpr h1)]
      linarith
  · exact ae_of_all _ fun x => sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x)))

lemma finiteIntensityMarks_smul {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ] :
    ((κ univ).toNNReal : ℝ≥0∞) • finiteIntensityMarks κ = κ := by
  rw [ENNReal.coe_toNNReal (measure_ne_top _ _)]
  by_cases hκ : κ univ = 0
  · have he : κ = 0 := Measure.measure_univ_eq_zero.mp hκ
    simp [he]
  · rw [finiteIntensityMarks,ite_eq_right hκ,smul_smul,ENNReal.mul_inv_cancel hκ (measure_ne_top _ _),one_smul]

lemma poissonRandomMeasureLaw_laplace {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂poissonRandomMeasureLaw κ =
      expNegENNReal (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-f x)) ∂κ) := by
  rw [poissonRandomMeasureLaw,countablePoissonLaw_laplace_intensity _ _ hf hf0]
  congr 2
  simp only [countablePoissonIntensity,finiteIntensityMarks_smul,sum_sfiniteSeq]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLogIntensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.countablePoissonIntensity_sfinite _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma poissonLaplace_map {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {g : S → T} (hg : Measurable g) {f : T → ℝ} (hf : Measurable f) (η : Measure S) :
    poissonLaplace f (η.map g) = poissonLaplace (f ∘ g) η := by
  rw [poissonLaplace,lintegral_map hf.ennreal_ofReal hg]
  rfl

lemma poissonRandomMeasureLaw_map {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [Nonempty S] [Nonempty T] (κ : Measure S) [SFinite κ]
    {g : S → T} (hg : Measurable g) :
    (poissonRandomMeasureLaw κ).map (Measure.map g) = poissonRandomMeasureLaw (κ.map g) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [integral_map (Measure.measurable_map g hg).aemeasurable
    (poissonLaplace_measurable hf).aestronglyMeasurable]
  simp_rw [poissonLaplace_map hg hf]
  rw [poissonRandomMeasureLaw_laplace _ (hf.comp hg) (fun x => hf0 (g x)),
    poissonRandomMeasureLaw_laplace _ hf hf0,
    lintegral_map (show Measurable (fun x : T => ENNReal.ofReal (1 - Real.exp (-f x))) from
      (measurable_const.sub hf.neg.exp).ennreal_ofReal) hg]
  rfl

lemma stableLogDensity_translate {b : ℝ} (_hb : 0 ≤ b) (c x : ℝ) :
    ENNReal.ofReal (b * Real.exp (-b*x)) =
      ENNReal.ofReal (Real.exp (b*c)) * ENNReal.ofReal (b * Real.exp (-b*(x+c))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_left_comm,← Real.exp_add]
  congr 2
  ring

lemma stableLogIntensity_lintegral_translate {b : ℝ} (hb : 0 ≤ b)
    (c : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (x+c) ∂stableLogIntensity b =
      ENNReal.ofReal (Real.exp (b*c)) * ∫⁻ x, f x ∂stableLogIntensity b := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) (show Measurable (fun x : ℝ => f (x+c)) from hf.comp (measurable_id.add_const c)),
    lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hf]
  change (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * f (x+c)) = _
  calc
    (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * f (x+c)) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (b*c)) *
          (ENNReal.ofReal (b * Real.exp (-b*(x+c))) * f (x+c)) := by
      apply lintegral_congr
      intro x
      rw [stableLogDensity_translate hb c x,mul_assoc]
    _ = ENNReal.ofReal (Real.exp (b*c)) *
        ∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*(x+c))) * f (x+c) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      exact lintegral_add_right_eq_self
        (fun x => ENNReal.ofReal (b * Real.exp (-b*x)) * f x) c

lemma stableLogIntensity_translate {b : ℝ} (hb : 0 ≤ b) (c : ℝ) :
    (stableLogIntensity b).map (fun x => x+c) =
      ENNReal.ofReal (Real.exp (b*c)) • stableLogIntensity b := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (show Measurable (fun x : ℝ => x+c) from measurable_id.add_const c),lintegral_smul_measure]
  exact stableLogIntensity_lintegral_translate hb c hf

lemma logMarkShift_measurable {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (hF : Measurable F) : Measurable (logMarkShift F) :=
  (measurable_fst.add (hF.comp measurable_snd)).prodMk measurable_snd

lemma stableLogIntensity_mark_shift {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F) :
    ((stableLogIntensity b).prod ν).map (logMarkShift F) =
      (stableLogIntensity b).prod (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b * F s)))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (logMarkShift_measurable hF)]
  rw [lintegral_prod_symm (fun p : ℝ × S => f (logMarkShift F p))
    (show AEMeasurable (fun p : ℝ × S => f (logMarkShift F p)) _ from
      (hf.comp (logMarkShift_measurable hF)).aemeasurable),
    lintegral_prod_symm _ hf.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul ν (by fun_prop)
    (Measurable.lintegral_prod_left' hf)]
  apply lintegral_congr
  intro s
  exact stableLogIntensity_lintegral_translate hb (F s) (hf.comp (measurable_id.prodMk measurable_const))

lemma poissonMeasure_atom_succ (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n+1} * (n+1 : ℝ≥0∞) = (r : ℝ≥0∞) * poissonMeasure r {n} := by
  have he : Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial * (n+1 : ℝ) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  have he' := congrArg ENNReal.ofReal he
  have hcast : ENNReal.ofReal ((n : ℝ)+1) = (n : ℝ≥0∞)+1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_one]
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial),
    ENNReal.ofReal_mul r.coe_nonneg,ENNReal.ofReal_coe_nnreal,hcast,poissonMeasure_singleton] using he'

lemma poissonMeasure_mean (r : ℝ≥0) :
    ∑' n : ℕ, poissonMeasure r {n} * (n : ℝ≥0∞) = r := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero,mul_zero,zero_add,Nat.cast_add,Nat.cast_one]
  simp_rw [poissonMeasure_atom_succ]
  rw [ENNReal.tsum_mul_left]
  have hmass : ∑' n : ℕ, poissonMeasure r {n} = 1 := by
    simp_rw [poissonMeasure_singleton]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      (hasSum_one_poissonMeasure r).summable,(hasSum_one_poissonMeasure r).tsum_eq]
    norm_num
  rw [hmass,mul_one]

lemma finitePointMeasure_lintegral {S : Type*} [MeasurableSpace S]
    {f : S → ℝ≥0∞} (hf : Measurable f) (n : ℕ) (x : Fin n → S) :
    ∫⁻ a, f a ∂finitePointMeasure n x = ∑ i, f (x i) := by
  simp only [finitePointMeasure,lintegral_finsetSum_measure,lintegral_dirac' _ hf]

lemma finitePoissonLaw_campbell {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ η, ∫⁻ x, f x ∂η ∂finitePoissonLaw r ν = (r : ℝ≥0∞) * ∫⁻ x, f x ∂ν := by
  have hm := Measure.measurable_lintegral hf
  rw [finitePoissonLaw,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure,lintegral_map hm (finitePointMeasure_measurable _),
    finitePointMeasure_lintegral hf]
  have he (n : ℕ) : (∫⁻ x : Fin n → S, ∑ i, f (x i) ∂Measure.pi (fun _ => ν)) =
      (n : ℝ≥0∞) * ∫⁻ y, f y ∂ν := by
    rw [lintegral_finsetSum (f := fun (i : Fin n) (x : Fin n → S) => f (x i)) _
      (fun i _ => hf.comp (measurable_pi_apply i))]
    simp_rw [(measurePreserving_eval (fun _ : Fin n => ν) _).lintegral_comp hf]
    simp
  simp_rw [he,smul_eq_mul,← mul_assoc]
  rw [ENNReal.tsum_mul_right,poissonMeasure_mean]

lemma countablePoissonLaw_campbell {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ η, ∫⁻ x, f x ∂η ∂countablePoissonLaw r ν =
      ∫⁻ x, f x ∂countablePoissonIntensity r ν := by
  rw [countablePoissonLaw,lintegral_map (Measure.measurable_lintegral hf) measureSum_measurable]
  simp only [lintegral_sum_measure]
  rw [lintegral_tsum (f := fun (i : ℕ) (η : ℕ → Measure S) => ∫⁻ x, f x ∂η i)
    (fun i => ((Measure.measurable_lintegral hf).comp (measurable_pi_apply i)).aemeasurable)]
  simp_rw [(measurePreserving_eval_infinitePi (fun i => finitePoissonLaw (r i) (ν i)) _).lintegral_comp
    (Measure.measurable_lintegral hf),finitePoissonLaw_campbell _ _ hf]
  simp only [countablePoissonIntensity,lintegral_sum_measure,lintegral_smul_measure,smul_eq_mul]

lemma poissonRandomMeasureLaw_campbell {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ η, ∫⁻ x, f x ∂η ∂poissonRandomMeasureLaw κ = ∫⁻ x, f x ∂κ := by
  rw [poissonRandomMeasureLaw,countablePoissonLaw_campbell _ _ hf]
  simp only [countablePoissonIntensity,finiteIntensityMarks_smul,sum_sfiniteSeq]

lemma ae_ne_top_of_laplace_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : Measurable Z)
    (hlim : Tendsto (fun n : ℕ => ∫ ω,
      expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω) ∂P) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P, Z ω ≠ ⊤ := by
  let L : Ω → ℝ := fun ω => if Z ω = ⊤ then 0 else 1
  have hLm : Measurable L := measurable_const.ite (measurableSet_eq_fun hZ measurable_const) measurable_const
  have hLb (ω : Ω) : 0 ≤ L ω ∧ L ω ≤ 1 := by unfold L; split_ifs <;> norm_num
  have hLi : Integrable L P := Integrable.of_bound hLm.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hLb ω).1]; exact (hLb ω).2)
  have hconv (ω : Ω) : Tendsto (fun n : ℕ =>
      expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω)) atTop (𝓝 (L ω)) := by
    by_cases hz : Z ω = ⊤
    · have he (n : ℕ) : expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω) = 0 := by
        rw [hz,ENNReal.mul_top (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))),expNegENNReal_top]
      simpa only [he,L,ite_eq_left hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have he (n : ℕ) : expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω) =
          Real.exp (-(1 / ((n : ℝ)+1) * (Z ω).toReal)) := by
        rw [expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hz),
          ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
      simp_rw [he]
      simpa [L,hz,Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (Z ω).toReal).neg
  have hconv' := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun n ω => expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω))
    (fun _ : Ω => (1 : ℝ))
    (fun n => (expNegENNReal_continuous.measurable.comp
      (measurable_const.mul hZ)).aestronglyMeasurable) (integrable_const 1)
    (fun _ => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (expNegENNReal_bound _).1]
      exact (expNegENNReal_bound _).2) (ae_of_all _ hconv)
  have he : ∫ ω, L ω ∂P = 1 := (tendsto_nhds_unique hlim hconv').symm
  have hzero : ∫ ω, 1 - L ω ∂P = 0 := by rw [integral_sub (integrable_const 1) hLi,he]; simp
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun ω => sub_nonneg.mpr (hLb ω).2) ((integrable_const 1).sub hLi)).mp hzero
  filter_upwards [hae] with ω hω
  intro hz
  simp [L,hz] at hω

lemma poissonRandomMeasureLaw_lintegral_ne_top {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfin : ∫⁻ x, ENNReal.ofReal (min (f x) 1) ∂κ ≠ ⊤) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, (∫⁻ x, ENNReal.ofReal (f x) ∂η) ≠ ⊤ := by
  apply ae_ne_top_of_laplace_tendsto _ (Measure.measurable_lintegral hf.ennreal_ofReal)
  have hf' (n : ℕ) : Measurable (fun x => 1 / ((n : ℝ)+1) * f x) := measurable_const.mul hf
  have hb (n : ℕ) (x : S) : 1 - Real.exp (-(1 / ((n : ℝ)+1) * f x)) ≤ min (f x) 1 := by
    apply le_min
    · have he := Real.add_one_le_exp (-(1 / ((n : ℝ)+1) * f x))
      have hc : 1 / ((n : ℝ)+1) ≤ 1 := by apply (div_le_iff₀ (by positivity)).mpr; simp
      nlinarith [mul_le_of_le_one_left (hf0 x) hc]
    · linarith [Real.exp_pos (-(1 / ((n : ℝ)+1) * f x))]
  have hl := tendsto_lintegral_of_dominated_convergence (μ := κ)
    (F := fun n x => ENNReal.ofReal (1 - Real.exp (-(1 / ((n : ℝ)+1) * f x))))
    (fun x => ENNReal.ofReal (min (f x) 1))
    (fun n => (measurable_const.sub (hf' n).neg.exp).ennreal_ofReal)
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (hb n x)) hfin
    (f := fun _ => 0) (ae_of_all _ fun x => by
      simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (Real.continuous_exp.continuousAt.tendsto.comp
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (f x)).neg)))
  have he (n : ℕ) : (∫ η, expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) *
        ∫⁻ x, ENNReal.ofReal (f x) ∂η) ∂poissonRandomMeasureLaw κ) =
      expNegENNReal (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-(1 / ((n : ℝ)+1) * f x))) ∂κ) := by
    convert poissonRandomMeasureLaw_laplace κ (hf' n) (fun x => mul_nonneg (by positivity) (hf0 x)) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext η
    unfold poissonLaplace
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (by positivity)]
  simp_rw [he]
  simpa only [lintegral_zero,expNegENNReal_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤),
    ENNReal.toReal_zero,neg_zero,Real.exp_zero,Function.comp_def] using
    expNegENNReal_continuous.continuousAt.tendsto.comp hl

lemma stableLogIntensity_min_exp_finite {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∫⁻ x, ENNReal.ofReal (min (Real.exp x) 1) ∂stableLogIntensity b) ≠ ⊤ := by
  have hi : Integrable (fun x : ℝ => b * Real.exp (-b*x) * min (Real.exp x) 1) := by
    have hh := (((integrableOn_exp_mul_Iic (a := 1-b) (by linarith) 0).integrable_indicator
      measurableSet_Iic).add ((integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0).integrable_indicator
      measurableSet_Ioi)).const_mul b
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases hx : x ≤ 0
    · simp only [Pi.add_apply]
      rw [indicator_of_mem (show x ∈ Iic 0 from hx),
        indicator_of_notMem (show x ∉ Ioi 0 from not_lt.mpr hx),add_zero,
        min_eq_left (Real.exp_le_one_iff.mpr hx)]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · have hx' : 0 < x := lt_of_not_ge hx
      simp only [Pi.add_apply]
      rw [indicator_of_notMem (show x ∉ Iic 0 from hx),
        indicator_of_mem (show x ∈ Ioi 0 from hx'),zero_add,
        min_eq_right (Real.one_le_exp_iff.mpr hx'.le),mul_one]
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) (by fun_prop)]
  have he : (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * ENNReal.ofReal (min (Real.exp x) 1)) =
      ∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x) * min (Real.exp x) 1) := by
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_mul (mul_nonneg hb0.le (Real.exp_pos _).le)).symm
  change (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * ENNReal.ofReal (min (Real.exp x) 1)) ≠ ⊤
  rw [he]
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)).mp hi.hasFiniteIntegral).ne

lemma stablePoisson_total_finite {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b),
      (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) ≠ ⊤ :=
  poissonRandomMeasureLaw_lintegral_ne_top _ Real.measurable_exp (fun x => (Real.exp_pos x).le)
    (stableLogIntensity_min_exp_finite hb0 hb1)

lemma stableLogIntensity_univ {b : ℝ} (hb : 0 < b) : stableLogIntensity b univ = ⊤ := by
  have ha : (volume : Measure ℝ) ≪ stableLogIntensity b :=
    withDensity_absolutelyContinuous' (by fun_prop)
      (ae_of_all _ fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hb (Real.exp_pos _))))
  have hne : stableLogIntensity b univ ≠ 0 := by
    intro h
    have hh := ha h
    simp at hh
  by_contra ht
  have hs := congrArg (fun κ : Measure ℝ => κ univ) (stableLogIntensity_translate hb.le 1)
  rw [Measure.map_apply (show Measurable (fun x : ℝ => x+1) from measurable_id.add_const 1)
    .univ,preimage_univ,Measure.smul_apply,smul_eq_mul] at hs
  have hr := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,mul_one] at hr
  have hp := ENNReal.toReal_pos hne ht
  have he : 1 < Real.exp b := Real.one_lt_exp_iff.mpr hb
  nlinarith

lemma poissonRandomMeasureLaw_lintegral_pos_of_infinite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] (hκ : κ univ = ⊤)
    {f : S → ℝ} (hf : Measurable f) (hfpos : ∀ x, 0 < f x) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, 0 < ∫⁻ x, ENNReal.ofReal (f x) ∂η := by
  have hconst : Measurable (fun _ : S => (1 : ℝ)) := measurable_const
  have he := poissonRandomMeasureLaw_laplace κ hconst (fun _ => zero_le_one)
  have hc : ENNReal.ofReal (1 - Real.exp (-1)) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [lintegral_const,hκ,ENNReal.mul_top hc,expNegENNReal_top] at he
  have hi : Integrable (poissonLaplace (fun _ : S => (1 : ℝ))) (poissonRandomMeasureLaw κ) := by
    apply Integrable.of_bound (poissonLaplace_measurable hconst).aestronglyMeasurable 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds _ η).1]
      exact (poissonLaplace_bounds _ η).2
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun η => (poissonLaplace_bounds (fun _ : S => (1 : ℝ)) η).1) hi).mp he
  filter_upwards [hae] with η hη
  have hsp : Function.support (fun x => ENNReal.ofReal (f x)) = univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hfpos x))
  rw [lintegral_pos_iff_support hf.ennreal_ofReal,hsp]
  by_contra hn
  have hz : η univ = 0 := bot_unique (le_of_not_gt hn)
  simp only [poissonLaplace,lintegral_const,ENNReal.ofReal_one,one_mul,hz,
    expNegENNReal_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤),ENNReal.toReal_zero,neg_zero,Real.exp_zero] at hη
  exact one_ne_zero hη

lemma stablePoisson_total_positive {b : ℝ} (hb : 0 < b) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b),
      0 < ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η :=
  poissonRandomMeasureLaw_lintegral_pos_of_infinite _ (stableLogIntensity_univ hb)
    Real.measurable_exp Real.exp_pos

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma one_sub_exp_neg_le_min {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 1-Real.exp (-u) ∧ 1-Real.exp (-u) ≤ min u 1 := by
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu))
  · exact le_min (by linarith [Real.add_one_le_exp (-u)]) (by linarith [Real.exp_pos (-u)])

lemma stableLaplaceConstant_finite {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b ≠ ⊤ := by
  apply ne_top_of_le_ne_top (stableLogIntensity_min_exp_finite hb0 hb1)
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (one_sub_exp_neg_le_min (Real.exp_pos x).le).2

lemma stableLaplaceConstant_positive {b : ℝ} (hb : 0 < b) :
    0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant
  rw [lintegral_pos_iff_support (by fun_prop)]
  have he : Function.support (fun x : ℝ => ENNReal.ofReal (1-Real.exp (-Real.exp x))) = univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by
      have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos x))
      linarith))
  rw [he,stableLogIntensity_univ hb]
  simp

lemma stableLaplaceExponent_scaling {b t : ℝ} (hb : 0 ≤ b) (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-(t*Real.exp x))) ∂stableLogIntensity b) =
      ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  have he := stableLogIntensity_lintegral_translate hb (Real.log t)
    (f := fun x => ENNReal.ofReal (1-Real.exp (-Real.exp x))) (by fun_prop)
  have hx (x : ℝ) : Real.exp (x+Real.log t) = t*Real.exp x := by
    rw [Real.exp_add,Real.exp_log ht]
    exact mul_comm _ _
  simp_rw [hx] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.rpow_def_of_pos ht,mul_comm b (Real.log t)]
  rfl

lemma stablePoissonTotal_pos {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b), 0 < stablePoissonTotal η := by
  filter_upwards [stablePoisson_total_positive hb0,stablePoisson_total_finite hb0 hb1] with η hp hf
  exact ENNReal.toReal_pos hp.ne' hf

lemma stablePoissonTotal_laplace {b t : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫ η, Real.exp (-t*stablePoissonTotal η) ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      Real.exp (-(stableLaplaceConstant b).toReal * t^b) := by
  have he := poissonRandomMeasureLaw_laplace (stableLogIntensity b)
    (f := fun x => t*Real.exp x) (by fun_prop) (fun x => mul_nonneg ht.le (Real.exp_pos x).le)
  rw [stableLaplaceExponent_scaling hb0.le ht,
    expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (stableLaplaceConstant_finite hb0 hb1)),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht b).le] at he
  convert he using 1
  · apply integral_congr_ae
    filter_upwards [stablePoisson_total_finite hb0 hb1] with η hη
    simp only [poissonLaplace,ENNReal.ofReal_mul ht.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hη),
      ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le]
    congr 1
    dsimp [stablePoissonTotal]
    ring
  · congr 1
    ring

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_integrable {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    Integrable (fun x => Real.exp (t * v x) * F x) μ := by
  refine Integrable.of_bound (hv.const_mul t |>.exp.mul hF).aestronglyMeasurable
    (Real.exp (|t| * C) * D) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hFD x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * v x)).trans (by rw [abs_mul]; gcongr; exact hvC x)

lemma tilt_partition_pos {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    0 < tiltPartition μ v t := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC (by norm_num : (0:ℝ) ≤ 1)
      hvC (fun _ => by norm_num) t
  have he : Real.exp (- |t| * C) ≤ tiltPartition μ v t := by
    calc
      Real.exp (- |t| * C) = ∫ _ : S, Real.exp (- |t| * C) ∂μ := by simp
      _ ≤ tiltPartition μ v t := integral_mono_ae (integrable_const _) hi (ae_of_all _ fun x => by
        apply Real.exp_le_exp.mpr
        have hh : |t*v x| ≤ |t| * C := by rw [abs_mul]; gcongr; exact hvC x
        nlinarith [neg_abs_le (t*v x)])
  exact (Real.exp_pos _).trans_le he

end Tilt

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_partition {v : S → ℝ} (_hv : Measurable v) (n : ℕ) (t : ℝ) :
    tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      (tiltPartition μ v t)^n := by
  unfold tiltPartition replicaPotential
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x))]
  simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma ennreal_rpow_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) : (∑ i ∈ s, f i)^a ≤ ∑ i ∈ s, (f i)^a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ha]
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1).trans (add_le_add le_rfl ih)

lemma ennreal_rpow_tsum_le (f : ℕ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑' i, f i)^a ≤ ∑' i, (f i)^a := by
  apply le_of_tendsto_of_tendsto
    ((ENNReal.continuous_rpow_const).continuousAt.tendsto.comp
      (ENNReal.summable.hasSum.tendsto_sum_nat (f := f)))
    (ENNReal.summable.hasSum.tendsto_sum_nat (f := fun i => (f i)^a))
  exact Filter.Eventually.of_forall fun n => ennreal_rpow_sum_le _ _ ha ha1

lemma finitePoissonLaw_rpow_lintegral_le {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) {f : S → ℝ≥0∞} (hf : Measurable f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᵐ η ∂finitePoissonLaw r ν, (∫⁻ x, f x ∂η)^a ≤ ∫⁻ x, (f x)^a ∂η := by
  rw [finitePoissonLaw,Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [ae_map_iff (finitePointMeasure_measurable n).aemeasurable
    (measurableSet_le ((Measure.measurable_lintegral hf).pow_const a)
      (Measure.measurable_lintegral (hf.pow_const a)))]
  apply ae_of_all
  intro y
  simp only [finitePointMeasure,lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac' _ hf,lintegral_dirac' _ (hf.pow_const a)]
  exact ennreal_rpow_sum_le _ _ ha ha1

lemma countablePoissonLaw_rpow_lintegral_le {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ≥0∞} (hf : Measurable f) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᵐ η ∂countablePoissonLaw r ν, (∫⁻ x, f x ∂η)^a ≤ ∫⁻ x, (f x)^a ∂η := by
  rw [countablePoissonLaw,ae_map_iff measureSum_measurable.aemeasurable
    (measurableSet_le ((Measure.measurable_lintegral hf).pow_const a)
      (Measure.measurable_lintegral (hf.pow_const a)))]
  have hi (i : ℕ) : ∀ᵐ η ∂Measure.infinitePi (fun j => finitePoissonLaw (r j) (ν j)),
      (∫⁻ x, f x ∂η i)^a ≤ ∫⁻ x, (f x)^a ∂η i :=
    (measurePreserving_eval_infinitePi (fun j => finitePoissonLaw (r j) (ν j)) i).quasiMeasurePreserving.ae
      (finitePoissonLaw_rpow_lintegral_le (r i) (ν i) hf ha ha1)
  filter_upwards [ae_all_iff.mpr hi] with η hη
  simp only [lintegral_sum_measure]
  exact (ennreal_rpow_tsum_le _ ha ha1).trans (ENNReal.tsum_le_tsum hη)

lemma poissonRandomMeasureLaw_rpow_lintegral_le {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ≥0∞} (hf : Measurable f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, (∫⁻ x, f x ∂η)^a ≤ ∫⁻ x, (f x)^a ∂η :=
  countablePoissonLaw_rpow_lintegral_le _ _ hf ha ha1

lemma ennreal_rpow_le_one_add {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ≥0∞) :
    u^a ≤ 1+u := by
  by_cases h : u ≤ 1
  · exact (ENNReal.rpow_le_one h ha0).trans (le_add_right le_rfl)
  · have hu : u^a ≤ u := by simpa using ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge h) ha1
    exact hu.trans (le_add_left le_rfl)

lemma poissonRandomMeasureLaw_fractional_moment {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f g : S → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hfin : ∫⁻ x, f x ∂κ ≠ ⊤) (hgin : ∫⁻ x, (g x)^a ∂κ ≠ ⊤) :
    (∫⁻ η, (∫⁻ x, f x+g x ∂η)^a ∂poissonRandomMeasureLaw κ) ≠ ⊤ := by
  have hbound : ∀ᵐ η ∂poissonRandomMeasureLaw κ,
      (∫⁻ x, f x+g x ∂η)^a ≤ 1+(∫⁻ x, f x ∂η)+(∫⁻ x, (g x)^a ∂η) := by
    filter_upwards [poissonRandomMeasureLaw_rpow_lintegral_le κ hg ha ha1] with η hη
    rw [lintegral_add_left hf]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1).trans
      (add_le_add (ennreal_rpow_le_one_add ha.le ha1 _) hη)
  apply ne_top_of_le_ne_top _ (lintegral_mono_ae hbound)
  rw [lintegral_add_left (f := fun η => 1+(∫⁻ x, f x ∂η)) (measurable_const.add (Measure.measurable_lintegral hf)),
    lintegral_add_left (f := fun _ => (1 : ℝ≥0∞)) measurable_const,lintegral_const,measure_univ,one_mul,
    poissonRandomMeasureLaw_campbell κ hf,poissonRandomMeasureLaw_campbell κ (hg.pow_const a)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨by simp,hfin⟩,hgin⟩

lemma stableLogIntensity_of_integrable {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => b * Real.exp (-b*x) * f x)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂stableLogIntensity b) ≠ ⊤ := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hf.ennreal_ofReal]
  have he (x : ℝ) : ENNReal.ofReal (b * Real.exp (-b*x)) * ENNReal.ofReal (f x) =
      ENNReal.ofReal (b * Real.exp (-b*x) * f x) :=
    (ENNReal.ofReal_mul (mul_nonneg hb (Real.exp_pos _).le)).symm
  simp only [Pi.mul_apply]
  simp_rw [he]
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x =>
    mul_nonneg (mul_nonneg hb (Real.exp_pos _).le) (hf0 x))).mp hi.hasFiniteIntegral).ne

lemma stableLogIntensity_small_moment {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∫⁻ x, (Iic 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x
      ∂stableLogIntensity b) ≠ ⊤ := by
  have hi := ((integrableOn_exp_mul_Iic (a := 1-b) (by linarith) 0).integrable_indicator
    measurableSet_Iic).const_mul b
  have he (x : ℝ) : b*Real.exp (-b*x) * (Iic 0).indicator Real.exp x =
      b * (Iic 0).indicator (fun y => Real.exp ((1-b)*y)) x := by
    by_cases hx : x ∈ Iic 0
    · simp only [indicator_of_mem hx]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · simp [indicator_of_notMem hx]
  have hh := stableLogIntensity_of_integrable (f := (Iic (0 : ℝ)).indicator Real.exp) hb0.le (Real.measurable_exp.indicator measurableSet_Iic)
    (fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x) (by simpa only [he] using hi)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  by_cases hx : x ∈ Iic 0 <;> simp [hx]

lemma stableLogIntensity_large_moment {b a : ℝ} (hb : 0 ≤ b) (hab : a < b) :
    (∫⁻ x, (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp (a*y))) x
      ∂stableLogIntensity b) ≠ ⊤ := by
  have hi := ((integrableOn_exp_mul_Ioi (a := a-b) (by linarith) 0).integrable_indicator
    measurableSet_Ioi).const_mul b
  have he (x : ℝ) : b*Real.exp (-b*x) * (Ioi 0).indicator (fun y => Real.exp (a*y)) x =
      b * (Ioi 0).indicator (fun y => Real.exp ((a-b)*y)) x := by
    by_cases hx : x ∈ Ioi 0
    · simp only [indicator_of_mem hx]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · simp [indicator_of_notMem hx]
  have hh := stableLogIntensity_of_integrable (f := (Ioi (0 : ℝ)).indicator (fun y => Real.exp (a*y))) hb ((measurable_const.mul measurable_id).exp.indicator measurableSet_Ioi)
    (fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x) (by simpa only [he] using hi)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  by_cases hx : x ∈ Ioi 0 <;> simp [hx]

lemma stablePoissonTotal_fractional_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (ha0 : 0 ≤ a) (hab : a < b) :
    Integrable (fun η => (stablePoissonTotal η)^a) (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  rcases ha0.eq_or_lt with h | ha
  · rw [← h]
    simp only [Real.rpow_zero]
    exact integrable_const 1
  have hh := poissonRandomMeasureLaw_fractional_moment (stableLogIntensity b)
    (f := (Iic (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp y)))
    (g := (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp y)))
    ((Real.measurable_exp.ennreal_ofReal).indicator measurableSet_Iic)
    ((Real.measurable_exp.ennreal_ofReal).indicator measurableSet_Ioi)
    ha (hab.trans hb1).le (stableLogIntensity_small_moment hb0 hb1)
  have he (x : ℝ) : ((Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x)^a =
      (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp (a*y))) x := by
    by_cases hx : x ∈ Ioi 0
    · simp only [indicator_of_mem hx]
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,mul_comm x a]
    · simp [indicator_of_notMem hx,ha]
  simp_rw [he] at hh
  specialize hh (stableLogIntensity_large_moment hb0.le hab)
  have he' (x : ℝ) : (Iic 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x +
      (Ioi 0).indicator (fun y => ENNReal.ofReal (Real.exp y)) x = ENNReal.ofReal (Real.exp x) := by
    by_cases hx : x ≤ 0 <;> simp [hx,not_lt.mpr,lt_of_not_ge]
  simp_rw [he'] at hh
  apply Integrable.mono' (integrable_toReal_of_lintegral_ne_top
      ((Measure.measurable_lintegral Real.measurable_exp.ennreal_ofReal).pow_const a).aemeasurable hh)
    ((stablePoissonTotal_measurable.pow_const a).aestronglyMeasurable)
  exact ae_of_all _ fun η => by
    simp only [stablePoissonTotal,Real.norm_eq_abs,ENNReal.toReal_rpow]
    rw [abs_of_nonneg ENNReal.toReal_nonneg]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TiltReplicaCoordinate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma gamma_lintegral_positive_scale {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^(a-1) * Real.exp (-t*r))) =
      ENNReal.ofReal (r^(-a) * Real.Gamma a) := by
  have hi : IntegrableOn (fun t : ℝ => t^(a-1) * Real.exp (-t*r)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a-1)
      (b := r) (by linarith) (by norm_num) hr using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simp only [Real.rpow_one]
    congr 2
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  congr 1
  calc
    (∫ t : ℝ in Ioi 0, t^(a-1)*Real.exp (-t*r)) =
      ∫ t : ℝ in Ioi 0, t^(a-1)*Real.exp (-(r*t)) := by
        congr 1; funext t; congr 2; ring
    _ = (1/r)^a * Real.Gamma a := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
    _ = r^(-a) * Real.Gamma a := by
      rw [one_div,Real.inv_rpow hr.le,Real.rpow_neg hr.le]

lemma integrable_rpow_neg_of_laplace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {S : Ω → ℝ}
    (hS : Measurable S) (hpos : ∀ᵐ ω ∂P, 0 < S ω)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hLap : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t*S ω) ∂P) = Real.exp (-c*t^b))
    {a : ℝ} (ha : 0 < a) : Integrable (fun ω => S ω ^ (-a)) P := by
  let K := fun (ω : Ω) (t : ℝ) => ENNReal.ofReal (t^(a-1)*Real.exp (-t*S ω))
  have hm : Measurable (Function.uncurry K) := by dsimp [K]; fun_prop
  have hexp (t : ℝ) (ht : 0 < t) : Integrable (fun ω => Real.exp (-t*S ω)) P := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hpos] with ω hω
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hinner (t : ℝ) (ht : 0 < t) :
      (∫⁻ ω, K ω t ∂P) = ENNReal.ofReal (t^(a-1)*Real.exp (-c*t^b)) := by
    dsimp [K]
    simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (hexp t ht) (ae_of_all _ fun _ => (Real.exp_pos _).le),
      hLap t ht]
  have hi : (∫⁻ t : ℝ in Ioi 0, ∫⁻ ω, K ω t ∂P) ≠ ⊤ := by
    have hfinite := (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := a-1) (p := b) (b := c) (by linarith) hb hc).hasFiniteIntegral
    have hfinite' : (∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (t^(a-1)*Real.exp (-c*t^b))) < ⊤ := by
      apply (hasFiniteIntegral_iff_ofReal _).mp hfinite
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    apply ne_top_of_le_ne_top hfinite'.ne
    apply le_of_eq
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hinner t ht
  have hi' : (∫⁻ ω, ENNReal.ofReal (S ω^(-a)*Real.Gamma a) ∂P) ≠ ⊤ := by
    rw [← lintegral_congr_ae (hpos.mono fun ω hω => gamma_lintegral_positive_scale ha hω)]
    change (∫⁻ ω, (∫⁻ t : ℝ in Ioi 0, K ω t) ∂P) ≠ ⊤
    rw [lintegral_lintegral_swap hm.aemeasurable]
    exact hi
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ S ω^(-a)*Real.Gamma a :=
    hpos.mono fun ω hω => mul_nonneg (Real.rpow_nonneg hω.le _) (Real.Gamma_pos_of_pos ha).le
  have hprod : Integrable (fun ω => S ω^(-a)*Real.Gamma a) P :=
    ⟨(hS.pow_const (-a) |>.mul_const (Real.Gamma a)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnonneg).mpr hi'.lt_top⟩
  have hh := hprod.div_const (Real.Gamma a)
  simpa only [mul_div_assoc, div_self (Real.Gamma_pos_of_pos ha).ne', mul_one] using hh

lemma stablePoissonTotal_negative_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (ha : 0 < a) : Integrable (fun η => stablePoissonTotal η ^ (-a))
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  exact integrable_rpow_neg_of_laplace _ stablePoissonTotal_measurable
    (stablePoissonTotal_pos hb0 hb1) hb0
    (ENNReal.toReal_pos (stableLaplaceConstant_positive hb0).ne' (stableLaplaceConstant_finite hb0 hb1))
    (fun _ ht => stablePoissonTotal_laplace hb0 hb1 ht) ha

lemma poissonRandomMeasureLaw_ae_null {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {E : Set S} (hE : MeasurableSet E) (hκ : κ E = 0) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, η E = 0 := by
  have he : (∫⁻ η, η E ∂poissonRandomMeasureLaw κ) = 0 := by
    rw [← hκ]
    simpa only [lintegral_indicator hE,lintegral_one,Measure.restrict_apply_univ]
      using poissonRandomMeasureLaw_campbell κ (measurable_const.indicator hE :
        Measurable (E.indicator (fun _ : S => (1 : ℝ≥0∞))))
  exact (lintegral_eq_zero_iff (Measure.measurable_coe hE)).mp he

lemma stablePoissonTotal_rpow_integrable {b a : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hab : a < b) : Integrable (fun η => stablePoissonTotal η ^ a)
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  by_cases ha : 0 ≤ a
  · exact stablePoissonTotal_fractional_integrable hb0 hb1 ha hab
  · have ha' : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
    simpa only [neg_neg] using stablePoissonTotal_negative_integrable hb0 hb1 ha'

lemma log_sq_le_two_rpow {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    (Real.log x)^2 ≤ (x^(2*ε)+x^(-(2*ε)))/ε^2 := by
  have hpow : (x^ε/ε)^2 = x^(2*ε)/ε^2 := by
    rw [div_pow,← Real.rpow_two,← Real.rpow_mul hx.le]
    congr 2
    ring
  have hinvpow : ((x⁻¹)^ε/ε)^2 = x^(-(2*ε))/ε^2 := by
    rw [div_pow,← Real.rpow_two,← Real.rpow_mul (inv_nonneg.mpr hx.le),
      Real.inv_rpow hx.le,← Real.rpow_neg hx.le]
    congr 2
    ring
  by_cases hl : 0 ≤ Real.log x
  · have hh := pow_le_pow_left₀ hl (Real.log_le_rpow_div hx.le hε) 2
    rw [hpow] at hh
    exact hh.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _)) (sq_nonneg ε))
  · have hh := pow_le_pow_left₀ (le_of_lt (neg_pos.mpr (lt_of_not_ge hl)))
      (show -Real.log x ≤ (x⁻¹)^ε/ε by
        simpa only [Real.log_inv] using Real.log_le_rpow_div (inv_nonneg.mpr hx.le) hε) 2
    rw [neg_sq,hinvpow] at hh
    exact hh.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _)) (sq_nonneg ε))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedPoisson
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {S : Type*} [MeasurableSpace S]

lemma indexedFiniteCloud_measurable : Measurable (indexedFiniteCloud (S := S)) := by
  have h : Measurable (fun a : (ℕ → S) × ℕ => indexedFiniteCloud (a.2,a.1)) := by
    apply measurable_from_prod_countable_left
    intro n
    exact (finitePointMeasure_measurable n).comp (Measurable.of_eval fun index => measurable_pi_apply index.val)
  exact h.comp measurable_swap

lemma iid_prefix_law (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun x (i : Fin n) => x i.val) =
      Measure.pi (fun _ : Fin n => ν) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj (f := Fin.val) Fin.val_injective,
    Measure.infinitePi_eq_pi]

lemma indexedFiniteCloud_law (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν] :
    ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ν))).map indexedFiniteCloud =
      finitePoissonLaw r ν := by
  rw [← Measure.sum_smul_dirac (poissonMeasure r),Measure.prod_sum_left,
    Measure.map_sum indexedFiniteCloud_measurable.aemeasurable]
  simp_rw [Measure.prod_smul_left,Measure.map_smul,Measure.dirac_prod,
    Measure.map_map indexedFiniteCloud_measurable measurable_prodMk_left]
  unfold finitePoissonLaw
  congr 1
  funext n
  congr 1
  rw [← iid_prefix_law ν n,Measure.map_map (finitePointMeasure_measurable n) (by fun_prop)]
  rfl

lemma indexedPoissonMeasure_measurable : Measurable (indexedPoissonMeasure (S := S)) :=
  measureSum_measurable.comp (Measurable.of_eval fun index =>
    indexedFiniteCloud_measurable.comp (measurable_pi_apply index))

lemma indexedPoissonMeasure_law (r : ℕ → ℝ≥0) (ν : ℕ → Measure S)
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => ν i)))).map indexedPoissonMeasure =
        countablePoissonLaw r ν := by
  unfold indexedPoissonMeasure countablePoissonLaw
  have hm : Measurable (fun a : ℕ → ℕ × (ℕ → S) => fun i => indexedFiniteCloud (a i)) :=
    Measurable.of_eval fun index => indexedFiniteCloud_measurable.comp (measurable_pi_apply index)
  change (Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
    (Measure.infinitePi (fun _ : ℕ => ν i)))).map
      ((fun η : ℕ → Measure S => Measure.sum η) ∘ (fun a : ℕ → ℕ × (ℕ → S) => fun i => indexedFiniteCloud (a i))) = _
  rw [← Measure.map_map measureSum_measurable hm,Measure.infinitePi_map_pi]
  · simp_rw [indexedFiniteCloud_law]
  · exact fun _ => indexedFiniteCloud_measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_PoissonWeightedTotal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma poissonWeightedTotal_measurable {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (hF : Measurable F) : Measurable (poissonWeightedTotal F) :=
  (Measure.measurable_lintegral ((measurable_fst.add (hF.comp measurable_snd)).exp.ennreal_ofReal)).ennreal_toReal

lemma poissonWeightedTotal_eq {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (hF : Measurable F) (η : Measure (ℝ × S)) :
    poissonWeightedTotal F η = stablePoissonTotal (η.map (fun p => p.1+F p.2)) := by
  unfold poissonWeightedTotal stablePoissonTotal
  rw [lintegral_map (by fun_prop) (by fun_prop)]

lemma poissonWeightedTotal_add_const {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (_hF : Measurable F) (c : ℝ) (η : Measure (ℝ × S)) :
    poissonWeightedTotal (fun x => F x+c) η = Real.exp c * poissonWeightedTotal F η := by
  unfold poissonWeightedTotal
  simp_rw [show ∀ p : ℝ × S, p.1+(F p.2+c) = c+(p.1+F p.2) by intro p; ring,
    Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos c).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos c).le]

lemma normalized_mark_density_probability {S : Type*} [MeasurableSpace S]
    (ν : Measure S) {b : ℝ} {F : S → ℝ}
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => (Real.exp_pos _).le),hM]
  simp

lemma stablePoisson_normalized_mark_projection {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map
      (Measure.map (fun p : ℝ × S => p.1+F p.2)) =
        poissonRandomMeasureLaw (stableLogIntensity b) := by
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) :=
    normalized_mark_density_probability ν hI hM
  have hm : Measurable (fun p : ℝ × S => p.1+F p.2) := measurable_fst.add (hF.comp measurable_snd)
  have he : (((stableLogIntensity b).prod ν).map (fun p : ℝ × S => p.1+F p.2)) =
      stableLogIntensity b := by
    change Measure.map (Prod.fst ∘ logMarkShift F) ((stableLogIntensity b).prod ν) = _
    rw [← Measure.map_map measurable_fst (logMarkShift_measurable hF),stableLogIntensity_mark_shift ν hb hF,
      Measure.map_fst_prod,measure_univ,one_smul]
  rw [poissonRandomMeasureLaw_map _ hm]
  simp only [he]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
lemma gaussianRows_apply (v : ι → E) (x : E) (i : ι) :
    gaussianRows v x i = inner ℝ (v i) x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_adjoint_basis (v : ι → E) (i : ι) :
    (gaussianRows v).adjoint (EuclideanSpace.basisFun ι ℝ i) = v i := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, gaussianRows_apply,real_inner_comm]

lemma gaussianRows_map_stdGaussian (v : ι → E) :
    (stdGaussian E).map (gaussianRows v) = multivariateGaussian 0 (Matrix.gram ℝ v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  simp only [ContinuousLinearMap.toBilinForm_apply,OrthonormalBasis.coe_toBasis]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,gaussianRows_adjoint_basis,
    gaussianRows_adjoint_basis,covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simp
  rfl

end GaussianRows

open TopologicalSpace

open scoped Polynomial

lemma integral_continuous_tendsto_of_moments {a b : ℝ}
    (μ : ℕ → Measure (Icc a b)) (ν : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ x, (x.val)^k ∂μ n) atTop
      (𝓝 (∫ x, (x.val)^k ∂ν))) (f : C(Icc a b, ℝ)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hi (ρ : Measure (Icc a b)) [IsFiniteMeasure ρ] (p : ℝ[X]) :
      Integrable (fun x : Icc a b => p.eval x.val) ρ :=
    (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (p : ℝ[X]) : Tendsto (fun n => ∫ x, p.eval x.val ∂μ n) atTop
      (𝓝 (∫ x, p.eval x.val ∂ν)) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add,integral_add (hi _ p) (hi _ q)] using hp.add hq
    | monomial k c =>
      simpa only [Polynomial.eval_monomial,integral_const_mul] using tendsto_const_nhds.mul (h k)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨p, hpε⟩ := exists_polynomial_near_continuousMap a b f (ε/3) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hp p)) (ε/3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbnd (ρ : Measure (Icc a b)) [IsProbabilityMeasure ρ] :
      |(∫ x, p.eval x.val ∂ρ) - ∫ x, f x ∂ρ| < ε/3 := by
    rw [← integral_sub (hi ρ p) (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    · calc
        |∫ x, p.eval x.val - f x ∂ρ| ≤ ‖p.toContinuousMapOn (Icc a b)-f‖ := by
          simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs,ContinuousMap.sub_apply,Polynomial.toContinuousMapOn_apply,Polynomial.toContinuousMap_apply] using
            (norm_integral_le_of_norm_le_const (μ := ρ)
              (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm
                (p.toContinuousMapOn (Icc a b)-f) x))
        _ < ε/3 := hpε
  have h₁ := hbnd (μ n)
  have h₂ := hbnd ν
  have h₃ := hN n hn
  rw [Real.dist_eq] at h₃ ⊢
  calc
    |(∫ x, f x ∂μ n) - ∫ x, f x ∂ν| ≤
        |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
        |(∫ x, p.eval x.val ∂μ n) - ∫ x, p.eval x.val ∂ν| +
        |(∫ x, p.eval x.val ∂ν) - ∫ x, f x ∂ν| := by
          calc
            _ ≤ |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
                |(∫ x, p.eval x.val ∂μ n) - ∫ x, f x ∂ν| := abs_sub_le _ _ _
            _ ≤ _ := by
              linarith [abs_sub_le (∫ x, p.eval x.val ∂μ n)
                (∫ x, p.eval x.val ∂ν) (∫ x, f x ∂ν)]
    _ < ε := by rw [abs_sub_comm (∫ x, f x ∂μ n)] ; linarith

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundedC1
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma poissonWeightedTotal_law {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (poissonWeightedTotal X) =
      (poissonRandomMeasureLaw (stableLogIntensity b)).map
        (fun η => Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η) := by
  let c := Real.log (∫ x, Real.exp (b*X x) ∂ν)/b
  let F := fun x => X x-c
  have hF : Measurable F := hX.sub_const c
  have hMpos := integral_exp_pos hI
  have hfac (x : S) : Real.exp (b*F x) = Real.exp (-b*c)*Real.exp (b*X x) := by
    dsimp [F]
    rw [← Real.exp_add]
    congr 1
    ring
  have hFI : Integrable (fun x => Real.exp (b*F x)) ν := by
    simp_rw [hfac]
    exact hI.const_mul _
  have hFM : (∫ x, Real.exp (b*F x) ∂ν) = 1 := by
    simp_rw [hfac]
    rw [integral_const_mul,show -b*c = -Real.log (∫ x, Real.exp (b*X x) ∂ν) by dsimp [c]; field_simp,
      Real.exp_neg,Real.exp_log hMpos,inv_mul_cancel₀ hMpos.ne']
  have he := stablePoisson_normalized_mark_projection ν hb.le hF hFI hFM
  have hm : Measurable (fun p : ℝ×S => p.1+F p.2) := measurable_fst.add (hF.comp measurable_snd)
  have hT : poissonWeightedTotal X = fun η => Real.exp c*stablePoissonTotal
      (η.map (fun p : ℝ×S => p.1+F p.2)) := by
    funext η
    rw [← poissonWeightedTotal_eq hF]
    convert poissonWeightedTotal_add_const hF c η using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    dsimp [F]
    ring
  rw [hT,show (fun η : Measure (ℝ×S) => Real.exp c*stablePoissonTotal
      (η.map (fun p => p.1+F p.2))) =
      (fun η : Measure ℝ => Real.exp c*stablePoissonTotal η) ∘ Measure.map (fun p : ℝ×S => p.1+F p.2) from rfl,
    ← Measure.map_map ((stablePoissonTotal_measurable.const_mul _))
      (Measure.measurable_map _ hm),he]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_StableCascade
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma cascadeTotalE_measurable (n : ℕ) : Measurable (cascadeTotalE n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measure.measurable_lintegral
      ((Real.measurable_exp.comp measurable_fst).ennreal_ofReal.mul (ih.comp measurable_snd))

lemma cascadeTotal_measurable (n : ℕ) : Measurable (cascadeTotal n) :=
  (cascadeTotalE_measurable n).ennreal_toReal

lemma poissonWeightedTotal_identDistrib {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    IdentDistrib (poissonWeightedTotal X)
      (fun η => Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η)
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
  ⟨(poissonWeightedTotal_measurable hX).aemeasurable,
    (stablePoissonTotal_measurable.const_mul _).aemeasurable,
    poissonWeightedTotal_law ν hb hX hI⟩

lemma poissonWeightedTotal_pos {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν), 0 < poissonWeightedTotal X η := by
  apply (poissonWeightedTotal_identDistrib ν hb hX hI).symm.ae_snd measurableSet_Ioi
  filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
  exact mul_pos (Real.exp_pos _) hη

lemma poissonWeightedTotal_rpow_integrable {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b a : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    Integrable (fun η => (poissonWeightedTotal X η)^a)
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) := by
  have hid := (poissonWeightedTotal_identDistrib ν hb hX hI).comp
    (measurable_id.pow_const a : Measurable (fun x : ℝ => x^a))
  apply hid.integrable_iff.mpr
  have he (η : Measure ℝ) : (Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η)^a =
      (Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b))^a*(stablePoissonTotal η)^a :=
    Real.mul_rpow (Real.exp_pos _).le ENNReal.toReal_nonneg
  simpa only [Function.comp_def,id_eq,he] using (stablePoissonTotal_rpow_integrable hb hb1 ha).const_mul
    ((Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b))^a)

lemma poissonRandomMeasureLaw_ae_ae {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {p : S → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ x ∂κ, p x) : ∀ᵐ η ∂poissonRandomMeasureLaw κ, ∀ᵐ x ∂η, p x := by
  have hh := poissonRandomMeasureLaw_ae_null κ hp.compl (ae_iff.mp h)
  exact hh.mono fun η hη => ae_iff.mpr hη

lemma cascadeTotal_succ_eq {n : ℕ} (z : Fin (n+1) → ℝ)
    (hp : ∀ᵐ η ∂(cascadeLaw n (fun i => z i.succ) : Measure (StableCascade n)),
      0 < cascadeTotal n η) :
    ∀ᵐ η ∂(cascadeLaw (n+1) z : Measure (StableCascade (n+1))),
      cascadeTotal (n+1) η = poissonWeightedTotal (fun C => Real.log (cascadeTotal n C)) η := by
  let ν : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
  have hpκ : ∀ᵐ p ∂(stableLogIntensity (z 0)).prod ν, 0 < cascadeTotal n p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const ((cascadeTotal_measurable n).comp measurable_snd))).mpr
      (ae_of_all _ fun _ => hp)
  have he := poissonRandomMeasureLaw_ae_ae ((stableLogIntensity (z 0)).prod ν)
    (measurableSet_lt measurable_const ((cascadeTotal_measurable n).comp measurable_snd)) hpκ
  change ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ν), _
  filter_upwards [he] with η hη
  unfold cascadeTotal poissonWeightedTotal
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hη] with p hp
  change ENNReal.ofReal (Real.exp p.1)*cascadeTotalE n p.2 =
    ENNReal.ofReal (Real.exp (p.1+Real.log (cascadeTotal n p.2)))
  change 0 < cascadeTotal n p.2 at hp
  rw [Real.exp_add,Real.exp_log hp,ENNReal.ofReal_mul (Real.exp_pos _).le,cascadeTotal,
    ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.mp hp).2.ne]

theorem cascadeTotal_regular (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    (∀ᵐ η ∂(cascadeLaw n z : Measure (StableCascade n)), 0 < cascadeTotal n η) ∧
    ∀ a : ℝ, (∀ i, a < z i) → Integrable (fun η => (cascadeTotal n η)^a)
      (cascadeLaw n z : Measure (StableCascade n)) := by
  induction n with
  | zero =>
    constructor
    · exact ae_of_all _ fun _ => by simp [cascadeTotal,cascadeTotalE]
    · intro a _; simpa only [cascadeTotal,cascadeTotalE,ENNReal.toReal_one,Real.one_rpow] using
        (integrable_const (1:ℝ) : Integrable (fun _ : StableCascade 0 => (1:ℝ)) (cascadeLaw 0 z : Measure (StableCascade 0)))
  | succ n ih =>
    let ν : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
    have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
    obtain ⟨hpos,hint⟩ := ih (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
    have hM : Integrable (fun C => Real.exp (z 0*Real.log (cascadeTotal n C))) ν := by
      have hh := hint (z 0) (fun i => hz (by simp))
      apply hh.congr
      filter_upwards [hpos] with C hC
      rw [Real.rpow_def_of_pos hC]
      congr 1
      ring
    have hEq := cascadeTotal_succ_eq z hpos
    have hlog : Measurable (fun C : StableCascade n => Real.log (cascadeTotal n C)) :=
      (cascadeTotal_measurable n).log
    constructor
    · have hp := poissonWeightedTotal_pos ν (hz0 0) (hz1 0) hlog hM
      filter_upwards [hp,hEq] with η hp he
      rwa [he]
    · intro a ha
      have hI := poissonWeightedTotal_rpow_integrable ν (hz0 0) (hz1 0) (ha 0) hlog hM
      exact hI.congr (hEq.mono fun η he => congrArg (fun t : ℝ => t^a) he.symm)

attribute [fun_prop] stablePoissonTotal_measurable

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableTotalBiasedLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff
attribute [fun_prop] stablePoissonTotal_measurable

variable {S : Type*} [MeasurableSpace S]

lemma markedStableTotalE_projection (η : Measure (ℝ × S)) :
    markedStableTotalE η = stableJumpMomentE 1 (η.map Prod.fst) := by
  simp only [markedStableTotalE,stableJumpMomentE,one_mul]
  rw [lintegral_map (by fun_prop) measurable_fst]

lemma markedStableTotal_projection (η : Measure (ℝ × S)) :
    markedStableTotal η = stablePoissonTotal (η.map Prod.fst) := by
  simp only [markedStableTotal,markedStableTotalE_projection,stableJumpMomentE,one_mul,stablePoissonTotal]

lemma markedStableCountKernel_eq (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η) :
    markedStableCountKernel η = η := by
  rw [markedStableCountKernel,Kernel.withDensity_apply _ (by fun_prop : Measurable
    (Function.uncurry (fun (η : Measure (ℝ × S)) (p : ℝ × S) => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1)))))]
  change (((η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ)⁻¹) •
    η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1))).withDensity
      (fun p => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) = η
  have hmass : η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ =
      ENNReal.ofReal (markedStableTotal η) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ENNReal.ofReal_toReal hf).symm
  rw [hmass,withDensity_smul_measure,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have hd : (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1)*
      ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) =
      (fun _ : ℝ × S => ENNReal.ofReal (markedStableTotal η)) := by
    funext p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.exp_neg]
    field_simp
  change (ENNReal.ofReal (markedStableTotal η))⁻¹ • η.withDensity
    (fun p => ENNReal.ofReal (Real.exp p.1)*ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1))) = η
  rw [hd,withDensity_const,smul_smul,ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,one_smul]

variable [Nonempty S]
lemma markedStable_project_law (ν : Measure S) [IsProbabilityMeasure ν] (b : ℝ) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (Measure.map Prod.fst) =
      poissonRandomMeasureLaw (stableLogIntensity b) := by
  rw [poissonRandomMeasureLaw_map _ measurable_fst]
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

lemma markedStable_regular (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν),
      markedStableTotalE η ≠ ⊤ ∧ 0 < markedStableTotal η := by
  have hpres : MeasurePreserving (Measure.map (Prod.fst : ℝ × S → ℝ))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ measurable_fst,markedStable_project_law ν b⟩
  have he := hpres.quasiMeasurePreserving.ae ((stablePoisson_total_finite hb hb1).and (stablePoissonTotal_pos hb hb1))
  simpa only [markedStableTotalE_projection,markedStableTotal_projection,stableJumpMomentE,one_mul] using he

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FocusedShapeProbability
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma descendant_transform_independent {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D) [SFinite ν] [SFinite ρ]
    (T : S × C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ) :
    (ν.prod ρ).map (fun p => (p.1,T p)) = ν.prod θ := by
  exact ((MeasurePreserving.id ν).skew_product (g := fun s c => T (s,c)) hT (ae_of_all _ hLaw)).map_eq

lemma stableIntensity_normalized_mark_projection {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    ((stableLogIntensity b).prod ν).map (fun p : ℝ×S => p.1+F p.2) = stableLogIntensity b := by
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) :=
    normalized_mark_density_probability ν hI hM
  change Measure.map (Prod.fst ∘ logMarkShift F) ((stableLogIntensity b).prod ν) = _
  rw [← Measure.map_map measurable_fst (logMarkShift_measurable hF),stableLogIntensity_mark_shift ν hb hF,
    Measure.map_fst_prod,measure_univ,one_smul]

lemma stableIntensity_descendant_transform {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure θ]
    {b : ℝ} (hb : 0 ≤ b) (T : S×C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    ((stableLogIntensity b).prod (ν.prod ρ)).map
      (fun p : ℝ×(S×C) => (p.1+F p.2.1,T p.2)) = (stableLogIntensity b).prod θ := by
  let I := stableLogIntensity b
  have hmark : MeasurePreserving (fun p : S×C => (p.1,T p)) (ν.prod ρ) (ν.prod θ) :=
    ⟨measurable_fst.prodMk hT, descendant_transform_independent ν ρ θ T hT hLaw⟩
  have hs : MeasurePreserving (fun p : ℝ×S => p.1+F p.2) (I.prod ν) I :=
    ⟨measurable_fst.add (hF.comp measurable_snd), stableIntensity_normalized_mark_projection ν hb hF hI hM⟩
  have hassoc : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ×S)×D ≃ᵐ ℝ×(S×D))
      ((I.prod ν).prod θ) (I.prod (ν.prod θ)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod⟩
  have hmain := (hs.prod (MeasurePreserving.id θ)).comp
    ((hassoc.symm).comp ((MeasurePreserving.id I).prod hmark))
  exact hmain.map_eq

lemma stablePoisson_descendant_transform {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    [Nonempty S] [Nonempty C] [Nonempty D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure θ]
    {b : ℝ} (hb : 0 ≤ b) (T : S×C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod (ν.prod ρ))).map
      (Measure.map (fun p : ℝ×(S×C) => (p.1+F p.2.1,T p.2))) =
        poissonRandomMeasureLaw ((stableLogIntensity b).prod θ) := by
  rw [poissonRandomMeasureLaw_map _ (by fun_prop)]
  congr 1
  exact stableIntensity_descendant_transform ν ρ θ hb T hT hLaw hF hI hM

lemma countKernel_parameter_map_measurable {X S D : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace D]
    (F : X×(ℝ×S) → D) (hF : Measurable F) :
    Measurable (fun p : X×Measure (ℝ×S) =>
      (markedStableCountKernel p.2).map (fun q => F (p.1,q))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  let κ : Kernel (X×Measure (ℝ×S)) (ℝ×S) := markedStableCountKernel.comap Prod.snd measurable_snd
  have hh : Measurable (fun p : (X×Measure (ℝ×S))×(ℝ×S) =>
      (s.indicator (fun _ => (1:ℝ≥0∞))) (F (p.1.1,p.2))) :=
    (measurable_const.indicator hs).comp (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  have hi := hh.lintegral_kernel_prod_right' (κ := κ)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  calc
    _ = ∫⁻ d, s.indicator (fun _ => (1:ℝ≥0∞)) d ∂(markedStableCountKernel p.2).map (fun q => F (p.1,q)) :=
      (lintegral_indicator_one hs).symm
    _ = _ := lintegral_map (measurable_const.indicator hs)
      (hF.comp (measurable_const.prodMk measurable_id))

lemma decoratedCascadeTransform_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) : Measurable (decoratedCascadeTransform step n F) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let H : X×(ℝ×(S×DecoratedCascade S n)) → ℝ×StableCascade n := fun p =>
      (p.2.1+F 0 (p.1,p.2.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,p.2.2.1),p.2.2.2))
    have hH : Measurable H :=
      (measurable_snd.fst.add ((hF 0).comp (measurable_fst.prodMk measurable_snd.snd.fst))).prodMk
        ((ih (fun i => F i.succ) (fun i => hF i.succ)).comp
          ((hstep.comp (measurable_fst.prodMk measurable_snd.snd.fst)).prodMk measurable_snd.snd.snd))
    exact countKernel_parameter_map_measurable H hH

theorem decoratedCascadeTransform_law {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)).map
      (fun η => decoratedCascadeTransform step n F (x,η)) = cascadeLaw n z := by
  induction n generalizing x with
  | zero =>
    change Measure.map (fun _ : Unit => ()) (Measure.dirac ()) = Measure.dirac ()
    exact Measure.map_dirac ()
  | succ n ih =>
    let ρ : Measure (DecoratedCascade S n) := decoratedCascadeLaw ν n (fun i => z i.succ)
    let θ : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
    let T : S×DecoratedCascade S n → StableCascade n := fun p =>
      decoratedCascadeTransform step n (fun i => F i.succ) (step (x,p.1),p.2)
    have hT : Measurable T :=
      (decoratedCascadeTransform_measurable step hstep n _ (fun i => hF i.succ)).comp
        ((hstep.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have ht : ∀ s, ρ.map (fun c => T (s,c)) = θ := fun s =>
      ih (fun i => z i.succ) (fun i => hz0 i.succ) (fun i => hz1 i.succ)
        (fun i => F i.succ) (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ) (step (x,s))
    let G : ℝ×(S×DecoratedCascade S n) → ℝ×StableCascade n :=
      fun p => (p.1+F 0 (x,p.2.1),T p.2)
    change (poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ((ν : Measure S).prod ρ))).map
      (fun η => (markedStableCountKernel η).map G) = poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod θ)
    calc
      _ = (poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ((ν : Measure S).prod ρ))).map
            (Measure.map G) := by
        apply Measure.map_congr
        filter_upwards [markedStable_regular ((ν : Measure S).prod ρ) (hz0 0) (hz1 0)] with η hη
        rw [markedStableCountKernel_eq η hη.1 hη.2]
      _ = _ := stablePoisson_descendant_transform (ν : Measure S) ρ θ (hz0 0).le T hT ht
        ((hF 0).comp (measurable_const.prodMk measurable_id)) (hI 0 x) (hM 0 x)

lemma cascadeTotal_log_memLp_two (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    MemLp (fun η => Real.log (cascadeTotal n η)) 2 (cascadeLaw n z : Measure (StableCascade n)) := by
  cases n with
  | zero => simp [cascadeTotal,cascadeTotalE]
  | succ n =>
    obtain ⟨hp,hI⟩ := cascadeTotal_regular (n+1) z hz hz0 hz1
    let ε : ℝ := z 0/4
    have hε : 0 < ε := div_pos (hz0 0) (by norm_num)
    have hmin : ∀ i, z 0 ≤ z i := fun i => hz.monotone (Fin.zero_le i)
    have hplus : ∀ i, 2*ε < z i := by intro i; dsimp [ε]; linarith [hmin i,hz0 0]
    have hminus : ∀ i, -(2*ε) < z i := by intro i; linarith [hz0 i]
    apply (memLp_two_iff_integrable_sq (cascadeTotal_measurable (n+1)).log.aestronglyMeasurable).mpr
    apply (((hI (2*ε) hplus).add (hI (-(2*ε)) hminus)).div_const (ε^2)).mono'
      ((cascadeTotal_measurable (n+1)).log.pow_const (2:ℕ)).aestronglyMeasurable
    filter_upwards [hp] with η hη
    change |(Real.log (cascadeTotal (n+1) η))^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact log_sq_le_two_rpow hη hε

lemma decoratedWeightedTotalE_transform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) (p : X×DecoratedCascade S n) :
    cascadeTotalE n (decoratedCascadeTransform step n F p) = decoratedWeightedTotalE step n F p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let G : ℝ×(S×DecoratedCascade S n) → ℝ×StableCascade n := fun q =>
      (q.1+F 0 (p.1,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,q.2.1),q.2.2))
    have hG : Measurable G :=
      (measurable_fst.add ((hF 0).comp (measurable_const.prodMk measurable_snd.fst))).prodMk
        ((decoratedCascadeTransform_measurable step hstep n _ (fun i => hF i.succ)).comp
          ((hstep.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
    change (∫⁻ q : ℝ×StableCascade n, ENNReal.ofReal (Real.exp q.1)*cascadeTotalE n q.2
      ∂(markedStableCountKernel p.2).map G) = _
    have hw : Measurable (fun q : ℝ×StableCascade n => ENNReal.ofReal (Real.exp q.1)*cascadeTotalE n q.2) :=
      ((Real.measurable_exp.comp measurable_fst).ennreal_ofReal.mul ((cascadeTotalE_measurable n).comp measurable_snd))
    calc
      _ = ∫⁻ q, ENNReal.ofReal (Real.exp (G q).1)*cascadeTotalE n (G q).2 ∂markedStableCountKernel p.2 :=
        lintegral_map hw hG
      _ = _ := by
        apply lintegral_congr
        intro q
        dsimp only [G]
        rw [ih (fun i => F i.succ) (fun i => hF i.succ)]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_InfinitePiSplit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma infinitePi_sumPiEquivProdPi_symm {ι κ : Type*} {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.infinitePi fun i => μ (.inl i)).prod
      (Measure.infinitePi fun i => μ (.inr i))).map
        (MeasurableEquiv.sumPiEquivProdPi X).symm = Measure.infinitePi μ := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have he : (MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' ((s : Set (ι ⊕ κ)).pi t) =
      (s.toLeft : Set ι).pi (fun i => t (.inl i)) ×ˢ
      (s.toRight : Set κ).pi (fun i => t (.inr i)) := by
    ext p
    simp only [mem_preimage,mem_pi,mem_prod,Finset.mem_coe,Finset.mem_toLeft,Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h (.inl i) hi,fun i hi => h (.inr i) hi⟩
    · rintro ⟨h₁,h₂⟩ (i|i) hi
      · exact h₁ i hi
      · exact h₂ i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun _ _ => ht _),
    Measure.infinitePi_pi _ (fun _ _ => ht _),Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

lemma infinitePi_zip {ι A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : ι → Measure A) (ν : ι → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  let e := MeasurableEquiv.arrowProdEquivProdArrow A B s
  have hm : Measurable (Prod.map (Finset.restrict s : (ι → A) → (s → A))
      (Finset.restrict s : (ι → B) → (s → B))) := by fun_prop
  have hp : ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p (i : s) => (p.1 i,p.2 i)) = Measure.pi (fun i : s => (μ i).prod (ν i)) := by
    calc
      _ = (((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
        (Prod.map (Finset.restrict s) (Finset.restrict s))).map e.symm := by
          rw [Measure.map_map e.symm.measurable hm]
          rfl
      _ = _ := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
          Measure.infinitePi_map_restrict,Measure.infinitePi_map_restrict]
        exact (measurePreserving_arrowProdEquivProdArrow A B s (fun i => μ i) (fun i => ν i)).symm.map_eq
  have he : (fun p : (ι → A) × (ι → B) => fun i => (p.1 i,p.2 i)) ⁻¹'
      (s : Set ι).pi t =
      (fun p : (ι → A) × (ι → B) => fun i : s => (p.1 i,p.2 i)) ⁻¹'
        (univ.pi (fun i : s => t i)) := by
    ext p
    simp [Set.mem_pi]
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet fun i _ => ht i),he,
    ← Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi fun i : s => ht i),hp,Measure.pi_pi]
  exact Finset.prod_attach s (fun i => (μ i).prod (ν i) (t i))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedMarkedPoisson
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafMeasure_sfinite _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma law_count_iid_zip {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (r : ℝ≥0) (ρ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] :
    (((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ρ))).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => (p.1.1, fun j => (p.1.2 j,p.2 j))) =
      (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ρ.prod ν)) := by
  let z : ((ℕ → A) × (ℕ → B)) → ℕ → A × B := fun p j => (p.1 j,p.2 j)
  have hz : Measurable z := by fun_prop
  calc
    _ = ((((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ρ))).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
        (MeasurableEquiv.prodAssoc : ((ℕ × (ℕ → A)) × (ℕ → B)) ≃ᵐ (ℕ × ((ℕ → A) × (ℕ → B))))).map (Prod.map id z) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [Measure.prodAssoc_prod, ← Measure.map_prod_map _ _ measurable_id hz,
        Measure.map_id, infinitePi_zip]

lemma indexedMarkedPoisson_law {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (r : ℕ → ℝ≥0) (ρ : ℕ → Measure A) (ν : Measure B)
    [∀ i, IsProbabilityMeasure (ρ i)] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => ρ i)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
        (fun p => indexedPoissonMeasure (fun i => (p.1 i |>.1,
          fun j => ((p.1 i).2 j,p.2 i j)))) =
        countablePoissonLaw r (fun i => (ρ i).prod ν) := by
  let z : (ℕ × (ℕ → A)) × (ℕ → B) → ℕ × (ℕ → A × B) :=
    fun p => (p.1.1,fun j => (p.1.2 j,p.2 j))
  have hz : Measurable z := by fun_prop
  let L := Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => ρ i)))
  let M := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν))
  have hp : (L.prod M).map (fun p i => z (p.1 i,p.2 i)) =
      Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
        (Measure.infinitePi (fun _ : ℕ => (ρ i).prod ν))) := by
    calc
      _ = ((L.prod M).map (fun p i => (p.1 i,p.2 i))).map (fun p i => z (p i)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = _ := by
        dsimp [L,M]
        rw [infinitePi_zip, Measure.infinitePi_map_pi]
        simp_rw [show ∀ i, ((poissonMeasure (r i)).prod
          (Measure.infinitePi (fun _ : ℕ => ρ i)) |>.prod
            (Measure.infinitePi (fun _ : ℕ => ν))).map z =
            (poissonMeasure (r i)).prod (Measure.infinitePi (fun _ : ℕ => (ρ i).prod ν))
          from fun i => law_count_iid_zip (r i) (ρ i) ν]
        exact fun _ => hz
  change (L.prod M).map (indexedPoissonMeasure ∘ (fun p i => z (p.1 i,p.2 i))) = _
  rw [← Measure.map_map indexedPoissonMeasure_measurable (by fun_prop),hp,
    indexedPoissonMeasure_law]

lemma countablePoissonLaw_product_intensity {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Nonempty A] [Nonempty B]
    (κ : Measure A) [SFinite κ] (ν : Measure B) [IsProbabilityMeasure ν] :
    countablePoissonLaw (fun i => ((sfiniteSeq κ i) univ).toNNReal)
      (fun i => (finiteIntensityMarks (sfiniteSeq κ i)).prod ν) =
        poissonRandomMeasureLaw (κ.prod ν) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [countablePoissonLaw_laplace_intensity _ _ hf hf0,
    poissonRandomMeasureLaw_laplace _ hf hf0]
  congr 2
  have he : countablePoissonIntensity (fun i => ((sfiniteSeq κ i) univ).toNNReal)
      (fun i => (finiteIntensityMarks (sfiniteSeq κ i)).prod ν) = κ.prod ν := by
    unfold countablePoissonIntensity
    simp_rw [← Measure.prod_smul_left, finiteIntensityMarks_smul]
    rw [← Measure.prod_sum_left,sum_sfiniteSeq]
  rw [he]

lemma indexedCascadeRealize_measurable {S : Type} [MeasurableSpace S] (n : ℕ) :
    Measurable (indexedCascadeRealize (S := S) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    dsimp only [indexedCascadeRealize]
    apply indexedPoissonMeasure_measurable.comp
    fun_prop

lemma countablePoissonLaw_eq_canonical {A : Type*} [MeasurableSpace A] [Nonempty A]
    (r : ℕ → ℝ≥0) (ρ : ℕ → Measure A) [∀ i, IsProbabilityMeasure (ρ i)] :
    countablePoissonLaw r ρ = poissonRandomMeasureLaw (countablePoissonIntensity r ρ) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [countablePoissonLaw_laplace_intensity _ _ hf hf0,
    poissonRandomMeasureLaw_laplace _ hf hf0]

lemma prod_rotate_front {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (τ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    (μ.prod (ν.prod τ)).map (fun p => (p.2.1,(p.1,p.2.2))) = ν.prod (μ.prod τ) := by
  have h := (measurePreserving_prodAssoc ν μ τ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id τ)).comp
      (measurePreserving_prodAssoc μ ν τ).symm)
  exact h.map_eq

lemma indexedPoissonMeasure_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {g : A → B} (hg : Measurable g) (a : ℕ → ℕ × (ℕ → A)) :
    (indexedPoissonMeasure a).map g =
      indexedPoissonMeasure (fun i => ((a i).1,fun j => g ((a i).2 j))) := by
  unfold indexedPoissonMeasure indexedFiniteCloud finitePointMeasure
  rw [Measure.map_sum hg.aemeasurable]
  simp_rw [Measure.map_finset_sum hg.aemeasurable,Measure.map_dirac' hg]

lemma prod_interlace_law {A B C D E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]
    (α : Measure A) (β : Measure B) (γ : Measure C) (δ : Measure D) (ε : Measure E)
    [SFinite α] [SFinite β] [SFinite γ] [SFinite δ] [SFinite ε]
    {g : B × D → E} (hg : MeasurePreserving g (β.prod δ) ε) :
    ((α.prod β).prod (γ.prod δ)).map
      (fun p => (p.1.1,(p.2.1,g (p.1.2,p.2.2)))) = α.prod (γ.prod ε) := by
  have h₁ := measurePreserving_prodAssoc α β (γ.prod δ)
  have h₂ : MeasurePreserving (fun p : B × (C × D) => (p.2.1,(p.1,p.2.2)))
      (β.prod (γ.prod δ)) (γ.prod (β.prod δ)) :=
    ⟨by fun_prop,prod_rotate_front β γ δ⟩
  exact (((MeasurePreserving.id α).prod ((MeasurePreserving.id γ).prod hg)).comp
    (((MeasurePreserving.id α).prod h₂).comp h₁)).map_eq

lemma indexedCascadeRealize_law {S : Type} [MeasurableSpace S] [Nonempty S]
    (ν : ProbabilityMeasure S) (n : ℕ) (z : Fin n → ℝ) :
    ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n)).map (indexedCascadeRealize n) =
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  induction n with
  | zero => simp [indexedCascadeBaseLaw,indexedCascadeMarksLaw,indexedCascadeRealize,decoratedCascadeLaw]
  | succ n ih =>
    let κ := stableLogIntensity (z 0)
    let r : ℕ → ℝ≥0 := fun i => ((sfiniteSeq κ i) univ).toNNReal
    let ρ := fun i => finiteIntensityMarks (sfiniteSeq κ i)
    let B := (indexedCascadeBaseLaw n (fun j => z j.succ) : Measure (IndexedCascadeBase n))
    let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
    let D := (decoratedCascadeLaw ν n (fun j => z j.succ) : Measure (DecoratedCascade S n))
    let f : ((ℝ × IndexedCascadeBase n) × (S × IndexedCascadeMarks S n)) →
        ℝ × (S × DecoratedCascade S n) :=
      fun p => (p.1.1,(p.2.1,indexedCascadeRealize n (p.1.2,p.2.2)))
    have hf : Measurable f := by
      exact measurable_fst.fst.prodMk (measurable_snd.fst.prodMk
        ((indexedCascadeRealize_measurable n).comp (measurable_fst.snd.prodMk measurable_snd.snd)))
    have hR : MeasurePreserving (indexedCascadeRealize (S := S) n) (B.prod M) D :=
      ⟨indexedCascadeRealize_measurable n,ih (fun j => z j.succ)⟩
    have hi : (countablePoissonIntensity r (fun i => (ρ i).prod B |>.prod ((ν : Measure S).prod M))).map f =
        κ.prod ((ν : Measure S).prod D) := by
      unfold countablePoissonIntensity
      rw [Measure.map_sum hf.aemeasurable]
      simp_rw [Measure.map_smul]
      have hfi (i : ℕ) : (((ρ i).prod B).prod ((ν : Measure S).prod M)).map f =
          (ρ i).prod ((ν : Measure S).prod D) :=
        prod_interlace_law (ρ i) B (ν : Measure S) M D hR
      simp_rw [hfi]
      dsimp only [r,ρ]
      simp_rw [← Measure.prod_smul_left,finiteIntensityMarks_smul]
      rw [← Measure.prod_sum_left,sum_sfiniteSeq]
    let P := Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => (ρ i).prod B)))
    let Q := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (ν : Measure S).prod M))
    let a : ((ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n)) ×
      (ℕ → ℕ → S × IndexedCascadeMarks S n)) →
        ℕ → ℕ × (ℕ → (ℝ × IndexedCascadeBase n) × (S × IndexedCascadeMarks S n)) :=
      fun p i => ((p.1 i).1,fun j => ((p.1 i).2 j,p.2 i j))
    have ha : Measurable a := by fun_prop
    have he : indexedCascadeRealize (S := S) (n+1) =
        Measure.map f ∘ (indexedPoissonMeasure ∘ a) := by
      funext p
      exact (indexedPoissonMeasure_map hf (a p)).symm
    change (P.prod Q).map (indexedCascadeRealize (S := S) (n+1)) =
      poissonRandomMeasureLaw (κ.prod ((ν : Measure S).prod D))
    rw [he,← Measure.map_map (Measure.measurable_map f hf)
      (indexedPoissonMeasure_measurable.comp ha)]
    have hP := indexedMarkedPoisson_law r (fun i => (ρ i).prod B) ((ν : Measure S).prod M)
    change (P.prod Q).map (indexedPoissonMeasure ∘ a) = _ at hP
    rw [hP,countablePoissonLaw_eq_canonical,poissonRandomMeasureLaw_map _ hf]
    congr 1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedCascadeRegular
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma indexedPoissonMeasure_lintegral {A : Type*} [MeasurableSpace A]
    (a : ℕ → ℕ × (ℕ → A)) {f : A → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂indexedPoissonMeasure a) =
      ∑' i, ∑ j : Fin ((a i).1), f ((a i).2 j.val) := by
  simp only [indexedPoissonMeasure,indexedFiniteCloud,finitePointMeasure,
    lintegral_sum_measure,lintegral_finsetSum_measure,lintegral_dirac' _ hf]

lemma indexedCascadeRealize_rootMass {S : Type} [MeasurableSpace S] (n : ℕ)
    (b : IndexedCascadeBase (n+1)) (m : IndexedCascadeMarks S (n+1)) :
    markedStableTotalE (indexedCascadeRealize (n+1) (b,m)) = indexedCascadeRootMass b := by
  unfold indexedCascadeRealize indexedCascadeRootMass markedStableTotalE
  rw [indexedPoissonMeasure_lintegral _ (by fun_prop),indexedPoissonMeasure_lintegral _ (by fun_prop)]

lemma indexedCascadeBase_child_law (n : ℕ) (z : Fin (n+1) → ℝ) (i j : ℕ) :
    MeasurePreserving (fun b : IndexedCascadeBase (n+1) => (((b i).2 j).2))
      (indexedCascadeBaseLaw (n+1) z) (indexedCascadeBaseLaw n (fun l => z l.succ)) := by
  let B := (indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n))
  let ρ := fun i => finiteIntensityMarks (sfiniteSeq (stableLogIntensity (z 0)) i)
  let r := fun i => ((sfiniteSeq (stableLogIntensity (z 0)) i) univ).toNNReal
  exact (measurePreserving_snd (μ := ρ i) (ν := B)).comp
    ((measurePreserving_eval_infinitePi (fun _ : ℕ => (ρ i).prod B) j).comp
      ((measurePreserving_snd (μ := poissonMeasure (r i))
        (ν := Measure.infinitePi (fun _ : ℕ => (ρ i).prod B))).comp
          (measurePreserving_eval_infinitePi (fun i => (poissonMeasure (r i)).prod
            (Measure.infinitePi (fun _ : ℕ => (ρ i).prod B))) i)))

lemma indexedCascadeRootMass_pos (n : ℕ) (z : Fin (n+1) → ℝ)
    (hz0 : 0 < z 0) (hz1 : z 0 < 1) :
    ∀ᵐ b ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))),
      0 < (indexedCascadeRootMass b).toReal := by
  let B := (indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n))
  let κ := stableLogIntensity (z 0)
  have hl : (indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).map
      indexedPoissonMeasure = poissonRandomMeasureLaw (κ.prod B) := by
    change (Measure.infinitePi (fun i => (poissonMeasure (((sfiniteSeq κ i) univ).toNNReal)).prod
      (Measure.infinitePi (fun _ : ℕ => (finiteIntensityMarks (sfiniteSeq κ i)).prod B)))).map
        indexedPoissonMeasure = _
    rw [indexedPoissonMeasure_law,countablePoissonLaw_product_intensity]
  have hreg := (markedStable_regular B hz0 hz1).mono fun η hη => hη.2
  rw [← hl] at hreg
  exact (ae_map_iff indexedPoissonMeasure_measurable.aemeasurable
    (measurableSet_lt measurable_const markedStableTotal_measurable)).mp hreg

lemma indexedCascadeGood_ae (n : ℕ) (z : Fin n → ℝ)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    ∀ᵐ b ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)), IndexedCascadeGood n b := by
  induction n with
  | zero => exact ae_of_all _ fun _ => trivial
  | succ n ih =>
    have ht (i j : ℕ) : ∀ᵐ b ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))),
        IndexedCascadeGood n (((b i).2 j).2) :=
      (indexedCascadeBase_child_law n z i j).quasiMeasurePreserving.ae
        (ih (fun l => z l.succ) (fun l => hz0 l.succ) (fun l => hz1 l.succ))
    filter_upwards [indexedCascadeRootMass_pos n z (hz0 0) (hz1 0),
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (ht i))] with b hb ht
    exact ⟨hb,ht⟩

lemma indexedCascadeGood_countKernel {S : Type} [MeasurableSpace S] {n : ℕ}
    {b : IndexedCascadeBase (n+1)} (hb : IndexedCascadeGood (n+1) b)
    (m : IndexedCascadeMarks S (n+1)) :
    markedStableCountKernel (indexedCascadeRealize (n+1) (b,m)) =
      indexedCascadeRealize (n+1) (b,m) := by
  apply markedStableCountKernel_eq
  · rw [indexedCascadeRealize_rootMass]
    exact (ENNReal.toReal_pos_iff.mp hb.1).2.ne
  · change 0 < (markedStableTotalE (indexedCascadeRealize (n+1) (b,m))).toReal
    rw [indexedCascadeRealize_rootMass]
    exact hb.1

lemma indexedLeafMeasure_lintegral (n : ℕ) (b : IndexedCascadeBase n) (f : IndexedLeaf n → ℝ≥0∞) :
    (∫⁻ l, f l ∂indexedLeafMeasure n b) = ∑' l, (indexedLeafWeight n b l : ℝ≥0∞)*f l := by
  simp only [indexedLeafMeasure,lintegral_sum_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]

lemma indexedLeafMeasure_lintegral_succ (n : ℕ) (b : IndexedCascadeBase (n+1))
    (f : IndexedLeaf (n+1) → ℝ≥0∞) :
    (∫⁻ l, f l ∂indexedLeafMeasure (n+1) b) =
      ∑' i, ∑ j : Fin ((b i).1), ENNReal.ofReal (Real.exp (((b i).2 j.val).1))*
        ∫⁻ l, f (i,j.val,l) ∂indexedLeafMeasure n (((b i).2 j.val).2) := by
  rw [indexedLeafMeasure_lintegral]
  change (∑' l : ℕ × ℕ × IndexedLeaf n, (indexedLeafWeight (n+1) b l : ℝ≥0∞)*f l) = _
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro i
  rw [ENNReal.tsum_prod']
  have he (j : ℕ) : (∑' l : IndexedLeaf n,
      (indexedLeafWeight (n+1) b (i,j,l) : ℝ≥0∞)*f (i,j,l)) =
      if j < (b i).1 then ENNReal.ofReal (Real.exp (((b i).2 j).1))*
        (∫⁻ l, f (i,j,l) ∂indexedLeafMeasure n (((b i).2 j).2)) else 0 := by
    by_cases hj : j < (b i).1
    · simp only [indexedLeafWeight,ite_eq_left hj,ENNReal.coe_mul]
      change (∑' l : IndexedLeaf n, ENNReal.ofReal (Real.exp (((b i).2 j).1)) *
        (indexedLeafWeight n (((b i).2 j).2) l : ℝ≥0∞)*f (i,j,l)) = _
      rw [indexedLeafMeasure_lintegral,← ENNReal.tsum_mul_left]
      exact tsum_congr (fun l => mul_assoc _ _ _)
    · simp [indexedLeafWeight,hj]
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range ((b i).1)) (fun j hj => by simp [Finset.mem_range.not.mp hj])]
  rw [Fin.sum_univ_eq_sum_range (fun j => ENNReal.ofReal (Real.exp (((b i).2 j).1)) *
    ∫⁻ l, f (i,j,l) ∂indexedLeafMeasure n (((b i).2 j).2))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (Finset.mem_range.mp hj)]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedVertices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedMarksFromVertices_measurable {S : Type} [MeasurableSpace S] (n : ℕ) :
    Measurable (indexedMarksFromVertices (S := S) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply (i,j,Sum.inl ())).prodMk
      (ih.comp (Measurable.of_eval fun vertex => measurable_pi_apply (i,j,Sum.inr vertex)))

lemma infinitePi_sumPiEquivProdPi {ι κ : Type*} {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.infinitePi μ).map (MeasurableEquiv.sumPiEquivProdPi X) =
      (Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i)) := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  exact (infinitePi_sumPiEquivProdPi_symm μ).symm

lemma indexedMarksFromVertices_law {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (n : ℕ) :
    (Measure.infinitePi (fun _ : IndexedVertex n => (ν : Measure S))).map
      (indexedMarksFromVertices n) = indexedCascadeMarksLaw ν n := by
  induction n with
  | zero => simp [indexedMarksFromVertices,indexedCascadeMarksLaw,Measure.map_const]
  | succ n ih =>
    let Q := Measure.infinitePi (fun _ : Unit ⊕ IndexedVertex n => (ν : Measure S))
    let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
    let a : (Unit ⊕ IndexedVertex n → S) → S×IndexedCascadeMarks S n := fun f =>
      (f (.inl ()),indexedMarksFromVertices n (fun v => f (.inr v)))
    have ha : Measurable a := (measurable_pi_apply _).prodMk
      ((indexedMarksFromVertices_measurable n).comp (Measurable.of_eval fun vertex => measurable_pi_apply (Sum.inr vertex)))
    have haQ : Q.map a = (ν : Measure S).prod M := by
      let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ IndexedVertex n => S)
      have he : a = (Prod.map (fun f : Unit → S => f ()) (indexedMarksFromVertices n)) ∘ e := rfl
      rw [he,← Measure.map_map ((measurable_pi_apply ()).prodMap (indexedMarksFromVertices_measurable n)) e.measurable,infinitePi_sumPiEquivProdPi]
      rw [← Measure.map_prod_map _ _ (by fun_prop) (indexedMarksFromVertices_measurable n),ih]
      rw [(measurePreserving_eval_infinitePi (fun _ : Unit => (ν : Measure S)) ()).map_eq]
    let e := MeasurableEquiv.curry ℕ (ℕ × (Unit ⊕ IndexedVertex n)) S
    let r := MeasurableEquiv.curry ℕ (Unit ⊕ IndexedVertex n) S
    let c : (IndexedVertex (n+1) → S) → ℕ → ℕ → Unit ⊕ IndexedVertex n → S :=
      fun f i j v => f (i,j,v)
    have hc : Measurable c := by fun_prop
    have hcQ : (Measure.infinitePi (fun _ : IndexedVertex (n+1) => (ν : Measure S))).map c =
        Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => Q)) := by
      have he : c = (fun f i => r (f i)) ∘ e := rfl
      rw [he,← Measure.map_map (by fun_prop) e.measurable]
      dsimp only [e, IndexedVertex]
      rw [Measure.infinitePi_map_curry (fun _ _ => (ν : Measure S)),
        Measure.infinitePi_map_pi _ (fun _ => r.measurable)]
      dsimp only [r]
      simp_rw [Measure.infinitePi_map_curry (fun _ _ => (ν : Measure S))]
      rfl
    have he : indexedMarksFromVertices (S := S) (n+1) = (fun f i j => a (f i j)) ∘ c := rfl
    rw [he,← Measure.map_map (by fun_prop) hc,hcQ]
    rw [Measure.infinitePi_map_pi _ (f := fun _ (f : ℕ → Unit ⊕ IndexedVertex n → S) => fun j => a (f j))
      (fun _ => Measurable.of_eval fun column => ha.comp (measurable_pi_apply column))]
    simp_rw [Measure.infinitePi_map_pi _ (fun _ => ha),haQ]
    rfl

lemma indexedLeafVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafVertex n l) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [indexedLeafVertex] at hij
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [indexedLeafVertex] at hij
      | succ j =>
        simpa only [Fin.succ_inj] using ih l.2.2 (by simpa [indexedLeafVertex] using hij)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_DecoratedWeightedTotal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma decoratedWeightedTotalE_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) : Measurable (decoratedWeightedTotalE step n F) := by
  have he : decoratedWeightedTotalE step n F = cascadeTotalE n ∘ decoratedCascadeTransform step n F := by
    funext p
    exact (decoratedWeightedTotalE_transform step hstep n F hF p).symm
  rw [he]
  exact (cascadeTotalE_measurable n).comp (decoratedCascadeTransform_measurable step hstep n F hF)

lemma decoratedWeightedTotal_transform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) (p : X×DecoratedCascade S n) :
    decoratedWeightedTotal step n F p = cascadeTotal n (decoratedCascadeTransform step n F p) :=
  congrArg ENNReal.toReal (decoratedWeightedTotalE_transform step hstep n F hF p).symm

lemma decoratedWeightedTotal_identDistrib {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    IdentDistrib (fun η => decoratedWeightedTotal step n F (x,η)) (cascadeTotal n)
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) (cascadeLaw n z) := by
  have hT : Measurable (fun η => decoratedCascadeTransform step n F (x,η)) :=
    (decoratedCascadeTransform_measurable step hstep n F hF).comp (measurable_const.prodMk measurable_id)
  have he : (fun η => decoratedWeightedTotal step n F (x,η)) =
      cascadeTotal n ∘ (fun η => decoratedCascadeTransform step n F (x,η)) := by
    funext η
    exact decoratedWeightedTotal_transform step hstep n F hF (x,η)
  rw [he]
  refine ⟨((cascadeTotal_measurable n).comp hT).aemeasurable,(cascadeTotal_measurable n).aemeasurable,?_⟩
  rw [← Measure.map_map (cascadeTotal_measurable n) hT,decoratedCascadeTransform_law ν step hstep n z hz0 hz1 F hF hI hM]

theorem decoratedCascade_log_identity {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ) :
    (∫ η, Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η)) ∂(decoratedCascadeLaw ν n z)) = c := by
  have hid := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 F hF hI hM x
  have hiz := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  have hld := hid.comp Real.measurable_log
  have hlz := hiz.comp Real.measurable_log
  have hL := cascadeTotal_log_memLp_two n z hz hz0 hz1
  have hId := MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (hld.memLp_iff.mpr hL)
  have hIz := MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (hlz.memLp_iff.mpr hL)
  have hp := (cascadeTotal_regular n z hz hz0 hz1).1
  have hdpos := hid.symm.ae_snd measurableSet_Ioi hp
  have hzpos := hiz.symm.ae_snd measurableSet_Ioi hp
  have he : (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) =ᵐ[(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))]
      (fun η => c+Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) := by
    filter_upwards [hdpos,hzpos] with η hη hg
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hη.ne') hg.ne',
      Real.log_mul (Real.exp_ne_zero _) hη.ne',Real.log_exp]
  have hsplit := integral_sub ((integrable_const c).add hId) hIz
  have hadd := integral_add (integrable_const c) hId
  have hdint := hld.integral_eq
  have hzint := hlz.integral_eq
  simp only [Pi.add_apply,Function.comp_apply] at hsplit hadd hdint hzint
  rw [integral_congr_ae he,hsplit,hadd,hdint,hzint]
  simp

lemma bounded_fractional_exp_integrable {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b C : ℝ} (hb : 0 ≤ b) {f : S → ℝ}
    (hf : Measurable f) (hC : ∀ s, |f s| ≤ C) :
    Integrable (fun s => Real.exp (b*f s)) ν := by
  apply (integrable_const (Real.exp (b*C))).mono' ((hf.const_mul b).exp).aestronglyMeasurable
  exact ae_of_all _ fun s => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hC s)) hb)

lemma fractionalLogMoment_abs_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b C : ℝ} (hb : 0 < b) {f : X×S → ℝ}
    (hf : Measurable f) (hC : ∀ p, |f p| ≤ C) (x : X) :
    |fractionalLogMoment ν b f x| ≤ C := by
  have hI := bounded_fractional_exp_integrable ν hb.le
    (hf.comp (measurable_const.prodMk measurable_id)) (fun s => hC (x,s))
  have hp : 0 < ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    apply integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hI |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hlo : Real.exp (b*(-C)) ≤ ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    have h := integral_mono (integrable_const (Real.exp (b*(-C)))) hI
      (fun s => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hC (x,s))).1 hb.le))
    simpa using h
  have hup : (∫ s, Real.exp (b*f (x,s)) ∂ν) ≤ Real.exp (b*C) := by
    have h := integral_mono hI (integrable_const (Real.exp (b*C)))
      (fun s => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hC (x,s))).2 hb.le))
    simpa using h
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hu := Real.log_le_log hp hup
  rw [Real.log_exp] at hl hu
  apply abs_le.mpr
  change -C ≤ Real.log _/b ∧ Real.log _/b ≤ C
  constructor
  · apply (le_div_iff₀ hb).mpr
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    nlinarith

lemma fractionalLogMoment_centered {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b : ℝ} (hb : b ≠ 0) {f : X×S → ℝ} (x : X)
    (hI : Integrable (fun s => Real.exp (b*f (x,s))) ν) :
    Integrable (fun s => Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x))) ν ∧
    (∫ s, Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) ∂ν) = 1 := by
  have hp : 0 < ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    apply integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hI |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hfac (s : S) : Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) =
      Real.exp (-(Real.log (∫ t, Real.exp (b*f (x,t)) ∂ν)))*Real.exp (b*f (x,s)) := by
    rw [← Real.exp_add]
    congr 1
    unfold fractionalLogMoment
    field_simp
    ring
  constructor
  · simp_rw [hfac]
    exact hI.const_mul _
  · simp_rw [hfac]
    rw [integral_const_mul,Real.exp_neg,Real.exp_log hp,inv_mul_cancel₀ hp.ne']

lemma finiteCascadeLogRecursion_abs_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} (hH : Measurable H)
    {C : ℝ} (hC : ∀ x, |H x| ≤ C) : ∀ x, |finiteCascadeLogRecursion ν step n z H x| ≤ C := by
  induction n with
  | zero => exact hC
  | succ n ih =>
    exact fractionalLogMoment_abs_le ν (hz 0)
      ((finiteCascadeLogRecursion_measurable ν step hs n (fun i => z i.succ) hH).comp hs)
      (fun p => ih (fun i => z i.succ) (fun i => hz i.succ) (step p))

lemma decoratedTerminalTotalE_telescoping {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (H : X → ℝ)
    (n : ℕ) (z : Fin n → ℝ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotalE step H n p =
      ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step n z H p.1)) *
        decoratedWeightedTotalE step n (finiteCascadeShifts ν step n z H) p := by
  induction n with
  | zero => simp [decoratedTerminalTotalE,finiteCascadeLogRecursion,decoratedWeightedTotalE]
  | succ n ih =>
    conv_lhs => rw [decoratedTerminalTotalE]
    conv_rhs => arg 2; rw [decoratedWeightedTotalE]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro q
    rw [ih (fun i => z i.succ)]
    simp only [finiteCascadeShifts,Fin.cases_zero,Fin.cases_succ]
    have he : ENNReal.ofReal (Real.exp q.1) *
        ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step (p.1,q.2.1)))) =
        ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step (n+1) z H p.1)) *
        ENNReal.ofReal (Real.exp (q.1 + (finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step (p.1,q.2.1)) -
          finiteCascadeLogRecursion ν step (n+1) z H p.1))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add,← Real.exp_add]
      congr 2
      ring
    rw [← mul_assoc,he,mul_assoc]

lemma decoratedTerminalTotalE_zero {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (n : ℕ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotalE step (fun _ => 0) n p = decoratedWeightedTotalE step n (fun _ _ => 0) p := by
  induction n with
  | zero => simp [decoratedTerminalTotalE,decoratedWeightedTotalE]
  | succ n ih =>
    conv_lhs => rw [decoratedTerminalTotalE]
    conv_rhs => rw [decoratedWeightedTotalE]
    apply lintegral_congr
    intro q
    rw [ih]
    simp

lemma decoratedTerminalTotal_telescoping {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (H : X → ℝ)
    (n : ℕ) (z : Fin n → ℝ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotal step H n p =
      Real.exp (finiteCascadeLogRecursion ν step n z H p.1) *
        decoratedWeightedTotal step n (finiteCascadeShifts ν step n z H) p := by
  exact (congrArg ENNReal.toReal (decoratedTerminalTotalE_telescoping ν step H n z p)).trans
    (by rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le]; rfl)

lemma decoratedTerminalTotal_zero {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (n : ℕ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotal step (fun _ => 0) n p = decoratedWeightedTotal step n (fun _ _ => 0) p :=
  congrArg ENNReal.toReal (decoratedTerminalTotalE_zero step n p)

lemma finiteCascadeFractionalIntegrable_of_bounded {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} (hH : Measurable H)
    {C : ℝ} (hC : ∀ x, |H x| ≤ C) : finiteCascadeFractionalIntegrable ν step H n z := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro x
      apply bounded_fractional_exp_integrable ν (hz 0).le
        (((finiteCascadeLogRecursion_measurable ν step hs n (fun j => z j.succ) hH).comp hs).comp
          (measurable_const.prodMk measurable_id))
      exact fun s => finiteCascadeLogRecursion_abs_le ν step hs n (fun j => z j.succ)
        (fun j => hz j.succ) hH hC (step (x,s))
    · exact ih (fun i => z i.succ) (fun i => hz i.succ)

lemma finiteCascadeShifts_normalized_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, z i ≠ 0) (H : X → ℝ)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) : ∀ i x,
    Integrable (fun s => Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s))) ν ∧
    (∫ s, Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s)) ∂ν) = 1 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    rcases hI with ⟨hroot,htail⟩
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) (fun k => hz k.succ) htail j) i
    intro x
    exact fractionalLogMoment_centered ν (hz 0)
      (f := fun p => finiteCascadeLogRecursion ν step n (fun j => z j.succ) H (step p)) x (hroot x)

theorem finiteCascade_terminal_log_recursion_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    (∫ η, Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η)) ∂decoratedCascadeLaw ν n z) =
        finiteCascadeLogRecursion ν step n z H x := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_identity ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_PiMarkLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma decoratedTerminalTotal_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (z : Fin n → ℝ) : Measurable (decoratedTerminalTotal step H n) := by
  have he : decoratedTerminalTotal step H n = fun p =>
      Real.exp (finiteCascadeLogRecursion ν step n z H p.1) *
        decoratedWeightedTotal step n (finiteCascadeShifts ν step n z H) p := by
    funext p
    exact decoratedTerminalTotal_telescoping ν step H n z p
  rw [he]
  exact (((finiteCascadeLogRecursion_measurable ν step hs n z hH).comp measurable_fst).exp).mul
    (decoratedWeightedTotalE_measurable step hs n _ (finiteCascadeShifts_measurable ν step hs n z hH)).ennreal_toReal

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianMarkRecursion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
lemma gaussianLinearMarkStep_measurable (A : ℕ → E →L[ℝ] E) :
    Measurable (gaussianLinearMarkStep A) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply (j+1)).comp measurable_fst).add
    ((A j).measurable.comp measurable_snd)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianMarks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma countableCoordinate_injective {ι : Type*} [Countable ι] :
    Function.Injective (countableCoordinate (ι := ι)) := by
  let := Encodable.ofCountable ι
  exact Encodable.encode_injective

section
variable {V I : Type} [Countable V] [Fintype I]

lemma countableGaussianVectors_measurable : Measurable (countableGaussianVectors (V := V) (I := I)) := by
  apply Measurable.of_eval
  intro v
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  fun_prop

lemma countableGaussianVectors_law :
    countableGaussianLaw.map (countableGaussianVectors (V := V) (I := I)) =
      Measure.infinitePi (fun _ : V => stdGaussian (EuclideanSpace ℝ I)) := by
  let c : (ℕ → ℝ) → V×I → ℝ := fun g p => g (countableCoordinate p)
  have hc : Measurable c := by fun_prop
  have hl : countableGaussianLaw.map c = Measure.infinitePi (fun _ : V×I => gaussianReal 0 1) :=
    Measure.map_infinitePi_infinitePi_of_inj countableCoordinate_injective
  let e := MeasurableEquiv.curry V I ℝ
  have he : countableGaussianVectors (V := V) (I := I) =
      ((fun f v => WithLp.toLp 2 (f v)) ∘ e) ∘ c := rfl
  have hm : Measurable (fun f : V → I → ℝ => fun v => WithLp.toLp 2 (f v)) := by fun_prop
  rw [he,← Measure.map_map (hm.comp e.measurable) hc,hl,
    ← Measure.map_map hm e.measurable]
  rw [show e = MeasurableEquiv.curry V I ℝ from rfl,Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1),
    Measure.infinitePi_map_pi _ (fun _ => (PiLp.continuous_toLp 2 _).measurable)]
  simp only [Measure.infinitePi_eq_pi,map_pi_eq_stdGaussian]

end

lemma indexedGaussianDisorder_measurable (n : ℕ) (I : Type) [Fintype I] :
    Measurable (indexedGaussianDisorder n I) := by
  exact ((measurable_pi_apply (Sum.inl ())).comp (countableGaussianVectors_measurable (V := SharedVertex n) (I := I))).prodMk
    ((indexedMarksFromVertices_measurable n).comp
      ((Measurable.of_eval fun vertex => measurable_pi_apply (Sum.inr vertex)).comp
        (countableGaussianVectors_measurable (V := SharedVertex n) (I := I))))

lemma indexedGaussianDisorder_law (n : ℕ) (I : Type) [Fintype I] :
    countableGaussianLaw.map (indexedGaussianDisorder n I) =
      (stdGaussian (EuclideanSpace ℝ I)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ I)) n) := by
  let E := EuclideanSpace ℝ I
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : SharedVertex n => E)
  let a := Prod.map (fun f : Unit → E => f ()) (indexedMarksFromVertices (S := E) n)
  have ha : Measurable a := (measurable_pi_apply ()).prodMap (indexedMarksFromVertices_measurable n)
  have he : indexedGaussianDisorder n I = (a ∘ e) ∘ countableGaussianVectors (V := SharedVertex n) (I := I) := rfl
  rw [he,← Measure.map_map (ha.comp e.measurable) countableGaussianVectors_measurable,
    countableGaussianVectors_law,← Measure.map_map ha e.measurable,infinitePi_sumPiEquivProdPi]
  rw [← Measure.map_prod_map _ _ (measurable_pi_apply ()) (indexedMarksFromVertices_measurable n),
    Measure.infinitePi_map_eval]
  exact congrArg (Measure.prod (stdGaussian E)) (indexedMarksFromVertices_law (gaussianMarkLaw (E := E)) n)

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E] in
lemma indexedLeafState_gaussianLinear (A : ℕ → E →L[ℝ] E) (n : ℕ)
    (x : ℕ → E) (f : IndexedVertex n → E) (l : IndexedLeaf n) (j : ℕ) :
    indexedLeafState (gaussianLinearMarkStep A) n (x,indexedMarksFromVertices n f) l j =
      x (j+n) + ∑ i : Fin n, A (j+n-1-i.val) (f (indexedLeafVertex n l i)) := by
  induction n generalizing x j with
  | zero => simp [indexedLeafState]
  | succ n ih =>
    change indexedLeafState (gaussianLinearMarkStep A) n
      (gaussianLinearMarkStep A (x,f (l.1,l.2.1,Sum.inl ())),
        indexedMarksFromVertices n (fun v => f (l.1,l.2.1,Sum.inr v))) l.2.2 j = _
    rw [ih,Fin.sum_univ_succ]
    simp only [gaussianLinearMarkStep,indexedLeafVertex,Fin.cases_zero,Fin.cases_succ,
      Fin.val_zero,Fin.val_succ,Nat.sub_zero]
    rw [show j+(n+1)-1 = j+n by omega]
    have he : (∑ i : Fin n, A (j+n-1-i.val) (f (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 i)))) =
        ∑ i : Fin n, A (j+n-(i.val+1)) (f (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      omega
    rw [he]
    simp only [add_assoc]

end

lemma indexedLeafSharedVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafSharedVertex n l) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [indexedLeafSharedVertex] at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [indexedLeafSharedVertex] at hij
    | succ j =>
      simpa only [Fin.succ_inj] using indexedLeafVertex_injective n l
        (by simpa [indexedLeafSharedVertex] using hij)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteGaussianRow
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {K : Type*} [Fintype K]

lemma finiteGaussianRow_key {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (k : K) :
    finiteGaussianRow key a (key k) = a k := by
  classical
  simp [finiteGaussianRow,hk.eq_iff]

lemma finiteGaussianRow_zero {key : K → ℕ} (a : K → ℝ) (i : ℕ)
    (hi : ∀ k, key k ≠ i) : finiteGaussianRow key a i = 0 := by
  simp [finiteGaussianRow,hi]

lemma finiteGaussianRow_key_lt (key : K → ℕ) (k : K) :
    key k < finiteGaussianRowLength key :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))

lemma finiteGaussianRow_tail (key : K → ℕ) (a : K → ℝ) (i : ℕ)
    (hi : finiteGaussianRowLength key ≤ i) : finiteGaussianRow key a i = 0 := by
  apply finiteGaussianRow_zero a i
  intro k
  have h := finiteGaussianRow_key_lt key k
  omega

lemma finiteGaussianRow_sum {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ)
    (F : ℕ → ℝ → ℝ) (hF : ∀ i, F i 0 = 0) :
    (∑ i : Fin (finiteGaussianRowLength key), F i.val (finiteGaussianRow key a i.val)) =
      ∑ k, F (key k) (a k) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => F i (finiteGaussianRow key a i))]
  have hs : Finset.univ.image key ⊆ Finset.range (finiteGaussianRowLength key) := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (finiteGaussianRow_key_lt key k)
  rw [← Finset.sum_subset hs]
  · rw [Finset.sum_image hk.injOn]
    simp_rw [finiteGaussianRow_key hk]
  · intro i hi hi'
    rw [finiteGaussianRow_zero a i,hF]
    intro k hki
    exact hi' (Finset.mem_image.mpr ⟨k,Finset.mem_univ k,hki⟩)

lemma finiteGaussianRow_field {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (g : ℕ → ℝ) :
    (∑ i : Fin (finiteGaussianRowLength key), g i.val*finiteGaussianRow key a i.val) =
      ∑ k, g (key k)*a k :=
  finiteGaussianRow_sum hk a (fun i x => g i*x) (fun _ => mul_zero _)

end
variable {I : Type} [Fintype I]

lemma indexedGaussianRowKey_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedGaussianRowKey (I := I) n l) := by
  intro a b hab
  have h := countableCoordinate_injective hab
  exact Prod.ext (indexedLeafSharedVertex_injective n l (congrArg Prod.fst h)) (congrArg (fun q : SharedVertex n × I => q.2) h)

variable {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_field (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (g : ℕ → ℝ) (x : S×IndexedLeaf n) :
    countableGaussianField (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) g x =
      ∑ d : Fin (n+1), ∑ i : I,
        g (countableCoordinate (indexedLeafSharedVertex n x.2 d,i))* (B d i * V x.1 i) := by
  rw [countableGaussianField,gaussianPrefixField]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    g i.val * finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i.val) = _
  rw [finiteGaussianRow_field (indexedGaussianRowKey_injective n x.2),Fintype.sum_prod_type]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedDiagonalField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_diagonal_identity (n : ℕ) (root : I → ℝ) (step : ℕ → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (g : ℕ → ℝ) (x : S×IndexedLeaf n) :
    countableGaussianField (indexedGaussianRow n (hierarchyRowCoefficients n root step) V)
      (indexedGaussianRowLength (I := I) n) g x =
    inner ℝ (V x.1) (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
      ((fun _ => diagonalMark root (indexedGaussianDisorder n I g).1),
        (indexedGaussianDisorder n I g).2) x.2 0) := by
  rw [indexedGaussianRow_field]
  change _ = inner ℝ (V x.1) (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
    ((fun _ => diagonalMark root (countableGaussianVectors g (Sum.inl ()))),
      indexedMarksFromVertices n (fun v => countableGaussianVectors g (Sum.inr v))) x.2 0)
  rw [indexedLeafState_gaussianLinear,inner_add_right,inner_sum,Fin.sum_univ_succ]
  simp only [Nat.zero_add,hierarchyRowCoefficients,Fin.cases_zero,Fin.cases_succ,
    indexedLeafSharedVertex]
  congr 1
  · simp only [PiLp.inner_apply,diagonalMark_apply,countableGaussianVectors]
    apply Finset.sum_congr rfl
    intro i hi
    change _ = (root i * g (countableCoordinate (Sum.inl (),i))) * V x.1 i
    ring
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [PiLp.inner_apply,diagonalMark_apply,countableGaussianVectors]
    apply Finset.sum_congr rfl
    intro i hi
    change _ = (step (n-1-d.val) i * g (countableCoordinate (Sum.inr (indexedLeafVertex n x.2 d),i))) * V x.1 i
    ring

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedLeafTotal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma decoratedTerminalTotalE_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) : Measurable (decoratedTerminalTotalE step H n) := by
  have he : decoratedTerminalTotalE step H n = fun p =>
      ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step n (fun _ => 0) H p.1)) *
        decoratedWeightedTotalE step n (finiteCascadeShifts ν step n (fun _ => 0) H) p := by
    funext p
    exact decoratedTerminalTotalE_telescoping ν step H n (fun _ => 0) p
  rw [he]
  exact (((finiteCascadeLogRecursion_measurable ν step hs n _ hH).comp measurable_fst).exp.ennreal_ofReal).mul
    (decoratedWeightedTotalE_measurable step hs n _ (finiteCascadeShifts_measurable ν step hs n _ hH))

lemma indexedLeafMeasure_terminal_identity {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (m : IndexedCascadeMarks S n) (x : X) :
    decoratedTerminalTotalE step H n (x,indexedCascadeRealize n (b,m)) =
      ∫⁻ l, ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))) ∂indexedLeafMeasure n b := by
  induction n generalizing x with
  | zero =>
    rw [indexedLeafMeasure_lintegral]
    simp [decoratedTerminalTotalE,indexedLeafWeight,indexedLeafState,IndexedLeaf]
  | succ n ih =>
    rw [decoratedTerminalTotalE,indexedCascadeGood_countKernel hb]
    unfold indexedCascadeRealize
    dsimp only [Prod.fst,Prod.snd]
    have hm : Measurable (fun q : ℝ×(S×DecoratedCascade S n) => ENNReal.ofReal (Real.exp q.1) *
        decoratedTerminalTotalE step H n (step (x,q.2.1),q.2.2)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedTerminalTotalE_measurable ν hs hH n).comp (by fun_prop))
    rw [indexedPoissonMeasure_lintegral _ hm,
      indexedLeafMeasure_lintegral_succ]
    apply tsum_congr
    intro i
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    exact ih (((b i).2 j.val).2) (hb.2 i j.val) (m i j.val).2 (step (x,(m i j.val).1))

lemma indexedLeafMeasure_regular (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    ∀ᵐ b ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)),
      0 < ((indexedLeafMeasure n b) univ).toReal := by
  let ν : ProbabilityMeasure Unit := ⟨Measure.dirac (),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let step : Unit×Unit → Unit := fun _ => ()
  have hs : Measurable step := measurable_const
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks Unit n))
  let D := (decoratedCascadeLaw ν n z : Measure (DecoratedCascade Unit n))
  have hi := decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i x; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i x; simp) ()
  have hp := hi.symm.ae_snd measurableSet_Ioi (cascadeTotal_regular n z hz hz0 hz1).1
  have hR : MeasurePreserving (indexedCascadeRealize (S := Unit) n) (B.prod M) D :=
    ⟨indexedCascadeRealize_measurable n,indexedCascadeRealize_law ν n z⟩
  have ht := hR.quasiMeasurePreserving.ae hp
  have hg : ∀ᵐ p ∂B.prod M, IndexedCascadeGood n p.1 :=
    (measurePreserving_fst (μ := B) (ν := M)).quasiMeasurePreserving.ae (indexedCascadeGood_ae n z hz0 hz1)
  have he : ∀ᵐ p ∂B.prod M, 0 < ((indexedLeafMeasure n p.1) univ).toReal := by
    filter_upwards [ht,hg] with p hp hg
    have h := indexedLeafMeasure_terminal_identity ν hs (H := fun _ => 0) measurable_const n p.1 hg p.2 ()
    simp only [decoratedTerminalTotalE_zero,Real.exp_zero,ENNReal.ofReal_one,lintegral_one] at h
    change 0 < (decoratedWeightedTotalE step n (fun _ _ => 0) ((),indexedCascadeRealize n p)).toReal at hp
    rwa [← h]
  exact (Measure.ae_ae_of_ae_prod he).mono fun b hb => hb.exists.choose_spec

lemma indexedLeafProbability_lintegral (n : ℕ) (b : IndexedCascadeBase n)
    (hb : 0 < ((indexedLeafMeasure n b) univ).toReal) (f : IndexedLeaf n → ℝ≥0∞) :
    (∫⁻ l, f l ∂indexedLeafProbability n b) =
      ((indexedLeafMeasure n b) univ)⁻¹ * ∫⁻ l, f l ∂indexedLeafMeasure n b := by
  rw [indexedLeafProbability,ite_eq_left hb,lintegral_smul_measure,smul_eq_mul]

lemma indexedLeafProbability_terminal_identity {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (hb' : 0 < ((indexedLeafMeasure n b) univ).toReal)
    (m : IndexedCascadeMarks S n) (x : X) :
    (∫⁻ l, ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))) ∂indexedLeafProbability n b) =
      ((indexedLeafMeasure n b) univ)⁻¹ *
        decoratedTerminalTotalE step H n (x,indexedCascadeRealize n (b,m)) := by
  rw [indexedLeafProbability_lintegral n b hb',indexedLeafMeasure_terminal_identity ν hs hH n b hb]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedGibbsPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace SphericalPerceptronFreeEnergy

lemma indexedLeafProbability_terminal_integral {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (hb' : 0 < ((indexedLeafMeasure n b) univ).toReal)
    (m : IndexedCascadeMarks S n) (x : X) :
    (∫ l, Real.exp (H (indexedLeafState step n (x,m) l)) ∂indexedLeafProbability n b) =
      decoratedTerminalTotal step H n (x,indexedCascadeRealize n (b,m)) /
        decoratedTerminalTotal step (fun _ => 0) n (x,indexedCascadeRealize n (b,m)) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (measurable_of_countable _).aestronglyMeasurable,
    indexedLeafProbability_terminal_identity ν hs hH n b hb hb',ENNReal.toReal_mul,ENNReal.toReal_inv]
  have he := indexedLeafMeasure_terminal_identity ν hs (H := fun _ => 0) measurable_const n b hb m x
  simp only [Real.exp_zero,ENNReal.ofReal_one,lintegral_one] at he
  unfold decoratedTerminalTotal
  rw [he,div_eq_mul_inv,mul_comm]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma finite_profile_telescope {k : ℕ} (q : Fin (k+1) → ℝ) :
    q 0 + ∑ i : Fin k, (q i.succ-q i.castSucc) = q (Fin.last k) := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

lemma profileGaussian_coefficient {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) :
    hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) =
      Fin.cases (fun i => Real.sqrt (q 0 i))
        (fun l i => Real.sqrt (q l.succ i-q l.castSucc i)) := by
  funext l i
  induction l using Fin.cases with
  | zero => rfl
  | succ l =>
    simp only [hierarchyRowCoefficients,Fin.cases_succ,profileGaussianStep,
      dite_eq_left (show k-1-l.val<k by omega)]
    congr 2 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_succ,Fin.val_castSucc] <;> omega

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedAncestry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma indexedLeafVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin n) :
    indexedVertexDepth n (indexedLeafVertex n l i) = i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [indexedLeafVertex,Fin.cases_succ,indexedVertexDepth] using congrArg Fin.succ (ih l.2.2 i)

lemma indexedLeafSharedVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin (n+1)) :
    indexedSharedVertexDepth n (indexedLeafSharedVertex n l i) = i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => simpa only [indexedLeafSharedVertex,Fin.cases_succ,indexedSharedVertexDepth] using
      congrArg Fin.succ (indexedLeafVertex_depth n l i)

lemma indexedCommonDepth_self (n : ℕ) (l : IndexedLeaf n) :
    indexedCommonDepth n l l = Fin.last n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [indexedCommonDepth,ih]

lemma indexedLeafVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin n) :
    indexedLeafVertex n l i=indexedLeafVertex n m i ↔ i.val< (indexedCommonDepth n l m).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    by_cases he : l.1=m.1 ∧ l.2.1=m.2.1
    · rcases he with ⟨h1,h2⟩
      rw [indexedCommonDepth,ite_eq_left ⟨h1,h2⟩]
      induction i using Fin.cases with
      | zero => simp [indexedLeafVertex,h1,h2]
      | succ i =>
        simpa [indexedLeafVertex,h1,h2] using ih l.2.2 m.2.2 i
    · rw [indexedCommonDepth,ite_eq_right he]
      induction i using Fin.cases <;> simp_all [indexedLeafVertex,Prod.mk.injEq]

lemma indexedLeafSharedVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m i ↔ i ≤ indexedCommonDepth n l m := by
  induction i using Fin.cases with
  | zero => simp [indexedLeafSharedVertex]
  | succ i =>
    simpa only [indexedLeafSharedVertex,Fin.cases_succ,Sum.inr.injEq,
      Fin.le_iff_val_le_val,Fin.val_succ,Nat.succ_le_iff] using indexedLeafVertex_eq_iff n l m i

lemma indexedLeafSharedVertex_eq_iff_pair (n : ℕ) (l m : IndexedLeaf n) (i j : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m j ↔ i=j ∧ i ≤ indexedCommonDepth n l m := by
  constructor
  · intro h
    have he : i=j := by
      have hh := congrArg (indexedSharedVertexDepth n) h
      simpa only [indexedLeafSharedVertex_depth] using hh
    subst j
    exact ⟨rfl,(indexedLeafSharedVertex_eq_iff n l m i).mp h⟩
  · rintro ⟨rfl,h⟩
    exact (indexedLeafSharedVertex_eq_iff n l m i).mpr h

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_eventually_eq (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) :
    ∀ᶠ n in atTop, gaussianPrefixCovariance v w L n x y=countableGaussianCovariance v w L x y := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn
  unfold gaussianPrefixCovariance countableGaussianCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) n]
  have he (i : ℕ) : maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y =
      if i<L x then w i x*maskedGaussianCoefficient v L i y else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_range_cutoff,min_eq_right hn]
  unfold gaussianPrefixCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) (L x)]
  simp_rw [he,sum_range_cutoff,min_self]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_mask (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (i : ℕ) (x : S×IndexedLeaf n) :
    maskedGaussianCoefficient (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) i x =
      indexedGaussianRow n B V i x := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · rfl
  · exact (finiteGaussianRow_tail _ _ i (Nat.le_of_not_gt hi)).symm

lemma indexedGaussianRowKey_eq (n : ℕ) (l m : IndexedLeaf n) (a b : Fin (n+1)×I) :
    indexedGaussianRowKey n m b = indexedGaussianRowKey n l a ↔
      b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n m l := by
  rw [indexedGaussianRowKey,indexedGaussianRowKey,countableCoordinate_injective.eq_iff,
    Prod.mk.injEq,indexedLeafSharedVertex_eq_iff_pair]
  constructor
  · rintro ⟨⟨he,hc⟩,hi⟩
    exact ⟨he,hi,he ▸ hc⟩
  · rintro ⟨he,hi,hc⟩
    exact ⟨⟨he,he.symm ▸ hc⟩,hi⟩

omit [MeasurableSpace S] in
lemma indexedGaussianRow_cross_value (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) (a : Fin (n+1)×I) :
    indexedGaussianRow n B V (indexedGaussianRowKey n x.2 a) y =
      if a.1 ≤ indexedCommonDepth n y.2 x.2 then B a.1 a.2*V y.1 a.2 else 0 := by
  classical
  unfold indexedGaussianRow finiteGaussianRow
  simp_rw [indexedGaussianRowKey_eq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hd : ¬ (b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n y.2 x.2) := by
      rintro ⟨h1,h2,_⟩
      exact hba (Prod.ext h1 h2)
    simp [hd]
  · simp

omit [MeasurableSpace S] in
lemma indexedGaussianRow_covariance (n : ℕ) (B C : Fin (n+1) → I → ℝ)
    (V W : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n B V) (indexedGaussianRow n C W)
      (indexedGaussianRowLength (I := I) n) x y =
      ∑ i : I, (∑ j : Fin (n+1), if j ≤ indexedCommonDepth n y.2 x.2 then C j i*B j i else 0)*W x.1 i*V y.1 i := by
  classical
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [indexedGaussianRow_mask]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => C p.1 p.2*W x.1 p.2) i.val*
      indexedGaussianRow n B V i.val y) = _
  rw [finiteGaussianRow_sum (indexedGaussianRowKey_injective n x.2) _
    (fun i z => z*indexedGaussianRow n B V i y) (fun i => zero_mul _)]
  simp_rw [indexedGaussianRow_cross_value]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

end

lemma finite_profile_prefix {k : ℕ} (q : Fin (k+1) → ℝ) (a : Fin (k+1)) :
    q 0 + ∑ j : Fin k, (if j.succ ≤ a then q j.succ-q j.castSucc else 0) = q a := by
  have he (j : Fin k) : (if j.succ ≤ a then q j.succ-q j.castSucc else 0) =
      q (min j.succ a)-q (min j.castSucc a) := by
    by_cases hj : j.succ ≤ a
    · rw [ite_eq_left hj,min_eq_left hj,min_eq_left ((Fin.castSucc_le_succ j).trans hj)]
    · have hc : a ≤ j.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ] at *
        omega
      rw [ite_eq_right hj,min_eq_right (le_of_not_ge hj),min_eq_right hc,sub_self]
  simp_rw [he]
  simpa only [min_eq_left (Fin.zero_le a),min_eq_right (Fin.le_last a)] using
    finite_profile_telescope (fun l => q (min l a))

lemma profileGaussian_coefficient_prefix {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (a : Fin (k+1)) (i : I) :
    (∑ l : Fin (k+1), if l ≤ a then
      hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2 else 0) = q a i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.zero_le,ite_true,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (Fin.castSucc_le_succ j)))
  simp_rw [he]
  exact finite_profile_prefix (fun l => q l i) a

lemma profileGaussianRow_covariance {I S : Type} [Fintype I] [MeasurableSpace S]
    {k : ℕ} (q : Fin (k+1) → I → ℝ) (h0 : ∀ i, 0 ≤ q 0 i)
    (hq : ∀ i, Monotone (fun l => q l i)) (V W : S → EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V)
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) W)
      (indexedGaussianRowLength (I := I) k) x y =
      ∑ i : I, q (indexedCommonDepth k y.2 x.2) i*W x.1 i*V y.1 i := by
  rw [indexedGaussianRow_covariance]
  simp_rw [← sq,profileGaussian_coefficient_prefix q h0 hq]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LocalMaxSecondDerivNonpos
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_log_partition_bound {H : S → ℝ} (hH : Measurable H)
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) :
    |Real.log (tiltPartition μ H 1)| ≤ A := by
  have hp := tilt_partition_pos μ hH hA hHA 1
  have hi : Integrable (fun x => Real.exp (H x)) μ := by
    simpa only [one_mul,mul_one] using tilt_integrable μ (F := fun _ => 1) hH measurable_const hA (by norm_num : (0:ℝ) ≤ 1) hHA (fun _ => by norm_num) 1
  have hlo : Real.exp (-A) ≤ tiltPartition μ H 1 := by
    calc
      _ = ∫ _ : S, Real.exp (-A) ∂μ := by simp
      _ ≤ _ := by simpa only [tiltPartition,one_mul] using integral_mono (integrable_const _) hi (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).1)
  have hhi : tiltPartition μ H 1 ≤ Real.exp A := by
    calc
      _ ≤ ∫ _ : S, Real.exp A ∂μ := by simpa only [tiltPartition,one_mul] using integral_mono hi (integrable_const _) (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).2)
      _ = _ := by simp
  exact abs_le.mpr ⟨by simpa using Real.log_le_log (Real.exp_pos (-A)) hlo,by simpa using Real.log_le_log hp hhi⟩

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_IntegrableReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_exp_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    Integrable (fun x : Fin n → S => Real.exp (t*replicaPotential H n x))
      (Measure.pi fun _ : Fin n => μ) := by
  simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  exact Integrable.fintype_prod (fun _ => hi)

omit [IsProbabilityMeasure μ] in
lemma tilt_law_apply_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ H t s = (ENNReal.ofReal (tiltPartition μ H t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * H x) ∂μ) := by
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi_of_integrable {H : S → ℝ} (hH : Measurable H) {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential H n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ H t) := by
  let := tilt_law_probability_of_integrable μ hi
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply_of_integrable _ (replica_exp_integrable μ hi n) (MeasurableSet.univ_pi hs),
    replica_partition μ hH n,ENNReal.ofReal_pow (tilt_partition_pos_of_integrable μ hi).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential H n x) =
      ∏ i, Real.exp (t * H (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * H x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply_of_integrable μ hi (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

lemma gibbsReplicaMean_integral_of_integrable {H : S → ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (n : ℕ) (G : (Fin n → S) → ℝ) :
    gibbsReplicaMean μ H n G = ∫ x, G x ∂Measure.pi (fun _ : Fin n => tiltLaw μ H 1) := by
  rw [← tilt_law_pi_of_integrable μ hH (by simpa only [one_mul] using hi),
    tilt_law_integral_of_integrable _ (replicaPotential_measurable hH n)
      (replica_exp_integrable μ (by simpa only [one_mul] using hi) n)]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ContactGGRate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (H : A → S → ℝ)

lemma gibbsProbabilityKernel_replica_integral (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) (G : (Fin r → S) → ℝ) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) =
      gibbsReplicaMean (κ a) (H a) r G := by
  rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
  exact (gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi r G).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelInfiniteReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma infiniteReplica_prefix_preserving (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i : Fin r => x i.val)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin r => μ)) := by
  let e : (Finset.range r) ≃ Fin r :=
    { toFun := fun i => ⟨i.val,Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : MeasurePreserving ((Finset.range r).restrict : (ℕ → S) → (Finset.range r) → S)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : (Finset.range r) => μ)) :=
    ⟨by fun_prop,Measure.infinitePi_map_restrict _⟩
  have he := measurePreserving_piCongrLeft (fun _ : Fin r => μ) e
  exact he.comp hp

lemma kernelInfiniteReplica_prefix_integral (a : A) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) :
    (∫ x, G (fun i => x i.val) ∂kernelInfiniteReplica κ ℕ a) =
      ∫ x, G x ∂Measure.pi (fun _ : Fin r => κ a) := by
  have hp := infiniteReplica_prefix_preserving (κ a) r
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hG.aestronglyMeasurable]
  rfl

end
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_prefix_integral (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) ∂P := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val)) :=
    hG.comp (by fun_prop)
  have hi : Integrable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using hGB (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => kernelInfiniteReplica_prefix_integral _ a r hG

lemma annealedInfiniteReplica_gibbs_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P := by
  rw [annealedInfiniteReplica_prefix_integral κ P H hH r hG hGB]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r G

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compact_moment_limit {a b : ℝ} (μ : ℕ→ProbabilityMeasure (Icc a b))
    (mom : ℕ→ℝ)
    (hmom : ∀ r, Tendsto (fun n => ∫ x, x.val^r ∂(μ n : Measure (Icc a b))) atTop (𝓝 (mom r))) :
    ∃ ν : ProbabilityMeasure (Icc a b), Tendsto μ atTop (𝓝 ν) ∧
      ∀ r, (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
  obtain ⟨ν, -, s, hs, hsub⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  have hm r : (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
    let F : Icc a b→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => x.val^r,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hsub
    have h₂ := (hmom r).comp hs.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨ν,?_,hm⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  apply integral_continuous_tendsto_of_moments (fun n => (μ n : Measure (Icc a b)))
    (ν : Measure (Icc a b)) (fun r => ?_) F.toContinuousMap
  rw [hm]
  exact hmom r


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LeafFreshLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

lemma freshRoot_swap_nested {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun t : A×(B×C) => (t.2.1,(t.1,t.2.2)))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  have h₁ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ν ρ)
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
    (MeasurePreserving.id ρ)
  exact (measurePreserving_prodAssoc ν μ ρ).comp (h₂.comp h₁)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_AnnealedMarkedReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace SphericalPerceptronFreeEnergy
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_marked_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : A→(Fin r→S)→ℝ}
    (hG : Measurable (Function.uncurry G)) {B : ℝ} (hGB : ∀ a x,|G a x|≤B) :
    (∫ a,G a.1 (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH)=
      ∫ a,gibbsReplicaMean (κ a) (H a) r (G a) ∂P := by
  let := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val)) :=
    hG.comp (measurable_fst.prodMk (by fun_prop))
  have hi : Integrable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using hGB a.1 (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  rw [kernelInfiniteReplica_prefix_integral _ a r hG.of_uncurry_left]
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r (G a)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

lemma bulkMarkedArray_block (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :
    (∫ Q,F (compactBlock r Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=
      bulkReplicaMean n M f.f v r (fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j))) := by
  change (∫ Q,F (compactBlock r Q) ∂Measure.map (bulkMarkedArray n M f K hK)
    (annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
      (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)))=_
  have hm : Measurable (fun Q : CompactArray (BulkPairRange K) => F (compactBlock r Q)) :=
    F.measurable.comp (compactBlock_continuous r).measurable
  rw [integral_map (bulkMarkedArray_measurable n M f K hK).aemeasurable hm.aestronglyMeasurable]
  unfold bulkReplicaMean
  apply annealedInfiniteReplica_marked_prefix (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f.f v)) r
    (G := fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j)))
  · apply F.measurable.comp
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    have hm : Measurable (fun p : BulkDisorder (n+1) M×(Fin r→NormalizedSpin (n+1)) => (p.2 i,p.2 j)) := by fun_prop
    exact ((bulkOverlap_measurable _).comp hm).prodMk
      (((bulkB_measurable _ _ _).comp (measurable_fst.prodMk hm)).subtype_mk)
  · intro a x
    exact F.norm_coe_le_norm _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction BigOperators Matrix

lemma cavityMatrixKernel_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (Ψ : EuclideanSpace ℝ I →ᵇ ℝ) (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    cavityMatrixKernel Ψ C=∫ z,Ψ z ∂multivariateGaussian 0 C :=
  (Classical.choose_spec (cavity_extension_exists Ψ)).2 ⟨C,hC⟩

lemma cavityReplicaTest_apply (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (z : EuclideanSpace ℝ (CavityReplicaIndex n d r)) :
    cavityReplicaTest n d r f Λ hΛ z =
      ∏ j : Fin r, min (sphericalExp n (WithLp.toLp 2 (fun i => z (Sum.inl i,j)))
        (Real.sqrt (n+1:ℕ))) Λ * ∏ t : Fin d,Real.exp (f (z (Sum.inr t,j))) := by
  simp [cavityReplicaTest,cappedSphericalExp,cavityVectorProjection,expBCF]

lemma cavityArrayKernel_tendsto (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ)
    {ν : ℕ→ProbabilityMeasure (CompactArray (BulkPairRange K))}
    {ν₀ : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hν : Tendsto ν atTop (𝓝 ν₀)) :
    Tendsto (fun j => ∫ Q,cavityArrayKernel n d r f Λ hΛ K Q ∂ν j) atTop
      (𝓝 (∫ Q,cavityArrayKernel n d r f Λ hΛ K Q ∂ν₀)) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cavityArrayKernel n d r f Λ hΛ K)).continuousAt.tendsto.comp hν

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGaussianReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Matrix

section

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [Fintype J] [DecidableEq J] in
lemma cavityTestReplica_apply (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ)
    (z : EuclideanSpace ℝ (J×Fin r)) :
    cavityTestReplica Ψ r z=∏ i : Fin r, Ψ (WithLp.toLp 2 (fun j=>z (j,i))) := by
  simp [cavityTestReplica]

theorem cavity_marked_moment {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (v : S→J→E)
    (hv : Measurable v) (W : S→ℝ) (hW : Measurable W) {C : ℝ}
    (hWB : ∀ s,|W s|≤C) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ y,(∫ s,Real.exp (W s)*Ψ (gaussianRows (v s) y) ∂μ)^r ∂stdGaussian E)=
      ∫ xs : Fin r→S,(∏ i,Real.exp (W (xs i)))*
        cavityMatrixKernel (cavityTestReplica Ψ r)
          (Matrix.gram ℝ (fun p : J×Fin r=>v (xs p.2) p.1))
        ∂Measure.pi (fun _=>μ) := by
  let P:=Measure.pi (fun _ : Fin r=>μ)
  let F : E×(Fin r→S)→ℝ:=fun p=>
    ∏ i : Fin r,Real.exp (W (p.2 i))*Ψ (gaussianRows (v (p.2 i)) p.1)
  have hm : Measurable F := by
    apply Finset.measurable_prod
    intro i hi
    have hvi : Measurable (fun p : E×(Fin r→S)=>v (p.2 i)) :=
      hv.comp ((measurable_pi_apply i).comp measurable_snd)
    have hwi : Measurable (fun p : E×(Fin r→S)=>W (p.2 i)) :=
      hW.comp ((measurable_pi_apply i).comp measurable_snd)
    apply hwi.exp.mul
    apply Ψ.measurable.comp
    change Measurable (fun p : E×(Fin r→S)=>WithLp.toLp 2
      (fun j=>inner ℝ (v (p.2 i) j) p.1))
    fun_prop
  have hb p : ‖F p‖≤(Real.exp C*‖Ψ‖)^r := by
    simp only [F,norm_prod,norm_mul]
    calc
      _ ≤ ∏ i : Fin r, Real.exp C * ‖Ψ‖ := by
        apply Finset.prod_le_prod (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
        intro i hi
        apply mul_le_mul _ (Ψ.norm_coe_le_norm _) (norm_nonneg _) (Real.exp_pos C).le
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (abs_le.mp (hWB _)).2
      _ = _ := by simp
  have hi : Integrable F ((stdGaussian E).prod P) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  calc
    _=∫ y,∫ xs : Fin r→S,F (y,xs) ∂P ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with y
      simpa only [F,P,Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι:=Fin r)
          (fun s=>Real.exp (W s)*Ψ (gaussianRows (v s) y)) (μ:=μ)).symm
    _=∫ xs : Fin r→S,∫ y,F (y,xs) ∂stdGaussian E ∂P := integral_integral_swap hi
    _=_ := by
      apply integral_congr_ae
      filter_upwards [] with xs
      have he y : F (y,xs)=(∏ i,Real.exp (W (xs i)))*
          cavityTestReplica Ψ r (gaussianRows (fun p : J×Fin r=>v (xs p.2) p.1) y) := by
        simp only [F,Finset.prod_mul_distrib,cavityTestReplica_apply]
        congr 1
      simp_rw [he]
      rw [integral_const_mul,cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ _),
        ←gaussianRows_map_stdGaussian,
        integral_map (gaussianRows _).continuous.measurable.aemeasurable
          (cavityTestReplica Ψ r).continuous.aestronglyMeasurable]

lemma cavitySingleTest_replica (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    cavityTestReplica (cavitySingleTest n d f Λ hΛ) r=cavityReplicaTest n d r f Λ hΛ := by
  ext z
  simp only [cavityTestReplica_apply,cavitySingleTest_apply,cavityReplicaTest_apply]

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkCoefficients
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityBulkFeature_inner (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x y : NormalizedSpin (m+1)) (j k : Fin (n+1)⊕Fin d) :
    inner ℝ (cavityBulkFeature n d m M f a x j) (cavityBulkFeature n d m M f a y k)=
      if j=k then Sum.elim (fun _=>bulkB (m+1) M f a.1 x y)
        (fun _=>inner ℝ x.val y.val) j else 0 := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,cavityBulkFeature]
  rw [Fintype.sum_prod_type]
  by_cases hjk : j=k
  · subst k
    simp only [ite_true]
    have he (p : Fin (n+1)⊕Fin d) :
        (∑ t : Fin M⊕Fin (m+1),
          (if p=j then cavityBulkBase n d m M f a y j t else 0)*
          (if p=j then cavityBulkBase n d m M f a x j t else 0))=
        if p=j then ∑ t : Fin M⊕Fin (m+1),
          cavityBulkBase n d m M f a y j t*cavityBulkBase n d m M f a x j t else 0 := by
      split_ifs <;> simp_all
    simp_rw [he]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ,ite_true]
    cases j with
    | inl _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inl,mul_zero,Finset.sum_const_zero,add_zero]
      unfold bulkB
      rw [Finset.mul_sum]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
      apply Finset.sum_congr rfl
      intro i _hi
      have hn : (0:ℝ)<(m+1:ℕ) := by positivity
      have hs : Real.sqrt ((m+1:ℕ):ℝ)^2=(m+1:ℕ) := Real.sq_sqrt hn.le
      have hp : Real.sqrt ((m+1:ℕ):ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
      field_simp
      rw [hs]
      ring
    | inr _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rfl
  · rw [ite_eq_right hjk]
    apply Finset.sum_eq_zero
    intro p _hp
    apply Finset.sum_eq_zero
    intro t _ht
    by_cases hpj : p=j
    · subst p
      simp [hjk]
    · simp [hpj]

lemma cavityBulkFeature_gram (n d r m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : Fin r→NormalizedSpin (m+1)) (K : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) :
    Matrix.gram ℝ (fun p : CavityReplicaIndex n d r=>cavityBulkFeature n d m M f a (x p.2) p.1)=
      fun i j=> if i.1=j.1 then
        Sum.elim (fun _=>(bulkMarkedEntry m M f K hK a (x i.2) (x j.2)).2.val)
          (fun _=>(bulkMarkedEntry m M f K hK a (x i.2) (x j.2)).1.val) i.1 else 0 := by
  ext i j
  exact cavityBulkFeature_inner n d m M f a (x i.2) (x j.2) i.1 j.1

lemma cavity_gibbs_moment {S J E : Type*} [MeasurableSpace S]
    [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : S→J→E) (hv : Measurable v) (H : S→ℝ) (hH : Measurable H)
    (he : Integrable (fun x=>Real.exp (H x)) μ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ y,(tiltMean μ H (fun x=>Ψ (gaussianRows (v x) y)) 1)^r ∂stdGaussian E)=
      gibbsReplicaMean μ H r (fun xs=>cavityMatrixKernel (cavityTestReplica Ψ r)
        (Matrix.gram ℝ (fun p : J×Fin r=>v (xs p.2) p.1))) := by
  have he1 : Integrable (fun x=>Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  simp_rw [←tilt_law_integral_of_integrable μ hH he1]
  rw [gibbsReplicaMean_integral_of_integrable μ hH he]
  simpa only [Real.exp_zero,one_mul,Finset.prod_const_one] using
    cavity_marked_moment (tiltLaw μ H 1) v hv (fun _=>0) measurable_const
      (C:=0) (fun _=>by simp) Ψ r

lemma cavityBulkMoment_array (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (K : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) (r : ℕ) :
    cavityBulkMoment n d m M f v Λ hΛ r=
      ∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂bulkMarkedArrayLaw m M f v K hK := by
  let F : CompactBlock (BulkPairRange K) r→ᵇℝ :=
    (cavityMatrixKernel (cavityReplicaTest n d r f.f Λ hΛ)).compContinuous
      ⟨fun Q=>fun i j : CavityReplicaIndex n d r=>if i.1=j.1 then
        Sum.elim (fun _=>(Q i.2 j.2).2.val) (fun _=>(Q i.2 j.2).1.val) i.1 else 0,by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          split_ifs
          · cases i.1 <;> dsimp only [Sum.elim] <;> fun_prop
          · exact continuous_const⟩
  have hb := bulkMarkedArray_block m M f v K hK r F
  change (∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂bulkMarkedArrayLaw m M f v K hK)=_ at hb
  rw [hb]
  unfold cavityBulkMoment bulkReplicaMean
  apply integral_congr_ae
  filter_upwards [] with a
  have he := bulkHamiltonian_exp_integrable m M f.f v a
  have hv : Measurable (cavityBulkFeature n d m M f a) :=
    (cavityBulkFeature_measurable n d m M f).of_uncurry_left
  rw [show (∫ y,cavityBulkPartition n d m M f v Λ hΛ (a,y)^r ∂stdGaussian _)=
      gibbsReplicaMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v a) r
        (fun xs=>cavityMatrixKernel (cavityTestReplica (cavitySingleTest n d f.f Λ hΛ) r)
          (Matrix.gram ℝ (fun p : (Fin (n+1)⊕Fin d)×Fin r=>
            cavityBulkFeature n d m M f a (xs p.2) p.1))) from
      cavity_gibbs_moment _ _ hv _ (bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left he _ r]
  rw [cavitySingleTest_replica]
  apply congrArg (gibbsReplicaMean _ _ r)
  funext xs
  rw [cavityBulkFeature_gram n d r m M f a xs K hK]
  rfl

theorem cavityBulkMoment_tendsto (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
    (r : ℕ) :
    Tendsto (fun j=>cavityBulkMoment n d (s j) (M (s j)) f (v (s j)) Λ hΛ r) atTop
      (𝓝 (∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂ν)) := by
  simp_rw [cavityBulkMoment_array n d _ _ f _ Λ hΛ K (hK _)]
  exact cavityArrayKernel_tendsto n d r f.f Λ hΛ K hlim

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityBulkPartitionLaw_integral (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (F : ℝ→ℝ) (hF : Measurable F) :
    (∫ x,F x.val ∂(cavityBulkPartitionLaw n d m M f v Λ hΛ : Measure (CavityPartitionRange d f.f Λ)))=
      ∫ p,F (cavityBulkPartition n d m M f v Λ hΛ p)
        ∂(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) :=
  integral_map ((cavityBulkPartition_measurable n d m M f v Λ hΛ).subtype_mk).aemeasurable
    (hF.comp measurable_subtype_coe).aestronglyMeasurable

lemma cavityBulkPartition_power_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) :
    Integrable (fun p=>cavityBulkPartition n d m M f v Λ hΛ p^r)
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound ((cavityBulkPartition_measurable n d m M f v Λ hΛ).pow_const r).aestronglyMeasurable
    ((Λ*Real.exp ((d:ℝ)*‖f.f‖))^r)
  filter_upwards [] with p
  have hb:=cavityBulkPartition_mem n d m M f v Λ hΛ p
  rw [norm_pow,Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le hb.1)]
  exact pow_le_pow_left₀ ((Real.exp_pos _).trans_le hb.1).le hb.2 r

lemma cavityBulkPartitionLaw_moment (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) :
    (∫ x,x.val^r ∂(cavityBulkPartitionLaw n d m M f v Λ hΛ : Measure (CavityPartitionRange d f.f Λ)))=
      cavityBulkMoment n d m M f v Λ hΛ r := by
  rw [cavityBulkPartitionLaw_integral n d m M f v Λ hΛ (fun x : ℝ=>x^r) (by fun_prop),
    integral_prod _ (cavityBulkPartition_power_integrable n d m M f v Λ hΛ r)]
  rfl

lemma cavityBulkPartitionLaw_log (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    (∫ x,Real.log x.val ∂(cavityBulkPartitionLaw n d m M f v Λ hΛ : Measure (CavityPartitionRange d f.f Λ)))=
      cavityBulkLog n d m M f v Λ hΛ := by
  rw [cavityBulkPartitionLaw_integral _ _ _ _ _ _ _ _ _ Real.measurable_log]
  change _=∫ a,∫ y,Real.log (cavityBulkPartition n d m M f v Λ hΛ (a,y)) ∂stdGaussian _ ∂_
  apply integral_prod
  apply Integrable.of_bound ((cavityBulkPartition_measurable n d m M f v Λ hΛ).log).aestronglyMeasurable
    ‖cavityPartitionLogTest d f.f Λ‖
  filter_upwards [] with p
  exact (cavityPartitionLogTest d f.f Λ).norm_coe_le_norm
    ⟨cavityBulkPartition n d m M f v Λ hΛ p,cavityBulkPartition_mem n d m M f v Λ hΛ p⟩

theorem cavityBulkLog_tendsto (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (CavityPartitionRange d f.f Λ),
      Tendsto (fun j=>cavityBulkPartitionLaw n d (s j) (M (s j)) f (v (s j)) Λ hΛ) atTop (𝓝 η) ∧
      (∀ r,(∫ x,x.val^r ∂(η : Measure (CavityPartitionRange d f.f Λ)))=∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂ν) ∧
      Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ) atTop
        (𝓝 (∫ x,Real.log x.val ∂(η : Measure (CavityPartitionRange d f.f Λ)))) := by
  have hmom r := cavityBulkMoment_tendsto n d M f v Λ hΛ K hK s hlim r
  simp_rw [←cavityBulkPartitionLaw_moment] at hmom
  obtain ⟨η,hη,hm⟩:=compact_moment_limit _ _ hmom
  refine ⟨η,hη,hm,?_⟩
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cavityPartitionLogTest d f.f Λ)).continuousAt.tendsto.comp hη
  simpa only [Function.comp_def,cavityPartitionLogTest,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
    cavityBulkPartitionLaw_log] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

section Sum
variable {I J : Type} [Fintype I] [Fintype J]
omit [Fintype I] [Fintype J] in
lemma gaussianSumSplit_measurable : Measurable (gaussianSumSplit (I:=I) (J:=J)) := by
  unfold gaussianSumSplit
  fun_prop
lemma gaussianSumSplit_preserving :
    MeasurePreserving (gaussianSumSplit (I:=I) (J:=J)) (stdGaussian (EuclideanSpace ℝ (I⊕J)))
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) := by
  have hI : MeasurePreserving (WithLp.toLp 2 : (I→ℝ)→EuclideanSpace ℝ I)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ I)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hJ : MeasurePreserving (WithLp.toLp 2 : (J→ℝ)→EuclideanSpace ℝ J)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ J)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  refine ⟨gaussianSumSplit_measurable,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map gaussianSumSplit_measurable (PiLp.continuous_toLp 2 _).measurable]
  convert ((hI.prod hJ).comp (measurePreserving_sumPiEquivProdPi (fun _ : I⊕J=>gaussianReal 0 1))).map_eq using 1
  all_goals try with_reducible_and_instances rfl
  rfl
end Sum

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityNormalizedIncrement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_truncated_countable_kernel {S I : Type*} [MeasurableSpace S]
    [Fintype I] [DecidableEq I] (v : ℕ→S→ℝ) (L : S→ℕ)
    (Ψ : EuclideanSpace ℝ I→ᵇℝ) (n : ℕ) (xs : I→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i=>truncatedCountableGaussianField v L n g (xs i)))
      ∂countableGaussianLaw)=
      cavityMatrixKernel Ψ (fun i j=>gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
  let rows : I→EuclideanSpace ℝ (Fin n):=fun i=>
    WithLp.toLp 2 (fun j=>maskedGaussianCoefficient v L j.val (xs i))
  have hg : Matrix.gram ℝ rows=(fun i j=>gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
    ext i j
    change (∑ l : Fin n,maskedGaussianCoefficient v L l.val (xs j)*
      maskedGaussianCoefficient v L l.val (xs i))=_
    exact Finset.sum_congr rfl fun l _=>mul_comm _ _
  rw [←hg,cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ rows),
    ←gaussianRows_map_stdGaussian rows,
    integral_map (gaussianRows rows).continuous.measurable.aemeasurable Ψ.continuous.aestronglyMeasurable,
    ←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  have hp:=gaussianCoordinatePrefix_measurePreserving n
  have hm : AEStronglyMeasurable (fun y : Fin n→ℝ=>Ψ (gaussianRows rows (WithLp.toLp 2 y)))
      (Measure.pi fun _ : Fin n=>gaussianReal 0 1) := by fun_prop
  rw [←hp.map_eq] at hm ⊢
  rw [integral_map hp.measurable.aemeasurable hm]
  apply integral_congr_ae
  exact ae_of_all _ fun g=>rfl

lemma cavity_countable_kernel {S I : Type*} [MeasurableSpace S]
    [Fintype I] [DecidableEq I] (v : ℕ→S→ℝ) (L : S→ℕ)
    (Ψ : EuclideanSpace ℝ I→ᵇℝ) (xs : I→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i=>countableGaussianField v L g (xs i)))
      ∂countableGaussianLaw)=
      cavityMatrixKernel Ψ (fun i j=>countableGaussianCovariance v v L (xs i) (xs j)) := by
  have he : ∀ᶠ n : ℕ in atTop,∀ i : I,∀ g,
      truncatedCountableGaussianField v L n g (xs i)=countableGaussianField v L g (xs i) :=
    Filter.eventually_all.mpr (fun i=>truncatedCountableGaussianField_eventually_eq v L (xs i))
  have hc : ∀ᶠ n : ℕ in atTop,∀ i j : I,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (fun j=>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn,hc⟩:=(he.and hc).exists
  have hh:=cavity_truncated_countable_kernel v L Ψ n xs
  simp_rw [hn,hc] at hh
  exact hh

theorem cavity_countable_moment {S J : Type*} [MeasurableSpace S]
    [Fintype J] [DecidableEq J] [MeasurableSpace J]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (hv : ∀ i,Measurable (v i)) (hL : Measurable L)
    (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ g, (∫ x, Ψ (cavityCountableField v L g x) ∂μ)^r ∂countableGaussianLaw)=
      ∫ xs : Fin r→S,cavityMatrixKernel (cavityTestReplica Ψ r)
        (fun i j : J×Fin r=>countableGaussianCovariance v v L (xs i.2,i.1) (xs j.2,j.1))
          ∂Measure.pi (fun _=>μ) := by
  let F : (ℕ→ℝ)×(Fin r→S)→ℝ:=fun p=>∏ i,Ψ (cavityCountableField v L p.1 (p.2 i))
  have hm : Measurable F := Finset.measurable_prod _ fun i _=>
    Ψ.measurable.comp ((cavityCountableField_measurable v L hv hL).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hb p : ‖F p‖≤‖Ψ‖^r := by
    simp only [F,norm_prod]
    exact (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>Ψ.norm_coe_le_norm _)).trans_eq (by simp)
  have hi : Integrable F (countableGaussianLaw.prod (Measure.pi fun _ : Fin r=>μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  calc
    _=∫ g,∫ xs : Fin r→S,F (g,xs) ∂Measure.pi (fun _=>μ) ∂countableGaussianLaw := by
      apply integral_congr_ae
      exact ae_of_all _ fun g=>by
        simpa only [F,Fintype.card_fin] using
          (integral_fintype_prod_eq_pow (ι:=Fin r) (fun x=>Ψ (cavityCountableField v L g x)) (μ:=μ)).symm
    _=∫ xs : Fin r→S,∫ g,F (g,xs) ∂countableGaussianLaw ∂Measure.pi (fun _=>μ) := integral_integral_swap hi
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ fun xs=>by
        simpa only [cavityTestReplica_apply,cavityCountableField,F] using
          cavity_countable_kernel v L (cavityTestReplica Ψ r) (fun p : J×Fin r=>(xs p.2,p.1))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityDiagonalKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

section

variable {I : Type} [Fintype I] [DecidableEq I]

lemma cavityNoiseRows_gram {n : ℕ} (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ) :
    Matrix.gram ℝ (cavityNoiseRows v σ)=fun i j=>Matrix.gram ℝ v i j+if i=j then σ i^2 else 0 := by
  ext i j
  change (∑ t : Fin n⊕I,Sum.elim (fun t=>v j t) (fun t=>if t=j then σ j else 0) t*
    Sum.elim (fun t=>v i t) (fun t=>if t=i then σ i else 0) t)=_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases h : i=j
  · subst j
    simp only [ite_true]
    simp [Matrix.gram,PiLp.inner_apply,pow_two]
  · simp only [ite_eq_right h,zero_mul]
    rfl

lemma cavityNoiseRows_apply {n : ℕ} (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ)
    (y : EuclideanSpace ℝ (Fin n⊕I)) (i : I) :
    inner ℝ (cavityNoiseRows v σ i) y=
      inner ℝ (v i) (gaussianSumSplit y).1+σ i*(gaussianSumSplit y).2 i := by
  change (∑ t : Fin n⊕I,y t*Sum.elim (fun j=>v i j) (fun j=>if j=i then σ i else 0) t)=_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∑ t : Fin n,y (Sum.inl t)*v i t)+y (Sum.inr i)*σ i=
    (∑ t : Fin n,y (Sum.inl t)*v i t)+σ i*y (Sum.inr i)
  ring

theorem cavityMatrixKernel_diagonal_noise {n : ℕ}
    (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) :
    cavityMatrixKernel Ψ (fun i j=>Matrix.gram ℝ v i j+if i=j then σ i^2 else 0)=
      cavityMatrixKernel (cavityDiagonalAverage σ Ψ) (Matrix.gram ℝ v) := by
  rw [←cavityNoiseRows_gram v σ,
    cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ _),
    ←gaussianRows_map_stdGaussian,
    integral_map (by fun_prop) Ψ.continuous.aestronglyMeasurable]
  let F : EuclideanSpace ℝ (Fin n)×EuclideanSpace ℝ I→ℝ:=fun p=>
    Ψ (WithLp.toLp 2 (fun i=>inner ℝ (v i) p.1+σ i*p.2 i))
  have hm : Measurable F := by fun_prop
  have hi : Integrable F ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ I))) :=
    Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun p=>Ψ.norm_coe_le_norm _)
  have hp:=gaussianSumSplit_preserving (I:=Fin n) (J:=I)
  have he (y : EuclideanSpace ℝ (Fin n⊕I)) : Ψ (gaussianRows (cavityNoiseRows v σ) y)=F (gaussianSumSplit y) := by
    congr 1
    ext i
    exact cavityNoiseRows_apply v σ y i
  simp_rw [he]
  have hmap : (∫ y,F (gaussianSumSplit y) ∂stdGaussian (EuclideanSpace ℝ (Fin n⊕I)))=
      ∫ p,F p ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ I)) := by
    rw [←hp.map_eq,integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable]
  rw [hmap,integral_prod _ hi,
    cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ _),
    ←gaussianRows_map_stdGaussian,
    integral_map (by fun_prop) (cavityDiagonalAverage σ Ψ).continuous.aestronglyMeasurable]
  rfl

theorem cavity_countable_kernel_diagonal_noise {S : Type} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) (xs : I→S) :
    (∫ g,cavityDiagonalAverage σ Ψ (WithLp.toLp 2 (fun i=>countableGaussianField v L g (xs i)))
      ∂countableGaussianLaw)=
    cavityMatrixKernel Ψ (fun i j=>countableGaussianCovariance v v L (xs i) (xs j)+if i=j then σ i^2 else 0) := by
  rw [cavity_countable_kernel]
  have hc : ∀ᶠ n : ℕ in atTop,∀ i j : I,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (fun j=>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn⟩:=hc.exists
  let rows : I→EuclideanSpace ℝ (Fin n):=fun i=>WithLp.toLp 2 (fun j=>maskedGaussianCoefficient v L j.val (xs i))
  have hg : Matrix.gram ℝ rows=(fun i j=>countableGaussianCovariance v v L (xs i) (xs j)) := by
    ext i j
    rw [←hn i j]
    change (∑ l : Fin n,maskedGaussianCoefficient v L l.val (xs j)*
      maskedGaussianCoefficient v L l.val (xs i))=_
    exact Finset.sum_congr rfl fun l _=>mul_comm _ _
  have hh:=cavityMatrixKernel_diagonal_noise rows σ Ψ
  rw [hg] at hh
  exact hh.symm

end

variable {J : Type} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma cavityReplicaSplit_preserving [DecidableEq J] (r : ℕ) :
    MeasurePreserving (cavityReplicaSplit (J:=J) r)
      (stdGaussian (EuclideanSpace ℝ (J×Fin r)))
      (Measure.pi fun _ : Fin r=>stdGaussian (EuclideanSpace ℝ J)) := by
  have ho : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (J×Fin r)→(J×Fin r→ℝ))
      (stdGaussian (EuclideanSpace ℝ (J×Fin r)))
      (Measure.pi fun _ : J×Fin r=>gaussianReal 0 1) := by
    refine ⟨(PiLp.continuous_ofLp 2 _).measurable,?_⟩
    rw [←map_pi_eq_stdGaussian,Measure.map_map (PiLp.continuous_ofLp 2 _).measurable
      (PiLp.continuous_toLp 2 _).measurable]
    exact Measure.map_id
  have hs:=measurePreserving_piCongrLeft (fun _ : Fin r×J=>gaussianReal 0 1) (Equiv.prodComm J (Fin r))
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin r) J ℝ)
      (Measure.pi fun _ : Fin r×J=>gaussianReal 0 1)
      (Measure.pi fun _ : Fin r=>Measure.pi fun _ : J=>gaussianReal 0 1) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable,?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun (_ : Fin r) (_ : J)=>gaussianReal 0 1)
  have ht : MeasurePreserving (WithLp.toLp 2 : (J→ℝ)→EuclideanSpace ℝ J)
      (Measure.pi fun _ : J=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ J)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hp:=measurePreserving_pi (fun _ : Fin r=>Measure.pi fun _ : J=>gaussianReal 0 1)
    (fun _ : Fin r=>stdGaussian (EuclideanSpace ℝ J)) (fun _=>ht)
  convert hp.comp (hc.comp (hs.comp ho)) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma cavityDiagonalAverage_replica (σ : J→ℝ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    cavityDiagonalAverage (fun p : J×Fin r=>σ p.1) (cavityTestReplica Ψ r)=
      cavityTestReplica (cavityDiagonalAverage σ Ψ) r := by
  ext x
  let F : (Fin r→EuclideanSpace ℝ J)→ℝ := fun y=>
    ∏ i : Fin r,Ψ (WithLp.toLp 2 (fun j=>x (j,i)+σ j*y i j))
  have hm : Measurable F := by fun_prop
  have hp:=cavityReplicaSplit_preserving (J:=J) r
  change (∫ z,cavityTestReplica Ψ r (WithLp.toLp 2 (fun p=>x p+σ p.1*z p))
    ∂stdGaussian (EuclideanSpace ℝ (J×Fin r)))=_
  simp only [cavityTestReplica_apply]
  have he (z : EuclideanSpace ℝ (J×Fin r)) :
      (∏ i : Fin r,Ψ (WithLp.toLp 2 (fun j=>(WithLp.toLp 2 (fun p : J×Fin r=>x p+σ p.1*z p)) (j,i))))=
        F (cavityReplicaSplit r z) := rfl
  simp_rw [he]
  rw [←integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]
  exact integral_fintype_prod_eq_prod (fun (i : Fin r) (y : EuclideanSpace ℝ J)=>Ψ (WithLp.toLp 2 (fun j=>x (j,i)+σ j*y j)))

theorem cavity_countable_residual_moment {S : Type} [MeasurableSpace S]
    [MeasurableSpace J] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (hv : ∀ i,Measurable (v i)) (hL : Measurable L)
    (σ : J→ℝ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ g,(∫ x,cavityDiagonalAverage σ Ψ (cavityCountableField v L g x) ∂μ)^r
      ∂countableGaussianLaw)=
      ∫ xs : Fin r→S,cavityMatrixKernel (cavityTestReplica Ψ r)
        (fun p q : J×Fin r=>countableGaussianCovariance v v L (xs p.2,p.1) (xs q.2,q.1)+
          if p=q then σ p.1^2 else 0) ∂Measure.pi (fun _=>μ) := by
  rw [cavity_countable_moment μ v L hv hL,←cavityDiagonalAverage_replica]
  apply integral_congr_ae
  exact ae_of_all _ fun xs=>by
    dsimp only
    rw [←cavity_countable_kernel v L (cavityDiagonalAverage (fun p : J×Fin r=>σ p.1) (cavityTestReplica Ψ r)) (fun p : J×Fin r=>(xs p.2,p.1))]
    exact cavity_countable_kernel_diagonal_noise v L (fun p : J×Fin r=>σ p.1)
      (cavityTestReplica Ψ r) (fun p : J×Fin r=>(xs p.2,p.1))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityIndexedLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_indexed_log_recursion {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (H : X→ℝ) (hH : Measurable H) {C : ℝ} (hC : ∀ x,|H x|≤C)
    (k : ℕ) (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (x : X) :
    (∫ p : IndexedCascadeBase k×IndexedCascadeMarks S k,
      Real.log (∫ l,Real.exp (H (indexedLeafState step k (x,p.2) l))
        ∂indexedLeafProbability k p.1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (indexedCascadeMarksLaw ν k))=
      finiteCascadeLogRecursion ν step k z H x := by
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let M := (indexedCascadeMarksLaw ν k : Measure (IndexedCascadeMarks S k))
  have hb : ∀ᵐ p ∂B.prod M,IndexedCascadeGood k p.1 :=
    (measurePreserving_fst (μ:=B) (ν:=M)).quasiMeasurePreserving.ae
      (indexedCascadeGood_ae k z hz0 hz1)
  have hr : ∀ᵐ p ∂B.prod M,0<((indexedLeafMeasure k p.1) univ).toReal :=
    (measurePreserving_fst (μ:=B) (ν:=M)).quasiMeasurePreserving.ae
      (indexedLeafMeasure_regular k z hz hz0 hz1)
  have he : (fun p : IndexedCascadeBase k×IndexedCascadeMarks S k=>
      Real.log (∫ l,Real.exp (H (indexedLeafState step k (x,p.2) l))
        ∂indexedLeafProbability k p.1))=ᵐ[B.prod M]
      (fun p=>Real.log (decoratedTerminalTotal step H k (x,indexedCascadeRealize k p)/
        decoratedTerminalTotal step (fun _=>0) k (x,indexedCascadeRealize k p))) := by
    filter_upwards [hb,hr] with p hp hpr
    rw [indexedLeafProbability_terminal_integral ν hs hH k p.1 hp hpr p.2 x]
  have hm : Measurable (fun η : DecoratedCascade S k=>
      Real.log (decoratedTerminalTotal step H k (x,η)/decoratedTerminalTotal step (fun _=>0) k (x,η))) :=
    (((decoratedTerminalTotal_measurable ν step hs hH k z).comp (measurable_const.prodMk measurable_id)).div
      ((decoratedTerminalTotal_measurable ν step hs measurable_const k z).comp
        (measurable_const.prodMk measurable_id))).log
  change (∫ p,Real.log (∫ l,Real.exp (H (indexedLeafState step k (x,p.2) l))
    ∂indexedLeafProbability k p.1) ∂B.prod M)=_
  rw [integral_congr_ae he,←integral_map (indexedCascadeRealize_measurable k).aemeasurable hm.aestronglyMeasurable]
  change (∫ η,Real.log (decoratedTerminalTotal step H k (x,η)/
    decoratedTerminalTotal step (fun _=>0) k (x,η))
    ∂(((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
      (indexedCascadeMarksLaw ν k)).map (indexedCascadeRealize k)))=_
  rw [indexedCascadeRealize_law ν k z]
  exact finiteCascade_terminal_log_recursion_of_fractional ν step hs k z hz hz0 hz1 hH
    (finiteCascadeFractionalIntegrable_of_bounded ν step hs k z hz0 hH hC) x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CavityCappedRPC
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityResidualCapped_pos (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (x : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    0 < cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x :=
  (Real.exp_pos _).trans_le (cavityResidualCapped_bounds n d f Λ hΛ σ x).1

lemma cavityResidualCapped_log_bound (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (x : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    |Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x)|≤Real.log Λ+d*‖f‖ := by
  have hb:=cavityResidualCapped_bounds n d f Λ hΛ σ x
  have hp:=cavityResidualCapped_pos n d f Λ hΛ σ x
  have hl:=Real.log_le_log (Real.exp_pos _) hb.1
  have hu:=Real.log_le_log hp hb.2
  rw [Real.log_exp] at hl
  rw [Real.log_mul (by linarith : Λ≠0) (Real.exp_pos _).ne',Real.log_exp] at hu
  exact abs_le.mpr ⟨by linarith [Real.log_nonneg hΛ],hu⟩

theorem cavity_capped_indexed_log_recursion (n d k : ℕ) (f : ℝ→ᵇℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (σ : Fin (n+1)⊕Fin d→ℝ)
    (A : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)⊕Fin d))
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (x : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    (∫ p : IndexedCascadeBase k×IndexedCascadeMarks (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) k,
      Real.log (∫ l,cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
        (indexedLeafState (gaussianLinearMarkStep A) k (x,p.2) l 0)
        ∂indexedLeafProbability k p.1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) k))=
      finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
        (gaussianLinearMarkStep A) k z
        (fun s=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0))) x := by
  have hm : Measurable (fun s : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>
      Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0))) :=
    ((cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)).measurable.comp (measurable_pi_apply 0)).log
  have hh:=cavity_indexed_log_recursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
    (gaussianLinearMarkStep A) (gaussianLinearMarkStep_measurable A)
    (fun s=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0))) hm
    (fun s=>cavityResidualCapped_log_bound n d f Λ hΛ σ (s 0)) k z hz hz0 hz1 x
  simpa only [Real.exp_log (cavityResidualCapped_pos n d f Λ hΛ σ _)] using hh

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelMoment
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

variable {J : Type} [Fintype J] [DecidableEq J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {k : ℕ}

omit [MeasurableSingletonClass J] in
lemma cavityLabel_covariance [MeasurableSingletonClass J] (q : Fin (k+1)→J→ℝ) (h0 : ∀ i,0≤q 0 i)
    (hq : ∀ i,Monotone (fun l=>q l i)) (x y : IndexedLeaf k×J) :
    countableGaussianCovariance (cavityLabelRow q) (cavityLabelRow q) (cavityLabelLength k) x y=
      if x.2=y.2 then q (indexedCommonDepth k y.1 x.1) x.2 else 0 := by
  change countableGaussianCovariance
    (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) cavityLabelBasis)
    (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) cavityLabelBasis)
    (indexedGaussianRowLength (I:=J) k) (x.2,x.1) (y.2,y.1)=_
  rw [profileGaussianRow_covariance q h0 hq]
  simp only [cavityLabelBasis,PiLp.toLp_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases h : x.2=y.2
  · simp [h]
  · simp [h,Ne.symm h]


lemma cavity_label_completed_covariance (q : Fin (k+1)→J→ℝ)
    (h0 : ∀ i,0≤q 0 i) (hq : ∀ i,Monotone (fun l=>q l i))
    (D : J→ℝ) (hD : ∀ i,q (Fin.last k) i≤D i)
    (r : ℕ) (xs : Fin r→IndexedLeaf k) (p t : J×Fin r) :
    countableGaussianCovariance (cavityLabelRow q) (cavityLabelRow q) (cavityLabelLength k)
      (xs p.2,p.1) (xs t.2,t.1)+
      (if p=t then (Real.sqrt (D p.1-q (Fin.last k) p.1))^2 else 0)=
    if p=t then D p.1 else
      if p.1=t.1 then q (indexedCommonDepth k (xs t.2) (xs p.2)) p.1 else 0 := by
  rw [cavityLabel_covariance q h0 hq]
  by_cases h : p=t
  · subst t
    simp only [ite_true,indexedCommonDepth_self,Real.sq_sqrt (sub_nonneg.mpr (hD _))]
    ring
  · simp only [ite_eq_right h,add_zero]

theorem cavity_label_true_diagonal_moment (q : Fin (k+1)→J→ℝ)
    (h0 : ∀ i,0≤q 0 i) (hq : ∀ i,Monotone (fun l=>q l i))
    (D : J→ℝ) (hD : ∀ i,q (Fin.last k) i≤D i)
    (μ : Measure (IndexedLeaf k)) [IsProbabilityMeasure μ]
    (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ g,(∫ x,cavityDiagonalAverage (fun j=>Real.sqrt (D j-q (Fin.last k) j)) Ψ
      (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) g x) ∂μ)^r
      ∂countableGaussianLaw)=
    ∫ xs : Fin r→IndexedLeaf k,cavityMatrixKernel (cavityTestReplica Ψ r)
      (fun p t : J×Fin r=>if p=t then D p.1 else
        if p.1=t.1 then q (indexedCommonDepth k (xs t.2) (xs p.2)) p.1 else 0)
      ∂Measure.pi (fun _=>μ) := by
  simpa only [cavity_label_completed_covariance q h0 hq D hD r] using
    cavity_countable_residual_moment μ (cavityLabelRow q) (cavityLabelLength k)
      (cavityLabelRow_measurable q) (cavityLabelLength_measurable k)
      (fun j=>Real.sqrt (D j-q (Fin.last k) j)) Ψ r


omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma cavityLabelBasis_inner [MeasurableSpace J] [MeasurableSingletonClass J]
    (j : J) (x : EuclideanSpace ℝ J) :
    inner ℝ (cavityLabelBasis j) x=x j := by
  simp [cavityLabelBasis,PiLp.inner_apply]

lemma cavity_label_field_state (q : Fin (k+1)→J→ℝ) (g : ℕ→ℝ) (x : IndexedLeaf k) :
    cavityCountableField (cavityLabelRow q) (cavityLabelLength k) g x=
      indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
        ((fun _=>diagonalMark (profileGaussianRoot q) (indexedGaussianDisorder k J g).1),
          (indexedGaussianDisorder k J g).2) x 0 := by
  ext j
  change countableGaussianField (indexedGaussianRow k
    (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) cavityLabelBasis)
    (indexedGaussianRowLength (I:=J) k) g (j,x)=_
  rw [indexedGaussianRow_diagonal_identity,cavityLabelBasis_inner]


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityLabelPartitionLaw_integral (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) (z : Fin k→ℝ)
    (F : ℝ→ℝ) (hF : Measurable F) :
    (∫ x,F x.val ∂(cavityLabelPartitionLaw n d k f Λ hΛ σ q z : Measure (CavityPartitionRange d f Λ)))=
      ∫ p,F (cavityLabelPartition n d k f Λ hΛ σ q p)
        ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw := by
  exact integral_map ((cavityLabelPartition_measurable n d k f Λ hΛ σ q).subtype_mk).aemeasurable
    (hF.comp measurable_subtype_coe).aestronglyMeasurable

theorem cavityLabelPartitionLaw_moment (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (h0 : ∀ i,0≤q 0 i) (hq : ∀ i,Monotone (fun l=>q l i))
    (D : Fin (n+1)⊕Fin d→ℝ) (hD : ∀ i,q (Fin.last k) i≤D i) (z : Fin k→ℝ) (r : ℕ) :
    (∫ x,x.val^r ∂(cavityLabelPartitionLaw n d k f Λ hΛ
      (fun j=>Real.sqrt (D j-q (Fin.last k) j)) q z : Measure (CavityPartitionRange d f Λ)))=
    ∫ b,∫ xs : Fin r→IndexedLeaf k,cavityMatrixKernel (cavityTestReplica (cavitySingleTest n d f Λ hΛ) r)
      (fun p t : (Fin (n+1)⊕Fin d)×Fin r=>if p=t then D p.1 else
        if p.1=t.1 then q (indexedCommonDepth k (xs t.2) (xs p.2)) p.1 else 0)
      ∂Measure.pi (fun _=>indexedLeafProbability k b) ∂indexedCascadeBaseLaw k z := by
  let σ:=fun j=>Real.sqrt (D j-q (Fin.last k) j)
  let P:=cavityLabelPartition n d k f Λ hΛ σ q
  have hb (p : IndexedCascadeBase k×(ℕ→ℝ)) : ‖P p‖≤Λ*Real.exp ((d:ℝ)*‖f‖) := by
    have hh:=cavityLabelPartition_mem n d k f Λ hΛ σ q p
    rw [Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le hh.1)]
    exact hh.2
  have hi : Integrable (fun p=>P p^r) ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw) :=
    Integrable.of_bound ((cavityLabelPartition_measurable n d k f Λ hΛ σ q).pow_const r).aestronglyMeasurable
      ((Λ*Real.exp ((d:ℝ)*‖f‖))^r) (ae_of_all _ fun p=>by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb p) r)
  rw [cavityLabelPartitionLaw_integral _ _ _ _ _ _ _ _ _ (fun x : ℝ=>x^r) (by fun_prop),integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>cavity_label_true_diagonal_moment q h0 hq D hD
    (indexedLeafProbability k b) (cavitySingleTest n d f Λ hΛ) r


lemma cavityIndexedRootPartition_measurable (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityIndexedRootPartition n d k f Λ hΛ σ q) := by
  let E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)
  let X:=E×(IndexedCascadeBase k×IndexedCascadeMarks E k)
  let κ : Kernel X (IndexedLeaf k):=(indexedLeafKernel k).comap (fun p=>p.2.1) measurable_snd.fst
  have hm0 : Measurable (fun p : X×IndexedLeaf k=>
      indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
        ((fun _=>diagonalMark (profileGaussianRoot q) p.1.1),p.1.2.2) p.2) := by
    have hs := indexedLeafState_measurable
      (gaussianLinearMarkStep_measurable (fun j=>diagonalMark (profileGaussianStep q j))) k
    have hp : Measurable (fun p : X×IndexedLeaf k=>
        (((fun _ : ℕ=>diagonalMark (profileGaussianRoot q) p.1.1),p.1.2.2),p.2)) := by
      have hr : Measurable (fun p : X×IndexedLeaf k=>
          (fun _ : ℕ=>diagonalMark (profileGaussianRoot q) p.1.1)) :=
        Measurable.of_eval fun _=>
          (diagonalMark (profileGaussianRoot q)).measurable.comp measurable_fst.fst
      exact (hr.prodMk measurable_fst.snd.snd).prodMk measurable_snd
    exact hs.comp hp
  have hm : Measurable (fun p : X×IndexedLeaf k=>
      cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
        (indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
          ((fun _=>diagonalMark (profileGaussianRoot q) p.1.1),p.1.2.2) p.2 0)) :=
    (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)).measurable.comp
      ((measurable_pi_apply 0).comp hm0)
  exact (hm.stronglyMeasurable.integral_kernel_prod_right (κ:=κ)
    (f:=fun p l=>cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
      (indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
        ((fun _=>diagonalMark (profileGaussianRoot q) p.1),p.2.2) l 0))).measurable

lemma cavityIndexedRootPartition_log_bound (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)×
      (IndexedCascadeBase k×IndexedCascadeMarks (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) k)) :
    |Real.log (cavityIndexedRootPartition n d k f Λ hΛ σ q p)|≤Real.log Λ+d*‖f‖ := by
  let V : IndexedLeaf k→_:=fun l=>indexedLeafState
    (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
      ((fun _=>diagonalMark (profileGaussianRoot q) p.1),p.2.2) l 0
  have hh:=tilt_log_partition_bound (indexedLeafProbability k p.2.1)
    (H:=fun l=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (V l)))
    (measurable_of_countable _) (add_nonneg (Real.log_nonneg hΛ) (by positivity))
    (fun l=>cavityResidualCapped_log_bound n d f Λ hΛ σ (V l))
  simpa only [tiltPartition,one_mul,Real.exp_log (cavityResidualCapped_pos n d f Λ hΛ σ _),
    cavityIndexedRootPartition,V] using hh

lemma cavityIndexedRoot_disorder_preserving (k : ℕ) (J : Type) [Fintype J] (z : Fin k→ℝ) :
    MeasurePreserving
      (fun p : IndexedCascadeBase k×(ℕ→ℝ)=>
        ((indexedGaussianDisorder k J p.2).1,(p.1,(indexedGaussianDisorder k J p.2).2)))
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)
      ((stdGaussian (EuclideanSpace ℝ J)).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) k))) := by
  have hg : MeasurePreserving (indexedGaussianDisorder k J) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ J)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) k)) :=
    ⟨indexedGaussianDisorder_measurable k J,indexedGaussianDisorder_law k J⟩
  exact (freshRoot_swap_nested _ _ _).comp ((MeasurePreserving.id _).prod hg)

theorem cavityLabelPartitionLaw_log_recursion (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) :
    (∫ x,Real.log x.val ∂(cavityLabelPartitionLaw n d k f Λ hΛ σ q z : Measure (CavityPartitionRange d f Λ)))=
    ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
      (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k z
      (fun s=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0)))
      (fun _=>diagonalMark (profileGaussianRoot q) y) ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) := by
  let F:=fun p=>Real.log (cavityIndexedRootPartition n d k f Λ hΛ σ q p)
  have hm : Measurable F := (cavityIndexedRootPartition_measurable n d k f Λ hΛ σ q).log
  have hp:=cavityIndexedRoot_disorder_preserving k (Fin (n+1)⊕Fin d) z
  have hi : Integrable F ((stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))).prod
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) k))) :=
    Integrable.of_bound hm.aestronglyMeasurable (Real.log Λ+d*‖f‖) (ae_of_all _ fun p=>by
      simpa only [Real.norm_eq_abs] using cavityIndexedRootPartition_log_bound n d k f Λ hΛ σ q p)
  rw [cavityLabelPartitionLaw_integral _ _ _ _ _ _ _ _ _ Real.log Real.measurable_log]
  have he (p : IndexedCascadeBase k×(ℕ→ℝ)) :
      Real.log (cavityLabelPartition n d k f Λ hΛ σ q p)=
        F ((indexedGaussianDisorder k (Fin (n+1)⊕Fin d) p.2).1,
          (p.1,(indexedGaussianDisorder k (Fin (n+1)⊕Fin d) p.2).2)) := by
    unfold cavityLabelPartition F cavityIndexedRootPartition
    simp_rw [cavity_label_field_state]
  simp_rw [he]
  rw [←integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq,integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun y=>cavity_capped_indexed_log_recursion n d k f Λ hΛ σ
    (fun j=>diagonalMark (profileGaussianStep q j)) z hz hz0 hz1
    (fun _=>diagonalMark (profileGaussianRoot q) y)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityLabelMarkedLaw_block {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) (z : Fin k→ℝ) (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :
    (∫ Q,F (compactBlock r Q) ∂(cavityLabelMarkedLaw p D z : Measure (CompactArray (BulkPairRange K))))=
      ∫ b,∫ xs : Fin r→IndexedLeaf k,F (fun i j=>if i=j then D else
        p (indexedCommonDepth k (xs j) (xs i)))
        ∂Measure.pi (fun _=>indexedLeafProbability k b) ∂indexedCascadeBaseLaw k z := by
  let G : (Fin r→IndexedLeaf k)→ℝ:=fun xs=>F (fun i j=>if i=j then D else
    p (indexedCommonDepth k (xs j) (xs i)))
  have hG : Measurable G:=measurable_of_countable _
  have hGB (xs : Fin r→IndexedLeaf k) : |G xs|≤‖F‖:=F.norm_coe_le_norm _
  have he : ∀ᵐ b ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)),
      Integrable (fun _ : IndexedLeaf k=>Real.exp 0) (indexedLeafKernel k b) :=
    ae_of_all _ fun _=>integrable_const _
  have hh:=annealedInfiniteReplica_gibbs_prefix (indexedLeafKernel k)
    (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k) he r hG hGB
  change (∫ Q,F (compactBlock r Q) ∂Measure.map
    (fun a : IndexedCascadeBase k×(ℕ→IndexedLeaf k)=>cavityLabelMarkedArray p D a.2)
    (annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k)))=_
  erw [integral_map
    ((cavityLabelMarkedArray_measurable p D).comp measurable_snd).aemeasurable
    (F.measurable.comp (compactBlock_continuous r).measurable).aestronglyMeasurable]
  have hf : (fun a : IndexedCascadeBase k×(ℕ→IndexedLeaf k)=>F (compactBlock r (cavityLabelMarkedArray p D a.2)))=
      fun a=>G (fun i=>a.2 i.val) := by
    funext a
    apply congrArg F
    funext i j
    simp only [compactBlock,cavityLabelMarkedArray,Fin.val_inj]
  change (∫ a : IndexedCascadeBase k×(ℕ→IndexedLeaf k),
    F (compactBlock r (cavityLabelMarkedArray p D a.2))
    ∂annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k))=_
  rw [hf,hh]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>by
    simp only [gibbsReplicaMean,tiltMean,tiltIntegral,tiltPartition,replicaPotential,
      Finset.sum_const_zero,mul_zero,Real.exp_zero,one_mul,integral_const,probReal_univ,one_smul,div_one,
      indexedLeafKernel,Kernel.coe_mk]
    rfl

lemma cavityPair_block_covariance (n d r : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K) (xs : Fin r→IndexedLeaf k) :
    (fun i j : CavityReplicaIndex n d r=>if i.1=j.1 then Sum.elim
      (fun _=>(if i.2=j.2 then D else p (indexedCommonDepth k (xs j.2) (xs i.2))).2.val)
      (fun _=>(if i.2=j.2 then D else p (indexedCommonDepth k (xs j.2) (xs i.2))).1.val) i.1 else 0)=
    (fun i j=>if i=j then cavityPairDiagonal n d D i.1 else
      if i.1=j.1 then cavityPairProfile n d p (indexedCommonDepth k (xs j.2) (xs i.2)) i.1 else 0) := by
  funext i j
  by_cases h1 : i.1=j.1
  · by_cases h2 : i.2=j.2
    · have h : i=j:=Prod.ext h1 h2
      simp only [h,ite_true,cavityPairDiagonal]
    · have h : i≠j:=fun hh=>h2 (congrArg Prod.snd hh)
      simp only [h1,h2,h,ite_false,ite_true,cavityPairProfile]
  · have h : i≠j:=fun hh=>h1 (congrArg Prod.fst hh)
    simp only [h1,h,ite_false]

theorem cavityLabelMarkedLaw_cavity_moment (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K) (z : Fin k→ℝ)
    (hp0 : ∀ i,0 ≤ cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i ≤ cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) :
    (∫ x,x.val^r ∂(cavityLabelPartitionLaw n d k f Λ hΛ
      (fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i))
      (cavityPairProfile n d p) z : Measure (CavityPartitionRange d f Λ)))=
    ∫ Q,cavityArrayKernel n d r f Λ hΛ K Q ∂cavityLabelMarkedLaw p D z := by
  rw [cavityLabelPartitionLaw_moment n d k f Λ hΛ _ hp0 hpm _ hpD z r]
  let F : CompactBlock (BulkPairRange K) r→ᵇℝ :=
    (cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ)).compContinuous
      ⟨fun Q=>fun i j : CavityReplicaIndex n d r=>if i.1=j.1 then
        Sum.elim (fun _=>(Q i.2 j.2).2.val) (fun _=>(Q i.2 j.2).1.val) i.1 else 0,by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          split_ifs
          · cases i.1 <;> dsimp only [Sum.elim] <;> fun_prop
          · exact continuous_const⟩
  change _=∫ Q,F (compactBlock r Q) ∂cavityLabelMarkedLaw p D z
  rw [cavityLabelMarkedLaw_block]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>integral_congr_ae (ae_of_all _ fun xs=>by
    change _=cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ) _
    rw [cavitySingleTest_replica]
    apply congrArg (cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ))
    exact (cavityPair_block_covariance n d r p D xs).symm)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

theorem cavity_joint_array_log_limit (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hbulk : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
    (k : ℕ→ℕ) (p : (j : ℕ)→Fin (k j+1)→BulkPairRange K)
    (D : ℕ→BulkPairRange K) (z : (j : ℕ)→Fin (k j)→ℝ)
    (hp0 : ∀ j i,0 ≤ cavityPairProfile n d (p j) 0 i)
    (hpm : ∀ j i,Monotone (fun l=>cavityPairProfile n d (p j) l i))
    (hpD : ∀ j i,cavityPairProfile n d (p j) (Fin.last (k j)) i ≤ cavityPairDiagonal n d (D j) i)
    (hrpc : Tendsto (fun j=>cavityLabelMarkedLaw (p j) (D j) (z j)) atTop (𝓝 ν)) :
    Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ-
      ∫ x,Real.log x.val ∂(cavityLabelPartitionLaw n d (k j) f.f Λ hΛ
        (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
        (cavityPairProfile n d (p j)) (z j) : Measure (CavityPartitionRange d f.f Λ))) atTop (𝓝 0) := by
  obtain ⟨η,_hη,hm,hlog⟩:=cavityBulkLog_tendsto n d M f v Λ hΛ K hK s hbulk
  let ρ : ℕ→ProbabilityMeasure (CavityPartitionRange d f.f Λ):=fun j=>
    cavityLabelPartitionLaw n d (k j) f.f Λ hΛ
      (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
      (cavityPairProfile n d (p j)) (z j)
  have hr : Tendsto ρ atTop (𝓝 η) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro F
    apply integral_continuous_tendsto_of_moments (fun j=>(ρ j : Measure (CavityPartitionRange d f.f Λ)))
      (η : Measure (CavityPartitionRange d f.f Λ)) (fun r=>?_) F.toContinuousMap
    rw [hm r]
    have ht:=cavityArrayKernel_tendsto n d r f.f Λ hΛ K hrpc
    have he j : (∫ x,x.val^r ∂(ρ j : Measure (CavityPartitionRange d f.f Λ)))=
        ∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂cavityLabelMarkedLaw (p j) (D j) (z j) :=
      cavityLabelMarkedLaw_cavity_moment n d (p j) (D j) (z j) (hp0 j) (hpm j) (hpD j) f.f Λ hΛ r
    simp_rw [he]
    exact ht
  have hl := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cavityPartitionLogTest d f.f Λ)).continuousAt.tendsto.comp hr
  have hd:=hlog.sub hl
  simpa only [Function.comp_def,cavityPartitionLogTest,BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk,sub_self,ρ] using hd

theorem cavity_joint_array_recursion_limit_oai (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hbulk : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
    (k : ℕ→ℕ) (p : (j : ℕ)→Fin (k j+1)→BulkPairRange K)
    (D : ℕ→BulkPairRange K) (z : (j : ℕ)→Fin (k j)→ℝ)
    (hp0 : ∀ j i,0 ≤ cavityPairProfile n d (p j) 0 i)
    (hpm : ∀ j i,Monotone (fun l=>cavityPairProfile n d (p j) l i))
    (hpD : ∀ j i,cavityPairProfile n d (p j) (Fin.last (k j)) i ≤ cavityPairDiagonal n d (D j) i)
    (hz : ∀ j,StrictMono (z j)) (hz0 : ∀ j i,0<z j i) (hz1 : ∀ j i,z j i<1)
    (hrpc : Tendsto (fun j=>cavityLabelMarkedLaw (p j) (D j) (z j)) atTop (𝓝 ν)) :
    Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ-
      ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
        (gaussianLinearMarkStep (fun l=>diagonalMark (profileGaussianStep (cavityPairProfile n d (p j)) l))) (k j) (z j)
        (fun t=>Real.log (cavityDiagonalAverage
          (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
          (cavitySingleTest n d f.f Λ hΛ) (t 0)))
        (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d (p j))) y)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) atTop (𝓝 0) := by
  have ht:=cavity_joint_array_log_limit n d M f v Λ hΛ K hK s hbulk k p D z hp0 hpm hpD hrpc
  simpa only [cavityLabelPartitionLaw_log_recursion n d _ f.f Λ hΛ _ _ _ (hz _) (hz0 _) (hz1 _)] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit_oai := @OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit_oai
