-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_memLp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:47:50.806596+00:00
-- url     : https://prove2.me/submissions/beea86c5-9420-443e-a6d5-2cc614cc9a2a

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma mem_interior_integrableExpSet_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    t ∈ interior (integrableExpSet X μ) := by
  have he : integrableExpSet X μ=univ := Set.eq_univ_of_forall hX
  simp [he]

omit [IsProbabilityMeasure μ] in
lemma cgf_analytic_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    AnalyticAt ℝ (cgf X μ) t :=
  analyticAt_cgf (mem_interior_integrableExpSet_of_all μ hX t)

lemma entropicMean_eq_div (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {p : ℝ} (hp : p ≠ 0) : entropicMean μ p X=cgf X μ p/p := by
  rw [entropicMean,intervalIntegral.integral_comp_mul_left _ hp]
  simp only [mul_zero,mul_one]
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (cgf_analytic_of_all μ hX t).differentiableAt.hasDerivAt)
    (hc.intervalIntegrable _ _),cgf_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma entropicMean_zero (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    entropicMean μ 0 X=∫ ω, X ω ∂μ := by
  simp [entropicMean,deriv_cgf_zero (mem_interior_integrableExpSet_of_all μ hX 0)]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_norm (a : ℝ) : Integrable (fun y : E => Real.exp (a*‖y‖)) μ := by
  obtain ⟨c,hc,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hh (y : E) : a*‖y‖ ≤ c*‖y‖^2+a^2/(4*c) := by
    have h := sq_nonneg (2*c*‖y‖-a)
    have hd : a^2/(4*c)*(4*c)=a^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply (hI.const_mul (Real.exp (a^2/(4*c)))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hh y]

lemma gaussian_integrable_exp_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a σ : ℝ) (x : E) :
    Integrable (fun y : E => Real.exp (a*f (x+σ • y))) μ := by
  have hbound (y : E) : a*f (x+σ • y) ≤ |a| *|f x|+(|a| *L*|σ|)*‖y‖ := by
    have hl := hf.dist_le_mul (x+σ • y) x
    simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hl
    have hn := abs_add_le (f (x+σ • y)-f x) (f x)
    rw [sub_add_cancel] at hn
    have hmul := mul_le_mul_of_nonneg_left (le_trans hn (add_le_add hl le_rfl)) (abs_nonneg a)
    have hle := le_abs_self (a*f (x+σ • y))
    rw [abs_mul] at hle
    nlinarith
  have hfc := hf.continuous
  apply ((gaussian_integrable_exp_norm μ (|a| *L*|σ|)).const_mul
    (Real.exp (|a| *|f x|))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    exact Real.exp_le_exp.mpr (hbound y)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

lemma integrable_of_all_exp (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) :
    Integrable X μ :=
  (memLp_of_mem_interior_integrableExpSet (mem_interior_integrableExpSet_of_all μ hX 0) 1).integrable (by simp)

omit [IsProbabilityMeasure μ] in
lemma all_exp_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) (c : ℝ) :
    ∀ t : ℝ, Integrable (fun ω => Real.exp (t*(X ω+c))) μ := by
  intro t
  simpa only [mul_add,Real.exp_add] using (hX t).mul_const (Real.exp (t*c))

lemma entropicMean_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (p c : ℝ) : entropicMean μ p (fun ω => X ω+c)=entropicMean μ p X+c := by
  by_cases hp : p=0
  · subst p
    rw [entropicMean_zero μ (all_exp_add_const μ hX c),entropicMean_zero μ hX,
      integral_add (integrable_of_all_exp μ hX) (integrable_const c),integral_const]
    simp
  · rw [entropicMean_eq_div μ (all_exp_add_const μ hX c) hp,entropicMean_eq_div μ hX hp]
    simp only [cgf,mgf_add_const]
    rw [Real.log_mul (ne_of_gt (mgf_pos (hX p))) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
    field_simp

lemma entropicMean_mono_variable
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    (hXY : X ≤ᵐ[μ] Y) {p : ℝ} (hp : 0 ≤ p) :
    entropicMean μ p X ≤ entropicMean μ p Y := by
  rcases hp.eq_or_lt with hp|hp
  · subst p
    rw [entropicMean_zero μ hX,entropicMean_zero μ hY]
    exact integral_mono_ae (integrable_of_all_exp μ hX) (integrable_of_all_exp μ hY) hXY
  · rw [entropicMean_eq_div μ hX (ne_of_gt hp),entropicMean_eq_div μ hY (ne_of_gt hp)]
    apply div_le_div_of_nonneg_right _ hp.le
    exact Real.log_le_log (mgf_pos (hX p)) (mgf_mono_of_nonneg hXY hp.le (hY p))

lemma entropicMean_bounded_difference
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    {C p : ℝ} (hp : 0 ≤ p) (hXY : ∀ᵐ ω ∂μ, |X ω-Y ω| ≤ C) :
    |entropicMean μ p X-entropicMean μ p Y| ≤ C := by
  have h1 : X ≤ᵐ[μ] (fun ω => Y ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).2
    linarith
  have h2 : Y ≤ᵐ[μ] (fun ω => X ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).1
    linarith
  have H1 := entropicMean_mono_variable μ hX (all_exp_add_const μ hY C) h1 hp
  have H2 := entropicMean_mono_variable μ hY (all_exp_add_const μ hX C) h2 hp
  rw [entropicMean_add_const μ hY] at H1
  rw [entropicMean_add_const μ hX] at H2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
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

lemma log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, F x ≤ G x + c) :
    Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ) ≤ c := by
  have hi : (∫ x, Real.exp (F x) ∂μ) ≤
      Real.exp c * ∫ x, Real.exp (G x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hF (hG.const_mul _)
    intro x
    calc
      Real.exp (F x) ≤ Real.exp (G x + c) := Real.exp_le_exp.mpr (h x)
      _ = Real.exp c * Real.exp (G x) := by rw [Real.exp_add, mul_comm]
  have hl := Real.log_le_log pF hi
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt pG), Real.log_exp] at hl
  linarith

lemma abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, |F x - G x| ≤ c) :
    |Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ)| ≤ c := by
  apply abs_le.mpr
  constructor
  · have hh := log_integral_exp_sub_le μ hG hF pG pF (fun x => by
      have := (abs_le.mp (h x)).1
      linarith)
    linarith
  · exact log_integral_exp_sub_le μ hF hG pF pG (fun x => by
      have := (abs_le.mp (h x)).2
      linarith)

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [BorelSpace X] [Nonempty X] in
lemma measurePreserving_fin_cons (n : ℕ) :
    MeasurePreserving (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ : Fin (n+1) => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X] in
lemma measurableEmbedding_fin_cons (n : ℕ) :
    MeasurableEmbedding (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm.measurableEmbedding
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProductMarkLaw
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

lemma decoratedCascade_log_second_moment_bound {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ) :
    MemLp (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) 2
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ∧
    (∫ η, (Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))-c)^2 ∂decoratedCascadeLaw ν n z) ≤
        cascadeLogFluctuationConstant n z := by
  have hid := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 F hF hI hM x
  have hiz := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  have hld := hid.comp Real.measurable_log
  have hlz := hiz.comp Real.measurable_log
  have hL := cascadeTotal_log_memLp_two n z hz hz0 hz1
  have hmD := hld.memLp_iff.mpr hL
  have hmZ := hlz.memLp_iff.mpr hL
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
  refine ⟨(memLp_congr_ae he).mpr (((memLp_const c).add hmD).sub hmZ),?_⟩
  have heD := (hld.comp (by fun_prop : Measurable (fun t : ℝ => t^2))).integral_eq
  have heZ := (hlz.comp (by fun_prop : Measurable (fun t : ℝ => t^2))).integral_eq
  simp only [Function.comp_apply] at heD heZ
  calc
    _ = ∫ η, (Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))^2 ∂decoratedCascadeLaw ν n z := by
      apply integral_congr_ae
      filter_upwards [he] with η hη
      rw [hη]
      ring
    _ ≤ ∫ η, (2*(Real.log (decoratedWeightedTotal step n F (x,η)))^2+
        2*(Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))^2) ∂decoratedCascadeLaw ν n z := by
      apply integral_mono (hmD.sub hmZ).integrable_sq
        ((hmD.integrable_sq.const_mul 2).add (hmZ.integrable_sq.const_mul 2))
      intro η
      dsimp only [Function.comp_apply,Pi.sub_apply,Pi.add_apply]
      nlinarith [sq_nonneg (Real.log (decoratedWeightedTotal step n F (x,η))+
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))]
    _ = _ := by
      have hsplit := integral_add (hmD.integrable_sq.const_mul 2) (hmZ.integrable_sq.const_mul 2)
      simp only [Function.comp_apply] at hsplit
      rw [hsplit,integral_const_mul,integral_const_mul,heD,heZ]
      unfold cascadeLogFluctuationConstant
      ring

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegrableProdConditionalSquare
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

lemma integrable_prod_of_conditional_square {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G : X → ℝ} (hF : Measurable F) (hG : MemLp G 2 μ)
    (K : ℝ) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hb : ∀ x, (∫ y, (F (x,y)-G x)^2 ∂ν) ≤ K) : Integrable F (μ.prod ν) := by
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (hs x).integrable (by norm_num)),?_⟩
  have hi : Integrable (fun x => K+(G x)^2+1) μ :=
    ((integrable_const K).add hG.integrable_sq).add (integrable_const 1)
  apply hi.mono' hF.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
  have hi1 : Integrable (fun y => (F (x,y)-G x)^2) ν :=
    ((hs x).sub (memLp_const (G x))).integrable_sq
  have hi2 : Integrable (fun y => (F (x,y)-G x)^2+(G x)^2) ν := hi1.add (integrable_const _)
  calc
    _ ≤ ∫ y, (F (x,y)-G x)^2+(G x)^2+1 ∂ν := by
      apply integral_mono ((hs x).integrable (by norm_num)).norm
        (hi2.add (integrable_const 1))
      intro y
      change ‖F (x,y)‖ ≤ (F (x,y)-G x)^2+(G x)^2+1
      rw [Real.norm_eq_abs]
      have h1 := sq_nonneg (|F (x,y)-G x|-1)
      have h2 := sq_nonneg (|G x|-1)
      have ht : |F (x,y)| ≤ |F (x,y)-G x|+|G x| := by
        simpa using abs_sub_le (F (x,y)) (G x) 0
      nlinarith [sq_abs (F (x,y)-G x),sq_abs (G x)]
    _ = (∫ y, (F (x,y)-G x)^2 ∂ν)+(G x)^2+1 := by
      rw [integral_add hi2 (integrable_const 1),integral_add hi1 (integrable_const ((G x)^2))]
      simp
    _ ≤ K+(G x)^2+1 := by linarith [hb x]

lemma finiteCascade_terminal_log_second_moment_bound {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    MemLp (fun η => Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η))) 2 (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ∧
    (∫ η, (Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η))-finiteCascadeLogRecursion ν step n z H x)^2
      ∂decoratedCascadeLaw ν n z) ≤ cascadeLogFluctuationConstant n z := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_second_moment_bound ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianMarkRecursion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
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
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_linear_shift {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (A : E →L[ℝ] E) (a : ℝ) (x : E) :
    Integrable (fun y => Real.exp (a*f (x+A y))) μ := by
  have hA : LipschitzWith ‖A‖₊ (fun y => x+A y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using A.lipschitz.dist_le_mul y z
  have hg := hf.comp hA
  simpa using gaussian_integrable_exp_lipschitz μ hg a 1 (0:E)

lemma gaussianLinearEntropic_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {b : ℝ} (hb : 0 ≤ b) (A : E →L[ℝ] E) :
    LipschitzWith L (gaussianLinearEntropic μ b A f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,gaussianLinearEntropic]
  apply entropicMean_bounded_difference μ
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a x)
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a y) hb
  exact ae_of_all _ fun z => by
    simpa only [Real.dist_eq,dist_add_right] using hf.dist_le_mul (x+A z) (y+A z)

lemma gaussianLinearBackward_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (l : List (ℝ×(E →L[ℝ] E)))
    (hl : ∀ c ∈ l, 0 ≤ c.1) : LipschitzWith L (gaussianLinearBackward μ l f) := by
  induction l with
  | nil => exact hf
  | cons c l ih =>
    exact gaussianLinearEntropic_lipschitz μ
      (ih (fun d hd => hl d (List.mem_cons_of_mem c hd))) (hl c List.mem_cons_self) c.2

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
lemma gaussianLinearMarkStep_measurable (A : ℕ → E →L[ℝ] E) :
    Measurable (gaussianLinearMarkStep A) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply (j+1)).comp measurable_fst).add
    ((A j).measurable.comp measurable_snd)

omit [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma linearCascadeWord_nonneg (A : ℕ → E →L[ℝ] E) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∀ c ∈ linearCascadeWord A k z, 0 ≤ c.1 := by
  induction k with
  | zero => simp [linearCascadeWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma gaussianLinearRecursion_realization (ν : ProbabilityMeasure E) [IsGaussian (ν:Measure E)]
    (A : ℕ → E →L[ℝ] E) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ x, finiteCascadeLogRecursion ν (gaussianLinearMarkStep A) k z (fun x => f (x 0)) x=
        gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k z) f (x k)) ∧
    finiteCascadeFractionalIntegrable ν (gaussianLinearMarkStep A) (fun x => f (x 0)) k z := by
  induction k with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ k ih =>
    have H := ih (fun i => z i.succ) (fun i => hz i.succ)
    let g := gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k (fun i => z i.succ)) f
    have hg : LipschitzWith L g := gaussianLinearBackward_lipschitz (ν:Measure E) hf _
      (linearCascadeWord_nonneg A k _ (fun i => (hz i.succ).le))
    constructor
    · intro x
      simp only [finiteCascadeLogRecursion,fractionalLogMoment,H.1,gaussianLinearMarkStep,
        linearCascadeWord,gaussianLinearBackward,gaussianLinearEntropic]
      rw [entropicMean_eq_div (ν:Measure E)
        (fun a => gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) a (x (k+1)))
        (hz 0).ne']
      rfl
    · constructor
      · intro x
        simp only [H.1,gaussianLinearMarkStep]
        exact gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) (z 0) (x (k+1))
      · exact H.2

end
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lipschitz_memLp_stdGaussian {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    MemLp f 2 (stdGaussian E) := by
  have hg : LipschitzWith L (fun x => f x-f 0) := by
    intro x y
    simpa only [edist_sub_right] using hf x y
  have hh := (hg.comp_memLp (by simp) (IsGaussian.memLp_id (stdGaussian E) 2 (by simp))).add
    (memLp_const (f 0))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

lemma gaussianLinearCascadeLog_measurable (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f : E → ℝ} (hf : Measurable f) (k : ℕ) (z : Fin k → ℝ) :
    Measurable (gaussianLinearCascadeLog A R f k) := by
  let ν : ProbabilityMeasure E := gaussianMarkLaw
  have hm : Measurable (fun a : E×DecoratedCascade E k => ((fun _ : ℕ => R a.1),a.2)) :=
    (Measurable.of_eval (fun _ => R.measurable.comp measurable_fst)).prodMk measurable_snd
  exact (((decoratedTerminalTotal_measurable ν _ (gaussianLinearMarkStep_measurable A)
    (hf.comp (measurable_pi_apply 0)) k z).div
    (decoratedTerminalTotal_measurable ν _ (gaussianLinearMarkStep_measurable A)
      measurable_const k z)).log).comp hm

lemma gaussianLinearCascadeLog_mean (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let ν : ProbabilityMeasure E := gaussianMarkLaw
    let μ := (stdGaussian E).prod (decoratedCascadeLaw ν k z)
    Integrable (gaussianLinearCascadeLog A R f k) μ ∧
      (∫ a, gaussianLinearCascadeLog A R f k a ∂μ)=
        ∫ a, gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) f (R a)
          ∂stdGaussian E := by
  let ν : ProbabilityMeasure E := gaussianMarkLaw
  let : IsGaussian (ν:Measure E) := (inferInstance : IsGaussian (stdGaussian E))
  let ρ := decoratedCascadeLaw ν k z
  let F := gaussianLinearCascadeLog A R f k
  let G := fun a => gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) f (R a)
  have hr := gaussianLinearRecursion_realization ν A hf k z hz0
  have hmH : Measurable (fun x : ℕ → E => f (x 0)) :=
    hf.continuous.measurable.comp (measurable_pi_apply 0)
  have hG : MemLp G 2 (stdGaussian E) := lipschitz_memLp_stdGaussian
    ((gaussianLinearBackward_lipschitz (stdGaussian E) hf _
      (linearCascadeWord_nonneg A k z (fun i => (hz0 i).le))).comp R.lipschitz)
  have hsec (a : E) : MemLp (fun η => F (a,η)) 2 (ρ:Measure _) ∧
      (∫ η, (F (a,η)-G a)^2 ∂ρ) ≤ cascadeLogFluctuationConstant k z := by
    have H := finiteCascade_terminal_log_second_moment_bound ν (gaussianLinearMarkStep A)
      (gaussianLinearMarkStep_measurable A) k z hz hz0 hz1 hmH hr.2 (fun _ => R a)
    rw [hr.1] at H
    exact H
  have hF := gaussianLinearCascadeLog_measurable A R hf.continuous.measurable k z
  have hi : Integrable F ((stdGaussian E).prod ρ) :=
    integrable_prod_of_conditional_square (stdGaussian E) ρ hF hG
      (cascadeLogFluctuationConstant k z) (fun a => (hsec a).1) (fun a => (hsec a).2)
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    have H := finiteCascade_terminal_log_recursion_of_fractional ν (gaussianLinearMarkStep A)
      (gaussianLinearMarkStep_measurable A) k z hz hz0 hz1 hmH hr.2 (fun _ => R a)
    rw [hr.1] at H
    exact H

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CascadeParameters
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {P X S : Type} [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace S]

lemma parameterMarkStep_measurable {step : X×S → X} (hs : Measurable step) :
    Measurable (parameterMarkStep (P := P) step) :=
  (measurable_fst.comp measurable_fst).prodMk
    (hs.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma decoratedTerminalTotalE_parameter (step : X×S → X) (H : P → X → ℝ)
    (n : ℕ) (p : P) (x : X) (η : DecoratedCascade S n) :
    decoratedTerminalTotalE (parameterMarkStep step) (Function.uncurry H) n ((p,x),η)=
      decoratedTerminalTotalE step (H p) n (x,η) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    apply lintegral_congr
    intro q
    congr 1
    exact ih (step (x,q.2.1)) q.2.2

lemma decoratedTerminalTotal_parameter (step : X×S → X) (H : P → X → ℝ)
    (n : ℕ) (p : P) (x : X) (η : DecoratedCascade S n) :
    decoratedTerminalTotal (parameterMarkStep step) (Function.uncurry H) n ((p,x),η)=
      decoratedTerminalTotal step (H p) n (x,η) :=
  congrArg ENNReal.toReal (decoratedTerminalTotalE_parameter step H n p x η)

end

variable {P E : Type} [MeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma gaussianLinearCascadeLog_parameter_measurable
    (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {H : P → E → ℝ} (hH : Measurable (Function.uncurry H)) (k : ℕ) (z : Fin k → ℝ) :
    Measurable (fun a : P × (E×DecoratedCascade E k) =>
      gaussianLinearCascadeLog A R (H a.1) k a.2) := by
  let step := gaussianLinearMarkStep A
  let V := fun p : P => fun x : ℕ → E => H p (x 0)
  have hV : Measurable (Function.uncurry V) := hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  let T := fun a : P × (E×DecoratedCascade E k) =>
    ((a.1,fun _ : ℕ => R a.2.1),a.2.2)
  have hT : Measurable T :=
    (measurable_fst.prodMk (Measurable.of_eval (fun _ =>
      R.measurable.comp (measurable_fst.comp measurable_snd)))).prodMk
        (measurable_snd.comp measurable_snd)
  let ν : ProbabilityMeasure E := gaussianMarkLaw
  have hs : Measurable step := gaussianLinearMarkStep_measurable A
  have h1 := (decoratedTerminalTotal_measurable ν (parameterMarkStep step)
    (parameterMarkStep_measurable hs) hV k z).comp hT
  have h0 := (decoratedTerminalTotal_measurable ν (parameterMarkStep step)
    (parameterMarkStep_measurable hs) (H := Function.uncurry (fun (_ : P) (_ : ℕ → E) => (0:ℝ)))
    measurable_const k z).comp hT
  have he (a : P × (E×DecoratedCascade E k)) :
      gaussianLinearCascadeLog A R (H a.1) k a.2=
        Real.log (decoratedTerminalTotal (parameterMarkStep step) (Function.uncurry V) k (T a)/
          decoratedTerminalTotal (parameterMarkStep step) (Function.uncurry (fun (_ : P) (_ : ℕ → E) => (0:ℝ))) k (T a)) := by
    rw [decoratedTerminalTotal_parameter,decoratedTerminalTotal_parameter]
    rfl
  simp_rw [he]
  exact (h1.div h0).log
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_PoissonCountMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma poisson_nat_lintegral (r : ℝ≥0) :
    (∫⁻ m : ℕ, ENNReal.ofReal (m:ℝ) ∂poissonMeasure r)=r := by
  simp_rw [ENNReal.ofReal_natCast]
  rw [lintegral_countable']
  simpa only [mul_comm] using poissonMeasure_mean r

lemma poisson_natSquare_lintegral (r : ℝ≥0) :
    (∫⁻ m : ℕ, ENNReal.ofReal ((m:ℝ)^2) ∂poissonMeasure r)=(r:ℝ≥0∞)^2+r := by
  have hmass : (∑' m : ℕ, poissonMeasure r {m})=1 := by
    simpa using (lintegral_countable' (μ := poissonMeasure r) (fun _ => (1:ℝ≥0∞))).symm
  simp_rw [ENNReal.ofReal_pow (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  rw [lintegral_countable']
  simp_rw [mul_comm ((_:ℝ≥0∞)^2)]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_add]
  have hterm (m : ℕ) : poissonMeasure r {m+1} * ((m+1:ℕ):ℝ≥0∞)^2=
      (r:ℝ≥0∞)*(poissonMeasure r {m}*(m:ℝ≥0∞))+(r:ℝ≥0∞)*poissonMeasure r {m} := by
    rw [pow_two,← mul_assoc]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [poissonMeasure_atom_succ]
    ring
  simp_rw [hterm]
  rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left,
    poissonMeasure_mean,hmass,mul_one,pow_two]

lemma poisson_nat_memLp (r : ℝ≥0) : MemLp (fun m : ℕ => (m:ℝ)) 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  refine ⟨by fun_prop,(hasFiniteIntegral_iff_norm _).mpr ?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  rw [poisson_natSquare_lintegral]
  finiteness

lemma poisson_nat_mean (r : ℝ≥0) : (∫ m : ℕ, (m:ℝ) ∂poissonMeasure r)=r := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun m => Nat.cast_nonneg m) (by fun_prop),
    poisson_nat_lintegral,ENNReal.coe_toReal]

lemma poisson_nat_square_mean (r : ℝ≥0) :
    (∫ m : ℕ, (m:ℝ)^2 ∂poissonMeasure r)=(r:ℝ)^2+r := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun m : ℕ => sq_nonneg (m:ℝ)) (by fun_prop),
    poisson_natSquare_lintegral,ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_pow,ENNReal.coe_toReal]

lemma poisson_nat_center_square (r : ℝ≥0) (a : ℝ) :
    (∫ m : ℕ, ((m:ℝ)-a)^2 ∂poissonMeasure r)=(r:ℝ)+((r:ℝ)-a)^2 := by
  have hi := (poisson_nat_memLp r).integrable (by norm_num)
  have hs := (poisson_nat_memLp r).integrable_sq
  have he (m : ℕ) : ((m:ℝ)-a)^2=(m:ℝ)^2-2*a*(m:ℝ)+a^2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun m : ℕ => (m:ℝ)^2-2*a*(m:ℝ))
      (g := fun _ : ℕ => a^2) (hs.sub (hi.const_mul (2*a))) (integrable_const _),
    integral_sub (f := fun m : ℕ => (m:ℝ)^2) (g := fun m : ℕ => 2*a*(m:ℝ))
      hs (hi.const_mul (2*a)),integral_const_mul]
  simp only [poisson_nat_mean,poisson_nat_square_mean]
  simp
  ring

lemma nat_bounded_increment_difference {F : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ m, |F (m+1)-F m| ≤ C) (m n : ℕ) :
    |F m-F n| ≤ C*|(m:ℝ)-(n:ℝ)| := by
  have hle (m n : ℕ) (hmn : m ≤ n) : |F n-F m| ≤ C*((n:ℝ)-(m:ℝ)) := by
    induction n,hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have ht := abs_sub_le (F (n+1)) (F n) (F m)
      have hh := hF n
      push_cast
      linarith
  rcases le_total m n with hmn|hnm
  · rw [abs_sub_comm (F m),abs_sub_comm (m:ℝ)]
    exact (hle m n hmn).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
  · exact (hle n m hnm).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)

lemma poisson_bounded_increment_memLp (r : ℝ≥0) {F : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ m, |F (m+1)-F m| ≤ C) : MemLp F 2 (poissonMeasure r) := by
  have hi : MemLp (fun m : ℕ => |F 0|+C*(m:ℝ)) 2 (poissonMeasure r) :=
    (memLp_const (μ := poissonMeasure r) |F 0|).add ((poisson_nat_memLp r).const_mul C)
  refine hi.mono (measurable_of_countable F).aestronglyMeasurable (ae_of_all _ fun m => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (show (0:ℝ) ≤ |F 0|+C*(m:ℝ) by positivity)]
  have hh := nat_bounded_increment_difference hC hF m 0
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m)] at hh
  have ht := abs_sub_le (F m) (F 0) 0
  simp only [sub_zero] at ht
  linarith

lemma poisson_bounded_increment_variance (r : ℝ≥0) {F : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ m, |F (m+1)-F m| ≤ C) :
    variance F (poissonMeasure r) ≤ C^2*((r:ℝ)+1) := by
  let a : ℕ := ⌊(r:ℝ)⌋₊
  have hp := poisson_bounded_increment_memLp r hC hF
  have hv := variance_le_expectation_sq ((hp.sub (memLp_const (F a))).aestronglyMeasurable)
  change variance (fun m => F m-F a) (poissonMeasure r) ≤
    ∫ m, (F m-F a)^2 ∂poissonMeasure r at hv
  rw [variance_sub_const hp.aestronglyMeasurable] at hv
  have hc : Integrable (fun m : ℕ => C^2*((m:ℝ)-(a:ℝ))^2) (poissonMeasure r) :=
    ((poisson_nat_memLp r).sub (memLp_const (a:ℝ))).integrable_sq.const_mul _
  have hd : (∫ m, (F m-F a)^2 ∂poissonMeasure r) ≤
      C^2*((r:ℝ)+((r:ℝ)-(a:ℝ))^2) := by
    calc
      _ ≤ ∫ m : ℕ, C^2*((m:ℝ)-(a:ℝ))^2 ∂poissonMeasure r := by
        apply integral_mono (hp.sub (memLp_const (F a))).integrable_sq hc
        intro m
        have hh := nat_bounded_increment_difference hC hF m a
        have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
        simpa only [sq_abs,mul_pow,Pi.sub_apply] using hs
      _ = _ := by rw [integral_const_mul,poisson_nat_center_square]
  have hfloor : (a:ℝ) ≤ (r:ℝ) := Nat.floor_le r.coe_nonneg
  have hceil : (r:ℝ) < (a:ℝ)+1 := Nat.lt_floor_add_one (r:ℝ)
  have hsq : ((r:ℝ)-(a:ℝ))^2 ≤ 1 := by nlinarith
  exact hv.trans (hd.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianRotation
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

lemma integral_sq_ge_sq_integral_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (hμ : 0 < μ.real univ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, (f x)^2 ∂μ := by
  let i := ∫ x, f x ∂μ
  let a := μ.real univ
  have hi := hf.integrable (by norm_num)
  have hi2 := hf.integrable_sq
  have he : (∫ x, (f x-i/a)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ)-2*(i/a)*i+a*(i/a)^2 := by
    calc
      _ = ∫ x, (f x)^2-(2*(i/a))*f x+(i/a)^2 ∂μ := integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = _ := by
        have ha := integral_add (hi2.sub (hi.const_mul (2*(i/a)))) (integrable_const ((i/a)^2))
        have hb := integral_sub hi2 (hi.const_mul (2*(i/a)))
        simp only [Pi.sub_apply] at ha
        rw [ha,hb,integral_const_mul,integral_const]
        rfl
  have hn : (0 : ℝ) ≤ ∫ x, (f x-i/a)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [he] at hn
  have ha : a ≠ 0 := hμ.ne'
  have hae : a*(i/a)^2 = i^2/a := by field_simp
  have hie : 2*(i/a)*i = 2*(i^2/a) := by ring
  rw [hae,hie] at hn
  have : i^2/a ≤ ∫ x, (f x)^2 ∂μ := by linarith
  exact (div_le_iff₀ hμ).mp this |>.trans_eq (mul_comm ..)

lemma integral_independent_difference_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    (∫ p : Ω×Ω, (F p.1-F p.2)^2 ∂μ.prod μ) = 2*variance F μ := by
  have hi := hF.integrable (by norm_num)
  have hi2 := hF.integrable_sq
  have hprod := hi.mul_prod hi
  calc
    _ = ∫ p : Ω×Ω, (F p.1)^2-2*(F p.1*F p.2)+(F p.2)^2 ∂μ.prod μ :=
      integral_congr_ae (ae_of_all _ fun p => by ring)
    _ = _ := by
      have ha := integral_add ((hi2.comp_fst μ).sub (hprod.const_mul 2)) (hi2.comp_snd μ)
      have hb := integral_sub (hi2.comp_fst μ) (hprod.const_mul 2)
      simp only [Pi.sub_apply] at ha
      rw [ha,hb,integral_const_mul,integral_fun_fst (fun x : Ω => (F x)^2),
        integral_fun_snd (fun x : Ω => (F x)^2),
        integral_prod_mul F F,variance_eq_sub hF]
      simp only [probReal_univ,one_smul,Pi.pow_apply]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma dual_rotation_norm (A B : StrongDual ℝ E) (t : ℝ) :
    ‖Real.cos t • A - Real.sin t • B‖^2 + ‖Real.sin t • A + Real.cos t • B‖^2 =
      ‖A‖^2+‖B‖^2 := by
  let e := (InnerProductSpace.toDual ℝ E).symm
  rw [← e.norm_map (Real.cos t • A - Real.sin t • B),
    ← e.norm_map (Real.sin t • A + Real.cos t • B),← e.norm_map A,← e.norm_map B]
  simp only [map_sub,map_add,map_smul,norm_sub_sq_real,norm_add_sq_real,
    real_inner_smul_left,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have h := Real.sin_sq_add_cos_sq t
  nlinarith [sq_nonneg ‖e A‖,sq_nonneg ‖e B‖]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussianVectorRotation_apply (t : ℝ) (p : E×E) :
    gaussianVectorRotation t p = (Real.cos t • p.1+Real.sin t • p.2,
      -Real.sin t • p.1+Real.cos t • p.2) := rfl

lemma gaussianVectorRotation_preserving (t : ℝ) :
    MeasurePreserving (gaussianVectorRotation (E := E) t) ((stdGaussian E).prod (stdGaussian E))
      ((stdGaussian E).prod (stdGaussian E)) := by
  refine ⟨by fun_prop, Measure.ext_of_charFunDual ?_⟩
  ext L
  rw [charFunDual_map]
  simp only [charFunDual_prod,charFunDual_stdGaussian]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  let A := L.comp (ContinuousLinearMap.inl ℝ E E)
  let B := L.comp (ContinuousLinearMap.inr ℝ E E)
  have hsplit (x y : E) : L (x,y) = L (x,0)+L (0,y) := by
    simpa using L.map_add (x,0) (0,y)
  have ha : (L.comp (gaussianVectorRotation t)).comp (ContinuousLinearMap.inl ℝ E E) =
      Real.cos t • A - Real.sin t • B := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      smul_apply,sub_apply,gaussianVectorRotation_apply,smul_zero,add_zero]
    rw [hsplit]
    change A (Real.cos t • x) + B (-Real.sin t • x) = _
    simp [sub_eq_add_neg]
  have hb : (L.comp (gaussianVectorRotation t)).comp (ContinuousLinearMap.inr ℝ E E) =
      Real.sin t • A + Real.cos t • B := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      smul_apply,add_apply,gaussianVectorRotation_apply,smul_zero,zero_add]
    rw [hsplit]
    change A (Real.sin t • x) + B (Real.cos t • x) = _
    simp
  rw [ha,hb]
  have h := dual_rotation_norm A B t
  have hc : (‖Real.cos t • A - Real.sin t • B‖ : ℂ)^2 +
    (‖Real.sin t • A + Real.cos t • B‖ : ℂ)^2 = (‖A‖ : ℂ)^2+(‖B‖ : ℂ)^2 := by
    exact_mod_cast h
  change _ = -(‖A‖ : ℂ)^2/2 + -(‖B‖ : ℂ)^2/2
  linear_combination -hc/2

lemma stdGaussian_dual_secondMoment (L : StrongDual ℝ E) :
    (∫ x, (L x)^2 ∂stdGaussian E) = ‖L‖^2 := by
  have hm : MemLp L 2 (stdGaussian E) := IsGaussian.memLp_dual _ _ 2 (by simp)
  have h := variance_eq_sub hm
  rw [integral_strongDual_stdGaussian,zero_pow (by omega),sub_zero,
    variance_dual_stdGaussian] at h
  exact h.symm

lemma hasFDerivAt_bounded_gaussian_memLp {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) {C : ℝ} (hC : 0 ≤ C)
    (hDC : ∀ x, ‖D x‖ ≤ C) : MemLp F 2 (stdGaussian E) := by
  have hL : LipschitzWith ⟨C,hC⟩ F := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hF x).differentiableAt) (fun x => by
      rw [(hF x).fderiv]
      exact_mod_cast hDC x)
  have hgc : LipschitzWith ⟨C,hC⟩ (fun x => F x-F 0) := by
    intro x y
    simpa only [edist_sub_right] using hL x y
  have hg := hgc.comp_memLp (by simp) (IsGaussian.memLp_id (stdGaussian E) 2 (by simp))
  have hh := hg.add (memLp_const (F 0))
  have he : ((fun x => F x-F 0) ∘ id + fun _ => F 0) = F := by
    funext x
    simp
  rw [he] at hh
  convert! hh

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussian_vector_rotation_path_bound {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D) (x y : E) :
    (F y-F x)^2 ≤ (Real.pi/2) * ∫ t in Ioc 0 (Real.pi/2),
      (D (Real.cos t • x+Real.sin t • y) (-Real.sin t • x+Real.cos t • y))^2 := by
  let d := fun t => D (Real.cos t • x+Real.sin t • y) (-Real.sin t • x+Real.cos t • y)
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hdF (t : ℝ) : HasDerivAt (fun t => F (Real.cos t • x+Real.sin t • y)) (d t) t := by
    exact (hF _).comp_hasDerivAt t (((Real.hasDerivAt_cos t).smul_const x).add
      ((Real.hasDerivAt_sin t).smul_const y))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hdF t) (hd.intervalIntegrable 0 (Real.pi/2))
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,Real.cos_zero,Real.sin_zero,
    zero_smul,one_smul,zero_add,add_zero] at hi
  rw [intervalIntegral.integral_of_le (by positivity)] at hi
  have hm : MemLp d 2 (volume.restrict (Ioc 0 (Real.pi/2))) :=
    (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
      ((hd.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hmass : (volume.restrict (Ioc 0 (Real.pi/2))).real univ = Real.pi/2 := by
    simp [Measure.real,Real.volume_Ioc]; positivity
  have hh := integral_sq_ge_sq_integral_div (volume.restrict (Ioc 0 (Real.pi/2)))
    hm (by rw [hmass]; positivity)
  rw [hmass,hi] at hh
  exact hh

lemma gaussian_vector_rotation_derivative_square_mean {D : E → StrongDual ℝ E}
    (hD : Continuous D) {C : ℝ} (hDC : ∀ x, ‖D x‖ ≤ C) (t : ℝ) :
    (∫ p : E × E,
      (D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2))^2
      ∂(stdGaussian E).prod (stdGaussian E)) =
      ∫ x, ‖D x‖^2 ∂stdGaussian E := by
  have he := integral_map (μ := (stdGaussian E).prod (stdGaussian E))
    (gaussianVectorRotation t).continuous.measurable.aemeasurable
    (f := fun p : E×E => (D p.1 p.2)^2) (by fun_prop)
  rw [(gaussianVectorRotation_preserving t).map_eq] at he
  dsimp only [gaussianVectorRotation_apply] at he
  rw [← he]
  have hi : Integrable (fun p : E×E => (D p.1 p.2)^2) ((stdGaussian E).prod (stdGaussian E)) := by
    have hh := ((IsGaussian.memLp_id (stdGaussian E) 2 (by simp)).norm.integrable_sq.const_mul (C^2)).comp_snd (stdGaussian E)
    apply hh.mono' (by fun_prop)
    refine ae_of_all _ fun p => ?_
    have hC : 0 ≤ C := (norm_nonneg (D p.1)).trans (hDC _)
    have hh : |D p.1 p.2| ≤ C*‖p.2‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDC _) (norm_nonneg _))
    have hh2 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (norm_nonneg p.2))).mpr hh
    simpa only [Real.norm_eq_abs,abs_sq,sq_abs,mul_pow,id_eq] using hh2
  rw [integral_prod _ hi]
  congr 1
  funext x
  exact stdGaussian_dual_secondMoment (D x)

lemma stdGaussian_poincare {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D)
    {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, ‖D x‖ ≤ C) :
    variance F (stdGaussian E) ≤ (Real.pi^2/8)*(∫ x, ‖D x‖^2 ∂stdGaussian E) := by
  let γ := stdGaussian E
  let μ := γ.prod γ
  let T := Real.pi/2
  let ν := volume.restrict (Ioc 0 T)
  let d := fun (t : ℝ) (p : E×E) =>
    D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hν : ν.real univ = T := by simp [ν,Measure.real,Real.volume_Ioc,hT.le]
  have hdom (t : ℝ) (p : E×E) : (d t p)^2 ≤ 2*C^2*(‖p.1‖^2+‖p.2‖^2) := by
    have hb : ‖-Real.sin t • p.1+Real.cos t • p.2‖ ≤ ‖p.1‖+‖p.2‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg]
      exact add_le_add (by nlinarith [Real.abs_sin_le_one t,norm_nonneg p.1])
        (by nlinarith [Real.abs_cos_le_one t,norm_nonneg p.2])
    have hh : |d t p| ≤ C*(‖p.1‖+‖p.2‖) := by
      change ‖D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2)‖ ≤ _
      apply (ContinuousLinearMap.le_opNorm _ _).trans
      exact mul_le_mul (hDC _) hb (norm_nonneg _) hC
    have hh2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C*(‖p.1‖+‖p.2‖))).mpr hh
    simp only [sq_abs,mul_pow] at hh2
    have hh3 := mul_nonneg (sq_nonneg C) (sq_nonneg (‖p.1‖-‖p.2‖))
    nlinarith
  have hs : Integrable (fun x : E => ‖x‖^2) γ :=
    (IsGaussian.memLp_id γ 2 (by simp)).norm.integrable_sq
  have hdI : Integrable (fun p : (E×E)×ℝ => (d p.2 p.1)^2) (μ.prod ν) := by
    have hh : Integrable (fun p : (E×E)×ℝ => 2*C^2*(‖p.1.1‖^2+‖p.1.2‖^2)) (μ.prod ν) :=
      (((hs.comp_fst γ).add (hs.comp_snd γ)).const_mul (2*C^2)).comp_fst ν
    apply hh.mono' (by dsimp [d]; fun_prop)
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,abs_sq] using hdom p.2 p.1
  have hmF : MemLp F 2 γ := hasFDerivAt_bounded_gaussian_memLp hF hC hDC
  have hdiff : Integrable (fun p : E×E => (F p.2-F p.1)^2) μ := by
    simpa only [Pi.sub_apply] using ((hmF.comp_snd γ).sub (hmF.comp_fst γ)).integrable_sq
  have he : (∫ p : E×E, (F p.2-F p.1)^2 ∂μ) = 2*variance F γ := by
    rw [show (fun p : E×E => (F p.2-F p.1)^2) = fun p => (F p.1-F p.2)^2 by
      funext p; ring]
    exact integral_independent_difference_square γ hmF
  have hn := integral_mono_ae hdiff (hdI.integral_prod_left.const_mul T)
    (ae_of_all _ fun p => gaussian_vector_rotation_path_bound hF hD p.1 p.2)
  rw [he,integral_const_mul,← integral_prod _ hdI,integral_prod_symm _ hdI] at hn
  have hmeans : (∫ t, ∫ p : E×E, (d t p)^2 ∂μ ∂ν) =
      T*(∫ x, ‖D x‖^2 ∂γ) := by
    simp_rw [show ∀ t, (∫ p : E×E, (d t p)^2 ∂μ) = ∫ x, ‖D x‖^2 ∂γ
      from fun t => gaussian_vector_rotation_derivative_square_mean hD hDC t]
    rw [integral_const,hν,smul_eq_mul]
  rw [hmeans] at hn
  dsimp only [T] at hn
  nlinarith

lemma stdGaussian_variance_le_of_fderiv_bound {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D)
    {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, ‖D x‖ ≤ C) :
    variance F (stdGaussian E) ≤ (Real.pi^2/8)*C^2 := by
  apply (stdGaussian_poincare hF hD hC hDC).trans
  gcongr
  calc
    _ ≤ ∫ _ : E, C^2 ∂stdGaussian E :=
      integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_const _)
        (ae_of_all _ fun x => (sq_le_sq₀ (norm_nonneg _) hC).mpr (hDC x))
    _ = C^2 := by simp

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_VectorPartition
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
  {W : S → ℝ} {V : S → StrongDual ℝ E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] in
lemma vectorEnergy_bound {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (x : E) (s : S) : |W s + V s x| ≤ K+C*‖x‖ := by
  apply (abs_add_le _ _).trans
  apply add_le_add (hW s)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg x))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_integrable (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    Integrable (fun s => Real.exp (W s + V s x)) ρ := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (K+C*‖x‖)) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound hW hV x s))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_pos (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    0 < vectorPartition ρ W V x := by
  apply integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le)
    (vectorPartition_integrable ρ hWm hVm hW hV x) |>.mpr
  simp [Function.support,Real.exp_ne_zero]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_hasFDerivAt (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    HasFDerivAt (vectorPartition ρ W V) (∫ s, Real.exp (W s+V s x) • V s ∂ρ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x 1) (bound := fun _ => Real.exp (K+C*(‖x‖+1))*C)
    (F' := fun y s => Real.exp (W s+V s y) • V s) (Metric.ball_mem_nhds x zero_lt_one)
    (Filter.Eventually.of_forall fun y => by fun_prop)
    (vectorPartition_integrable ρ hWm hVm hW hV x) (by fun_prop)
    (ae_of_all _ fun s y hy => ?_) (integrable_const _) (ae_of_all _ fun s y _ => ?_)
  · have hy' : ‖y‖ ≤ ‖x‖+1 := by
      have hh : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      have hn := norm_add_le (y-x) x
      rw [sub_add_cancel] at hn
      linarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hV _) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    exact ((le_abs_self _).trans (vectorEnergy_bound hW hV y s)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hC))
  · exact (((V s).hasFDerivAt).const_add (W s)).exp

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_hasFDerivAt (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    HasFDerivAt (vectorLogPartition ρ W V) (vectorLogDerivative ρ W V x) x :=
  (vectorPartition_hasFDerivAt ρ hWm hVm hC hW hV x).log
    (vectorPartition_pos ρ hWm hVm hW hV x).ne'

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogDerivative_continuous (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    Continuous (vectorLogDerivative ρ W V) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp := (vectorPartition_hasFDerivAt ρ hWm hVm hC hW hV x).continuousAt
  apply (hp.inv₀ (vectorPartition_pos ρ hWm hVm hW hV x).ne').smul
  apply continuousAt_of_dominated (bound := fun _ => Real.exp (K+C*(‖x‖+1))*C)
  · exact Filter.Eventually.of_forall fun y => by fun_prop
  · filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    exact ae_of_all _ fun s => by
      have hy' : ‖y‖ ≤ ‖x‖+1 := by
        have hh : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
        have hn := norm_add_le (y-x) x
        rw [sub_add_cancel] at hn
        linarith
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul _ (hV _) (norm_nonneg _) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      exact ((le_abs_self _).trans (vectorEnergy_bound hW hV y s)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hC))
  · exact integrable_const _
  · exact ae_of_all _ fun s => by fun_prop

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
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
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

section Partition
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_lipschitz {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K : ℝ} {C : ℝ≥0}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    LipschitzWith C (vectorLogPartition ρ W V) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,vectorLogPartition,vectorPartition]
  apply abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (vectorPartition_integrable ρ hWm hVm hW hV y)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (vectorPartition_pos ρ hWm hVm hW hV y)
  intro s
  simp only [add_sub_add_left_eq_sub,← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg _))
end Partition

lemma sourceEnrichedFeature_norm (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ)
    (x : NormalizedSpin N) : ‖sourceEnrichedFeature N p u x‖=enrichedFeatureBound N u := by
  rw [sourceEnrichedFeature,enrichedFeature_norm,Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

lemma enrichedTerminal_lipschitz (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (htop : ℝ) : LipschitzWith (enrichedFeatureBound (n+1) u)
      (enrichedTerminal n M f g p u htop) := by
  have hW : Continuous (normalizedPatternEnergy (n+1) M f g) :=
    (normalizedPatternEnergy_continuous (n+1) M f).comp
    (continuous_const.prodMk continuous_id)
  have hV : Continuous (fun x : NormalizedSpin (n+1) =>
      innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) :=
    (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  have hL := vectorLogPartition_lipschitz (unitSphereLaw (n+1)) hW.measurable hV.measurable
    (normalizedPatternEnergy_bound (n+1) M f g)
    (fun x => by rw [innerSL_apply_norm,sourceEnrichedFeature_norm])
  intro x y
  simpa only [enrichedTerminal,edist_sub_right] using hL x y

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedMoments
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

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussianLinearEntropic_C1 {f : E → ℝ} {D : E → StrongDual ℝ E} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x) (hD : Continuous D)
    {b : ℝ} (hb : 0<b) (A : E →L[ℝ] E) :
    ∃ D' : E → StrongDual ℝ E, Continuous D' ∧
      (∀ x, HasFDerivAt (gaussianLinearEntropic μ b A f) (D' x) x) ∧
      (∀ x, ‖D' x‖ ≤ L) := by
  have hfc : Continuous f := hf.continuous
  have hDC (x : E) : ‖D x‖ ≤ L := by
    rw [← (hd x).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hf
  let Z := fun x => ∫ y, Real.exp (b*f (x+A y)) ∂μ
  let ZD := fun x => ∫ y, Real.exp (b*f (x+A y)) • (b • D (x+A y)) ∂μ
  have hZpos (x : E) : 0<Z x := by
    apply integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
      (gaussian_integrable_exp_linear_shift μ hf A b x) |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hdom (x₀ x y : E) (hx : x ∈ Metric.ball x₀ 1) :
      ‖Real.exp (b*f (x+A y)) • (b • D (x+A y))‖ ≤
        (Real.exp (b*L)*(b*L))*Real.exp (b*f (x₀+A y)) := by
    have hh := hf.dist_le_mul (x+A y) (x₀+A y)
    rw [dist_add_right,Real.dist_eq] at hh
    have hx' : dist x x₀ ≤ 1 := (Metric.mem_ball.mp hx).le
    have hff : f (x+A y)-f (x₀+A y) ≤ L :=
      (le_abs_self _).trans (hh.trans (by simpa using mul_le_mul_of_nonneg_left hx' L.coe_nonneg))
    have hExp : Real.exp (b*f (x+A y)) ≤ Real.exp (b*L)*Real.exp (b*f (x₀+A y)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_of_pos hb]
    calc
      _ ≤ (Real.exp (b*L)*Real.exp (b*f (x₀+A y)))*(b*L) :=
        mul_le_mul hExp (mul_le_mul_of_nonneg_left (hDC _) hb.le) (by positivity) (by positivity)
      _ = _ := by ring
  have hZ (x : E) : HasFDerivAt Z (ZD x) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun x y => Real.exp (b*f (x+A y)) • (b • D (x+A y)))
      (bound := fun y => (Real.exp (b*L)*(b*L))*Real.exp (b*f (x+A y)))
      (Metric.ball_mem_nhds x zero_lt_one)
    · exact Eventually.of_forall fun x => by fun_prop
    · exact gaussian_integrable_exp_linear_shift μ hf A b x
    · fun_prop
    · exact ae_of_all _ fun y x' hx' => hdom x x' y hx'
    · exact (gaussian_integrable_exp_linear_shift μ hf A b x).const_mul _
    · exact ae_of_all _ fun y x' _ => by
        have hh := (hd (x'+A y)).comp x' ((hasFDerivAt_id x').add_const (A y))
        simpa using (hh.const_mul b).exp
  have hZD : Continuous ZD := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply continuousAt_of_dominated
      (bound := fun y => (Real.exp (b*L)*(b*L))*Real.exp (b*f (x+A y)))
    · exact Eventually.of_forall fun x => by fun_prop
    · filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with x' hx'
      exact ae_of_all _ fun y => hdom x x' y hx'
    · exact (gaussian_integrable_exp_linear_shift μ hf A b x).const_mul _
    · exact ae_of_all _ fun y => by fun_prop
  let D' := fun x => b⁻¹ • ((Z x)⁻¹ • ZD x)
  have he : gaussianLinearEntropic μ b A f = fun x => Real.log (Z x)/b := by
    funext x
    exact entropicMean_eq_div μ (fun s => gaussian_integrable_exp_linear_shift μ hf A s x) hb.ne'
  have hd' (x : E) : HasFDerivAt (gaussianLinearEntropic μ b A f) (D' x) x := by
    rw [he]
    have hh := ((hZ x).log (hZpos x).ne').const_mul b⁻¹
    simpa only [D',div_eq_mul_inv,mul_comm] using hh
  refine ⟨D',?_,hd',?_⟩
  · have hcZ : Continuous Z := continuous_iff_continuousAt.mpr (fun x => (hZ x).continuousAt)
    change Continuous (fun x => b⁻¹ • ((Z x)⁻¹ • ZD x))
    exact (continuous_const : Continuous (fun _ : E => (b⁻¹ : ℝ))).smul
      ((hcZ.inv₀ (fun x => (hZpos x).ne')).smul hZD)
  · intro x
    rw [← (hd' x).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (gaussianLinearEntropic_lipschitz μ hf hb.le A)

lemma gaussianLinearBackward_C1 {f : E → ℝ} {D : E → StrongDual ℝ E} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x) (hD : Continuous D)
    (l : List (ℝ×(E →L[ℝ] E))) (hl : ∀ c ∈ l, 0 < c.1) :
    ∃ D' : E → StrongDual ℝ E, Continuous D' ∧
      (∀ x, HasFDerivAt (gaussianLinearBackward μ l f) (D' x) x) ∧
      (∀ x, ‖D' x‖ ≤ L) := by
  induction l with
  | nil =>
    exact ⟨D,hD,hd,fun x => by
      rw [← (hd x).fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ hf⟩
  | cons c l ih =>
    have hl' : ∀ d ∈ l, 0<d.1 := fun d hd => hl d (List.mem_cons_of_mem c hd)
    obtain ⟨D',hD',hd',_⟩ := ih hl'
    exact gaussianLinearEntropic_C1 μ
      (gaussianLinearBackward_lipschitz μ hf l (fun d hd => (hl' d hd).le))
      hd' hD' (hl c List.mem_cons_self) c.2

lemma gaussianLinearBackward_root_variance {f : E → ℝ} {D : E → StrongDual ℝ E}
    {L : ℝ≥0} (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x)
    (hD : Continuous D) (l : List (ℝ×(E →L[ℝ] E))) (hl : ∀ c ∈ l, 0 < c.1)
    (R : E →L[ℝ] E) :
    variance (fun x => gaussianLinearBackward μ l f (R x)) (stdGaussian E) ≤
      (Real.pi^2/8)*((L:ℝ)*‖R‖)^2 := by
  obtain ⟨D',hD',hd',hb⟩ := gaussianLinearBackward_C1 μ hf hd hD l hl
  apply stdGaussian_variance_le_of_fderiv_bound
    (D := fun x => (D' (R x)).comp R)
    (fun x => (hd' (R x)).comp x R.hasFDerivAt)
  · exact Continuous.clm_comp (hD'.comp R.continuous) continuous_const
  · positivity
  · intro x
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg R))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_VarianceProdMemLp
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
section GeneralProductVariance
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma variance_prod_le_memLp {F : X × Y → ℝ}
    (hp : MemLp F 2 (μ.prod ν)) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hh : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 μ) {A B : ℝ}
    (hA : ∀ x, variance (fun y => F (x,y)) ν ≤ A)
    (hB : variance (fun x => ∫ y, F (x,y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ A+B := by
  have hi : (∫ x, ∫ y, F (x,y)^2 ∂ν ∂μ) ≤ A+∫ x, (∫ y, F (x,y) ∂ν)^2 ∂μ := by
    calc
      _ ≤ ∫ x, (A+(∫ y, F (x,y) ∂ν)^2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left
          ((integrable_const A).add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply, Pi.add_apply] using sub_le_iff_le_add.mp hv
      _ = _ := by rw [integral_add (integrable_const _) hh.integrable_sq]; simp
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,
    integral_prod _ (hp.integrable (by norm_num))]
  linarith

end GeneralProductVariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_data_bound {W W' : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hWm' : Measurable W') (hVm : Measurable V) {K K' C c : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hW' : ∀ s, |W' s| ≤ K') (hV : ∀ s, ‖V s‖ ≤ C)
    (hWc : ∀ s, |W s-W' s| ≤ c) (x : E) :
    |vectorLogPartition ρ W V x-vectorLogPartition ρ W' V x| ≤ c := by
  exact abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (vectorPartition_integrable ρ hWm' hVm hW' hV x)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (vectorPartition_pos ρ hWm' hVm hW' hV x)
    (fun s => by simpa only [add_sub_add_right_eq_sub] using hWc s)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianLinearVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma memLp_prod_of_conditional_square {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G : X → ℝ} (hF : Measurable F) (hG : MemLp G 2 μ)
    (K : ℝ) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hb : ∀ x, (∫ y, (F (x,y)-G x)^2 ∂ν) ≤ K) : MemLp F 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hF.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (hs x).integrable_sq),?_⟩
  have hi : Integrable (fun x => 2*K+2*(G x)^2) μ :=
    (integrable_const _).add (hG.integrable_sq.const_mul 2)
  apply hi.mono' (hF.pow_const 2).aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs,abs_sq]
    rw [abs_of_nonneg (integral_nonneg (fun y : Y => sq_nonneg (F (x,y))))]
    have hi1 : Integrable (fun y => (F (x,y)-G x)^2) ν :=
      ((hs x).sub (memLp_const (G x))).integrable_sq
    calc
      _ ≤ ∫ y, 2*(F (x,y)-G x)^2+2*(G x)^2 ∂ν := by
        apply integral_mono (hs x).integrable_sq ((hi1.const_mul 2).add (integrable_const _))
        intro y
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (F (x,y)-2*G x)]
      _ = 2*(∫ y, (F (x,y)-G x)^2 ∂ν)+2*(G x)^2 := by
        rw [integral_add (hi1.const_mul 2) (integrable_const _),integral_const_mul]
        simp
      _ ≤ _ := by linarith [hb x]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linearCascadeWord_pos (A : ℕ → E →L[ℝ] E) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0<z i) : ∀ c ∈ linearCascadeWord A k z, 0 < c.1 := by
  induction k with
  | zero => simp [linearCascadeWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma gaussianLinearCascadeLog_variance (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f : E → ℝ} {D : E → StrongDual ℝ E} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hd : ∀ x, HasFDerivAt f (D x) x) (hD : Continuous D)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let ν : ProbabilityMeasure E := gaussianMarkLaw
    let μ := (stdGaussian E).prod (decoratedCascadeLaw ν k z)
    MemLp (gaussianLinearCascadeLog A R f k) 2 μ ∧
      variance (gaussianLinearCascadeLog A R f k) μ ≤
        cascadeLogFluctuationConstant k z+(Real.pi^2/8)*((L:ℝ)*‖R‖)^2 := by
  let ν : ProbabilityMeasure E := gaussianMarkLaw
  let : IsGaussian (ν:Measure E) := (inferInstance : IsGaussian (stdGaussian E))
  let ρ := decoratedCascadeLaw ν k z
  let F := gaussianLinearCascadeLog A R f k
  let G := fun a => gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) f (R a)
  have hr := gaussianLinearRecursion_realization ν A hf k z hz0
  have hmH : Measurable (fun x : ℕ → E => f (x 0)) :=
    hf.continuous.measurable.comp (measurable_pi_apply 0)
  have hG : MemLp G 2 (stdGaussian E) := lipschitz_memLp_stdGaussian
    ((gaussianLinearBackward_lipschitz (stdGaussian E) hf _
      (linearCascadeWord_nonneg A k z (fun i => (hz0 i).le))).comp R.lipschitz)
  have hsec (a : E) : MemLp (fun η => F (a,η)) 2 (ρ:Measure _) ∧
      (∫ η, (F (a,η)-G a)^2 ∂ρ) ≤ cascadeLogFluctuationConstant k z := by
    have H := finiteCascade_terminal_log_second_moment_bound ν (gaussianLinearMarkStep A)
      (gaussianLinearMarkStep_measurable A) k z hz hz0 hz1 hmH hr.2 (fun _ => R a)
    rw [hr.1] at H
    exact H
  have hmean (a : E) : (∫ η, F (a,η) ∂ρ)=G a := by
    have H := finiteCascade_terminal_log_recursion_of_fractional ν (gaussianLinearMarkStep A)
      (gaussianLinearMarkStep_measurable A) k z hz hz0 hz1 hmH hr.2 (fun _ => R a)
    rw [hr.1] at H
    exact H
  have hF := gaussianLinearCascadeLog_measurable A R hf.continuous.measurable k z
  have hp := memLp_prod_of_conditional_square (stdGaussian E) ρ hF hG
    (cascadeLogFluctuationConstant k z) (fun a => (hsec a).1) (fun a => (hsec a).2)
  have hmean' : (fun a => ∫ η, F (a,η) ∂ρ)=G := funext hmean
  refine ⟨hp,?_⟩
  apply variance_prod_le_memLp (stdGaussian E) (ρ:Measure (DecoratedCascade E k))
    (F := F) hp (fun a => (hsec a).1) (hmean'.symm ▸ hG)
  · intro a
    rw [variance_eq_integral (hsec a).1.aestronglyMeasurable.aemeasurable,hmean]
    exact (hsec a).2
  · rw [hmean']
    exact gaussianLinearBackward_root_variance (stdGaussian E) hf hd hD _
      (linearCascadeWord_pos A k z hz0) R
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_EnrichedConcentration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma enrichedTerminal_C1 (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (htop : ℝ) :
    ∃ D : EnrichedMark (n+1) (n+1) p → StrongDual ℝ (EnrichedMark (n+1) (n+1) p),
      Continuous D ∧ ∀ x, HasFDerivAt (enrichedTerminal n M f g p u htop) (D x) x := by
  let W := normalizedPatternEnergy (n+1) M f g
  let V := fun x : NormalizedSpin (n+1) => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)
  have hW : Continuous W := (normalizedPatternEnergy_continuous (n+1) M f).comp
    (continuous_const.prodMk continuous_id)
  have hV : Continuous V := (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  have hWB : ∀ x, |W x| ≤ (M:ℝ)*‖f‖ := normalizedPatternEnergy_bound _ _ _ _
  have hVB : ∀ x, ‖V x‖ ≤ enrichedFeatureBound (n+1) u := fun x => by
    change ‖innerSL ℝ (sourceEnrichedFeature (n+1) p u x)‖ ≤ _
    rw [innerSL_apply_norm,sourceEnrichedFeature_norm]
  refine ⟨vectorLogDerivative (unitSphereLaw (n+1)) W V,
    vectorLogDerivative_continuous (unitSphereLaw (n+1)) hW.measurable hV.measurable
      (enrichedFeatureBound (n+1) u).coe_nonneg hWB hVB,?_⟩
  intro x
  exact (vectorLogPartition_hasFDerivAt (unitSphereLaw (n+1)) hW.measurable hV.measurable
    (enrichedFeatureBound (n+1) u).coe_nonneg hWB hVB x).sub_const _

lemma enrichedCascadeLog_fixed_patterns_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    MemLp (enrichedCascadeLog n M k f g p d u h) 2 (enrichedDisorderLaw n k p z) ∧
      variance (enrichedCascadeLog n M k f g p d u h) (enrichedDisorderLaw n k p z) ≤
        cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
          ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2 := by
  obtain ⟨D,hD,hd⟩ := enrichedTerminal_C1 n M f g p u (h (Fin.last k))
  exact gaussianLinearCascadeLog_variance (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (enrichedTerminal_lipschitz n M f g p u _) hd hD k z hz hz0 hz1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianLinearStability
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy
section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussianLinearBackward_bounded_difference {f g : E → ℝ} {L L' : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith L' g) {C : ℝ}
    (hC : ∀ x, |f x-g x| ≤ C)
    (l : List (ℝ×(E →L[ℝ] E))) (hl : ∀ c ∈ l, 0 ≤ c.1) (x : E) :
    |gaussianLinearBackward μ l f x-gaussianLinearBackward μ l g x| ≤ C := by
  induction l generalizing x with
  | nil => exact hC x
  | cons c l ih =>
    have hl' : ∀ d ∈ l, 0 ≤ d.1 := fun d hd => hl d (List.mem_cons_of_mem c hd)
    have hF := gaussianLinearBackward_lipschitz μ hf l hl'
    have hG := gaussianLinearBackward_lipschitz μ hg l hl'
    exact entropicMean_bounded_difference μ
      (fun a => gaussian_integrable_exp_linear_shift μ hF c.2 a x)
      (fun a => gaussian_integrable_exp_linear_shift μ hG c.2 a x)
      (hl c List.mem_cons_self) (ae_of_all _ fun y => ih hl' (x+c.2 y))
end

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianLinearCascadeLog_mean_difference (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    {f g : E → ℝ} {L L' : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith L' g)
    {C : ℝ} (hC : ∀ x, |f x-g x| ≤ C)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let μ := (stdGaussian E).prod
      (decoratedCascadeLaw (gaussianMarkLaw : ProbabilityMeasure E) k z)
    |(∫ a, gaussianLinearCascadeLog A R f k a ∂μ)-
      (∫ a, gaussianLinearCascadeLog A R g k a ∂μ)| ≤ C := by
  dsimp only
  rw [(gaussianLinearCascadeLog_mean A R hf k z hz hz0 hz1).2,
    (gaussianLinearCascadeLog_mean A R hg k z hz hz0 hz1).2]
  have hi {h : E → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) :
      Integrable (fun a => gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) h (R a))
        (stdGaussian E) :=
    (lipschitz_memLp_stdGaussian ((gaussianLinearBackward_lipschitz (stdGaussian E) hh _
      (linearCascadeWord_nonneg A k z (fun i => (hz0 i).le))).comp R.lipschitz)).integrable (by norm_num)
  rw [← integral_sub (hi hf) (hi hg)]
  simpa using norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun a => gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) f (R a)-
      gaussianLinearBackward (stdGaussian E) (linearCascadeWord A k z) g (R a))
    (C := C) (ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using
        gaussianLinearBackward_bounded_difference (stdGaussian E) hf hg hC _
          (linearCascadeWord_nonneg A k z (fun i => (hz0 i).le)) (R a))
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_EnrichedPatternMean
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma enrichedTerminal_parameters_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (htop : ℝ) :
    Measurable (fun a : (Fin M → Fin (n+1) → ℝ) × EnrichedMark (n+1) (n+1) p =>
      enrichedTerminal n M f a.1 p u htop a.2) := by
  let V := fun x : NormalizedSpin (n+1) => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)
  have hV : Continuous V := (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  have hW := normalizedPatternEnergy_continuous (n+1) M f
  have hm : Measurable (fun a : ((Fin M → Fin (n+1) → ℝ) × EnrichedMark (n+1) (n+1) p) × NormalizedSpin (n+1) =>
      Real.exp (normalizedPatternEnergy (n+1) M f a.1.1 a.2+V a.2 a.1.2)) :=
    ((hW.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).add
      ((hV.comp continuous_snd).clm_apply (continuous_snd.comp continuous_fst))).rexp.measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.log.sub_const _

lemma enrichedCascadeLog_parameters_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) :
    Measurable (fun a : (Fin M → Fin (n+1) → ℝ) ×
        (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k) =>
      enrichedCascadeLog n M k f a.1 p d u h a.2) := by
  have hh := gaussianLinearCascadeLog_parameter_measurable
    (P := Fin M → Fin (n+1) → ℝ) (E := EnrichedMark (n+1) (n+1) p)
    (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (H := fun g => enrichedTerminal n M f g p u (h (Fin.last k)))
    (enrichedTerminal_parameters_measurable n M f p u (h (Fin.last k))) k z
  simpa only [enrichedCascadeLog,gaussianLinearCascadeLog] using hh

lemma enrichedExpectedLog_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) :
    Measurable (enrichedExpectedLog n M k f p d u h z) :=
  (enrichedCascadeLog_parameters_measurable n M k f p d u h z).stronglyMeasurable.integral_prod_right'.measurable

lemma enrichedTerminal_pattern_change (n M M' : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (g' : Fin M' → Fin (n+1) → ℝ)
    (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (htop : ℝ) {C : ℝ}
    (hC : ∀ x, |normalizedPatternEnergy (n+1) M f g x-
      normalizedPatternEnergy (n+1) M' f g' x| ≤ C)
    (a : EnrichedMark (n+1) (n+1) p) :
    |enrichedTerminal n M f g p u htop a-enrichedTerminal n M' f g' p u htop a| ≤ C := by
  have hW (M : ℕ) (g : Fin M → Fin (n+1) → ℝ) :
      Continuous (normalizedPatternEnergy (n+1) M f g) :=
    (normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_const.prodMk continuous_id)
  have hV : Continuous (fun x : NormalizedSpin (n+1) => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) :=
    (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  simp only [enrichedTerminal,sub_sub_sub_cancel_right]
  exact vectorLogPartition_data_bound (unitSphereLaw (n+1)) (hW M g).measurable (hW M' g').measurable
    hV.measurable (normalizedPatternEnergy_bound _ _ _ _) (normalizedPatternEnergy_bound _ _ _ _)
    (C := enrichedFeatureBound (n+1) u)
    (fun x => by rw [innerSL_apply_norm,sourceEnrichedFeature_norm]) hC a

lemma enrichedExpectedLog_pattern_change (n M M' k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (g' : Fin M' → Fin (n+1) → ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) {C : ℝ}
    (hC : ∀ x, |normalizedPatternEnergy (n+1) M f g x-
      normalizedPatternEnergy (n+1) M' f g' x| ≤ C) :
    |enrichedExpectedLog n M k f p d u h z g-enrichedExpectedLog n M' k f p d u h z g'| ≤ C :=
  gaussianLinearCascadeLog_mean_difference (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (enrichedTerminal_lipschitz n M f g p u _) (enrichedTerminal_lipschitz n M' f g' p u _)
    (enrichedTerminal_pattern_change n M M' f g g' p u _ hC) k z hz hz0 hz1

lemma normalizedPatternEnergy_update (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin N → ℝ) (a : Fin M) (v : Fin N → ℝ) (x : NormalizedSpin N) :
    |normalizedPatternEnergy N M f (Function.update g a v) x-normalizedPatternEnergy N M f g x| ≤ 2*‖f‖ := by
  classical
  unfold normalizedPatternEnergy
  rw [← Finset.sum_sub_distrib]
  have he : (∑ b : Fin M, (f (∑ i, (Function.update g a v) b i*x.val i)-f (∑ i, g b i*x.val i)))=
      f (∑ i, v i*x.val i)-f (∑ i, g a i*x.val i) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [he]
  exact (abs_sub _ _).trans (by
    have hb := f.norm_coe_le_norm (∑ i, v i*x.val i)
    have ha := f.norm_coe_le_norm (∑ i, g a i*x.val i)
    simp only [Real.norm_eq_abs] at hb ha
    linarith)

lemma enrichedExpectedLog_update (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (g : Fin M → Fin (n+1) → ℝ) (a : Fin M) (v : Fin (n+1) → ℝ) :
    |enrichedExpectedLog n M k f p d u h z (Function.update g a v)-
      enrichedExpectedLog n M k f p d u h z g| ≤ 2*‖f‖ :=
  enrichedExpectedLog_pattern_change n M M k f _ _ p d u h z hz hz0 hz1
    (normalizedPatternEnergy_update (n+1) M f g a v)

lemma enrichedExpectedLog_bounded (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    ∃ C : ℝ, ∀ g, |enrichedExpectedLog n M k f p d u h z g| ≤ C := by
  refine ⟨|enrichedExpectedLog n M k f p d u h z 0|+2*(M:ℝ)*‖f‖,fun g => ?_⟩
  have hh := enrichedExpectedLog_pattern_change n M M k f g 0 p d u h z hz hz0 hz1
    (C := 2*(M:ℝ)*‖f‖) (fun x => (abs_sub _ _).trans (by
      have h1 := normalizedPatternEnergy_bound (n+1) M f g x
      have h0 := normalizedPatternEnergy_bound (n+1) M f 0 x
      linarith))
  have ht := abs_sub_le (enrichedExpectedLog n M k f p d u h z g)
    (enrichedExpectedLog n M k f p d u h z 0) 0
  simp only [sub_zero] at ht
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MeasurableVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy
variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem variance_pi_le_of_measurable_bounded_differences (n : ℕ) {F : (Fin n → X) → ℝ}
    (hF : Measurable F) {K c : ℝ} (hK : ∀ x, |F x| ≤ K)
    (hdiff : ∀ x i y, |F (Function.update x i y) - F x| ≤ c) :
    variance F (Measure.pi fun _ : Fin n => μ) ≤ (n : ℝ) * c ^ 2 := by
  classical
  induction n with
  | zero =>
      rw [Measure.pi_of_empty]
      simp
  | succ n ih =>
      let ν := Measure.pi fun _ : Fin n => μ
      let G : X × (Fin n → X) → ℝ := fun p => F (Fin.cons (α := fun _ => X) p.1 p.2)
      have hG : Measurable G := hF.comp (measurableEmbedding_fin_cons (X := X) n).measurable
      have hGK (p) : |G p| ≤ K := hK _
      have hA (x : X) : variance (fun y => G (x, y)) ν ≤ (n : ℝ) * c ^ 2 := by
        apply ih (hG.comp (measurable_const.prodMk measurable_id)) (fun y => hGK (x,y))
        intro y i z
        simpa only [G, Function.comp_apply, id_eq, Fin.cons_update] using hdiff (Fin.cons x y) i.succ z
      have hHc : Measurable (fun x => ∫ y, G (x, y) ∂ν) :=
        hG.stronglyMeasurable.integral_prod_right'.measurable
      have hHosc (x x' : X) :
          |(∫ y, G (x, y) ∂ν) - ∫ y, G (x', y) ∂ν| ≤ c := by
        have hi (x : X) : Integrable (fun y => G (x, y)) ν :=
          (integrable_const K).mono'
            (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => hGK (x, y))
        rw [← integral_sub (hi x) (hi x')]
        have hh : ∀ y, |G (x, y) - G (x', y)| ≤ c := by
          intro y
          have hu : Function.update (Fin.cons x' y) 0 x = Fin.cons (α := fun _ => X) x y := by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          simpa only [G, hu] using hdiff (Fin.cons x' y) 0 x
        simpa using norm_integral_le_of_norm_le_const
          (μ := ν) (f := fun y => G (x,y) - G (x',y))
          (Filter.Eventually.of_forall hh)
      have hpF : MemLp F 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
        MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
      have hpG : MemLp G 2 (μ.prod ν) :=
        MemLp.of_bound hG.aestronglyMeasurable K (Filter.Eventually.of_forall hGK)
      have hHL : MemLp (fun x => ∫ y, G (x,y) ∂ν) 2 μ :=
        MemLp.of_bound hHc.aestronglyMeasurable K (ae_of_all _ fun x => by
          simpa using norm_integral_le_of_norm_le_const (μ := ν)
            (f := fun y => G (x,y)) (ae_of_all _ fun y => hGK (x,y)))
      let x₀ : X := Classical.choice ‹Nonempty X›
      have hHrange : ∀ᵐ x ∂μ, (∫ y, G (x,y) ∂ν) ∈
          Icc ((∫ y, G (x₀,y) ∂ν)-c) ((∫ y, G (x₀,y) ∂ν)+c) := by
        exact ae_of_all _ fun x => by
          have hh := abs_le.mp (hHosc x x₀)
          constructor <;> linarith
      have hB : variance (fun x => ∫ y, G (x,y) ∂ν) μ ≤ c^2 := by
        convert variance_le_sq_of_bounded hHrange hHc.aemeasurable using 1
        all_goals try with_reducible_and_instances rfl
        ring
      have hv := variance_prod_le_memLp μ ν hpG
        (fun x => MemLp.of_bound (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          K (ae_of_all _ fun y => hGK (x,y))) hHL hA hB
      rw [variance_eq_sub hpG] at hv
      rw [variance_eq_sub hpF]
      have hmean := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) F
      have hsquare := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) (fun x => F x ^ 2)
      change (∫ x, G x ∂μ.prod ν) = _ at hmean
      change (∫ x, G x ^ 2 ∂μ.prod ν) = _ at hsquare
      simp only [Pi.pow_apply] at hv ⊢
      rw [hsquare, hmean] at hv
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hv

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_EnrichedPatternVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma enrichedExpectedLog_memLp (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    MemLp (enrichedExpectedLog n M k f p d u h z) 2 (finitePatternRowsLaw (n+1) M) := by
  obtain ⟨C,hC⟩ := enrichedExpectedLog_bounded n M k f p d u h z hz hz0 hz1
  exact MemLp.of_bound (enrichedExpectedLog_measurable n M k f p d u h z).aestronglyMeasurable
    C (ae_of_all _ hC)

lemma enrichedExpectedLog_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    variance (enrichedExpectedLog n M k f p d u h z) (finitePatternRowsLaw (n+1) M) ≤
      (M:ℝ)*(2*‖f‖)^2 := by
  obtain ⟨C,hC⟩ := enrichedExpectedLog_bounded n M k f p d u h z hz hz0 hz1
  exact variance_pi_le_of_measurable_bounded_differences
    (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) M
    (enrichedExpectedLog_measurable n M k f p d u h z) hC
    (enrichedExpectedLog_update n M k f p d u h z hz hz0 hz1)

lemma enrichedFixedCountLog_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let μ := (finitePatternRowsLaw (n+1) M).prod (enrichedDisorderLaw n k p z)
    MemLp (enrichedFixedCountLog n M k f p d u h) 2 μ ∧
      variance (enrichedFixedCountLog n M k f p d u h) μ ≤
        cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
          ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2+(M:ℝ)*(2*‖f‖)^2 := by
  let μ := finitePatternRowsLaw (n+1) M
  let ν := enrichedDisorderLaw n k p z
  let F := enrichedFixedCountLog n M k f p d u h
  let G := enrichedExpectedLog n M k f p d u h z
  let K := cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
    ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2
  have hG : MemLp G 2 μ := enrichedExpectedLog_memLp n M k f p d u h z hz hz0 hz1
  have hs (g : Fin M → Fin (n+1) → ℝ) :
      MemLp (fun a => F (g,a)) 2 ν ∧ variance (fun a => F (g,a)) ν ≤ K :=
    enrichedCascadeLog_fixed_patterns_variance n M k f g p d u h z hz hz0 hz1
  have hp : MemLp F 2 (μ.prod ν) := memLp_prod_of_conditional_square μ ν
    (enrichedCascadeLog_parameters_measurable n M k f p d u h z) hG K (fun g => (hs g).1)
    (fun g => by
      have hv := (hs g).2
      rw [variance_eq_integral (hs g).1.aestronglyMeasurable.aemeasurable] at hv
      exact hv)
  refine ⟨hp,?_⟩
  exact variance_prod_le_memLp μ ν hp (fun g => (hs g).1) hG (fun g => (hs g).2)
    (enrichedExpectedLog_variance n M k f p d u h z hz hz0 hz1)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountMixtureVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma memLp_prod_of_conditional_square_function {X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G A : X → ℝ} (hF : Measurable F) (hG : MemLp G 2 μ)
    (hA : Integrable A μ) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hb : ∀ x, (∫ y, (F (x,y)-G x)^2 ∂ν) ≤ A x) : MemLp F 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hF.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (hs x).integrable_sq),?_⟩
  have hi : Integrable (fun x => 2*A x+2*(G x)^2) μ :=
    (hA.const_mul 2).add (hG.integrable_sq.const_mul 2)
  apply hi.mono' (hF.pow_const 2).aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs,abs_sq]
    rw [abs_of_nonneg (integral_nonneg (fun y : Y => sq_nonneg (F (x,y))))]
    have hi1 : Integrable (fun y => (F (x,y)-G x)^2) ν :=
      ((hs x).sub (memLp_const (G x))).integrable_sq
    calc
      _ ≤ ∫ y, 2*(F (x,y)-G x)^2+2*(G x)^2 ∂ν := by
        apply integral_mono (hs x).integrable_sq ((hi1.const_mul 2).add (integrable_const _))
        intro y
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (F (x,y)-2*G x)]
      _ = 2*(∫ y, (F (x,y)-G x)^2 ∂ν)+2*(G x)^2 := by
        rw [integral_add (hi1.const_mul 2) (integrable_const _),integral_const_mul]
        simp
      _ ≤ _ := by linarith [hb x]

lemma variance_prod_le_integral {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X × Y → ℝ} (hp : MemLp F 2 (μ.prod ν))
    (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hh : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 μ) {A : X → ℝ} {B : ℝ}
    (hAi : Integrable A μ) (hA : ∀ x, variance (fun y => F (x,y)) ν ≤ A x)
    (hB : variance (fun x => ∫ y, F (x,y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ (∫ x, A x ∂μ)+B := by
  have hi : (∫ x, ∫ y, F (x,y)^2 ∂ν ∂μ) ≤ (∫ x, A x ∂μ)+∫ x, (∫ y, F (x,y) ∂ν)^2 ∂μ := by
    calc
      _ ≤ ∫ x, (A x+(∫ y, F (x,y) ∂ν)^2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left (hAi.add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply,Pi.add_apply] using sub_le_iff_le_add.mp hv
      _ = _ := integral_add hAi hh.integrable_sq
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,integral_prod _ (hp.integrable (by norm_num))]
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_EnrichedPoissonVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma patternPrefix_measurePreserving (N M : ℕ) : MeasurePreserving (patternPrefix N M)
    (infinitePatternRowsLaw N) (finitePatternRowsLaw N M) := by
  refine ⟨patternPrefix_measurable N M,?_⟩
  change Measure.map (fun g : ℕ → Fin N → ℝ => fun a : Fin M => g a.val)
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin N => gaussianReal 0 1)=
    Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

lemma normalizedPatternEnergy_prefix_succ (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : ℕ → Fin N → ℝ) (x : NormalizedSpin N) :
    |normalizedPatternEnergy N (M+1) f (patternPrefix N (M+1) g) x-
      normalizedPatternEnergy N M f (patternPrefix N M g) x| ≤ ‖f‖ := by
  unfold normalizedPatternEnergy
  rw [Fin.sum_univ_castSucc]
  simp only [patternPrefix,Fin.val_castSucc,Fin.val_last,add_sub_cancel_left]
  simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (∑ i, g M i*x.val i)

lemma enrichedPoissonLog_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) :
    Measurable (enrichedPoissonLog n k f p d u h) := by
  apply measurable_from_prod_countable_right
  intro M
  have hh := (enrichedCascadeLog_parameters_measurable n M k f p d u h z).comp
    (((patternPrefix_measurable (n+1) M).comp
      (measurable_fst (α := ℕ → Fin (n+1) → ℝ)
        (β := EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k))).prodMk measurable_snd)
  simpa only [enrichedPoissonLog,Function.comp_def] using hh

lemma enrichedPoissonLog_section_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    MemLp (fun a => enrichedPoissonLog n k f p d u h (M,a)) 2 (enrichedRowsDisorderLaw n k p z) ∧
      variance (fun a => enrichedPoissonLog n k f p d u h (M,a)) (enrichedRowsDisorderLaw n k p z) ≤
      cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
        ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2+(M:ℝ)*(2*‖f‖)^2 := by
  let E := EnrichedMark (n+1) (n+1) p
  let D := E × DecoratedCascade E k
  have hp : MeasurePreserving (fun a : (ℕ → Fin (n+1) → ℝ) × D =>
      (patternPrefix (n+1) M a.1,a.2))
      ((infinitePatternRowsLaw (n+1)).prod (enrichedDisorderLaw n k p z))
      ((finitePatternRowsLaw (n+1) M).prod (enrichedDisorderLaw n k p z)) :=
    (patternPrefix_measurePreserving (n+1) M).prod
      (MeasurePreserving.id (enrichedDisorderLaw n k p z))
  have hs := enrichedFixedCountLog_variance n M k f p d u h z hz hz0 hz1
  have hl := hs.1.comp_measurePreserving hp
  have hv := (hp.variance_fun_comp hs.1.aestronglyMeasurable.aemeasurable).trans_le hs.2
  constructor
  · simpa only [Function.comp_def,enrichedFixedCountLog,enrichedPoissonLog,enrichedRowsDisorderLaw] using hl
  · simpa only [enrichedFixedCountLog,enrichedPoissonLog,enrichedRowsDisorderLaw] using hv

lemma enrichedPoissonLog_mean_succ (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (M : ℕ) :
    |(∫ a, enrichedPoissonLog n k f p d u h (M+1,a) ∂enrichedRowsDisorderLaw n k p z)-
      ∫ a, enrichedPoissonLog n k f p d u h (M,a) ∂enrichedRowsDisorderLaw n k p z| ≤ ‖f‖ := by
  let μ := infinitePatternRowsLaw (n+1)
  let G (M : ℕ) := fun g => enrichedExpectedLog n M k f p d u h z (patternPrefix (n+1) M g)
  have hG (M : ℕ) : MemLp (G M) 2 μ :=
    (enrichedExpectedLog_memLp n M k f p d u h z hz hz0 hz1).comp_measurePreserving
      (patternPrefix_measurePreserving (n+1) M)
  have he (M : ℕ) : (∫ a, enrichedPoissonLog n k f p d u h (M,a) ∂enrichedRowsDisorderLaw n k p z)=
      ∫ g, G M g ∂μ :=
    integral_prod _ ((enrichedPoissonLog_section_variance n M k f p d u h z hz hz0 hz1).1.integrable (by norm_num))
  rw [he,he,← integral_sub ((hG (M+1)).integrable (by norm_num)) ((hG M).integrable (by norm_num))]
  have hh (g) : |G (M+1) g-G M g| ≤ ‖f‖ :=
    enrichedExpectedLog_pattern_change n (M+1) M k f _ _ p d u h z hz hz0 hz1
      (normalizedPatternEnergy_prefix_succ (n+1) M f g)
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := fun g => G (M+1) g-G M g)
    (ae_of_all _ hh)

lemma enrichedPoissonLog_variance (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (r : ℝ≥0) :
    let μ := (poissonMeasure r).prod (enrichedRowsDisorderLaw n k p z)
    MemLp (enrichedPoissonLog n k f p d u h) 2 μ ∧
      variance (enrichedPoissonLog n k f p d u h) μ ≤
      cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
        ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2+
          (r:ℝ)*(2*‖f‖)^2+‖f‖^2*((r:ℝ)+1) := by
  let ν := enrichedRowsDisorderLaw n k p z
  let F := enrichedPoissonLog n k f p d u h
  let G := fun M => ∫ a, F (M,a) ∂ν
  let K := cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
        ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2
  let A := fun M : ℕ => K+(M:ℝ)*(2*‖f‖)^2
  have hGdiff := enrichedPoissonLog_mean_succ n k f p d u h z hz hz0 hz1
  have hG : MemLp G 2 (poissonMeasure r) := poisson_bounded_increment_memLp r (norm_nonneg f) hGdiff
  have hAi : Integrable A (poissonMeasure r) :=
    (integrable_const K).add ((poisson_nat_memLp r).integrable (by norm_num) |>.mul_const _)
  have hs (M) := enrichedPoissonLog_section_variance n M k f p d u h z hz hz0 hz1
  have hp : MemLp F 2 ((poissonMeasure r).prod ν) :=
    memLp_prod_of_conditional_square_function (poissonMeasure r) ν
      (enrichedPoissonLog_measurable n k f p d u h z) hG hAi (fun M => (hs M).1)
      (fun M => by
        have hv := (hs M).2
        rw [variance_eq_integral (hs M).1.aestronglyMeasurable.aemeasurable] at hv
        exact hv)
  refine ⟨hp,?_⟩
  have hv := variance_prod_le_integral (poissonMeasure r) ν hp (fun M => (hs M).1) hG hAi
    (fun M => (hs M).2) (poisson_bounded_increment_variance r (norm_nonneg f) hGdiff)
  have he : (∫ M, A M ∂poissonMeasure r)=K+(r:ℝ)*(2*‖f‖)^2 := by
    rw [integral_add (integrable_const K) ((poisson_nat_memLp r).integrable (by norm_num) |>.mul_const _)]
    simp only [integral_const,integral_mul_const,poisson_nat_mean]
    simp
  rw [he] at hv
  exact hv

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

variable {S I : Type} [MeasurableSpace S] [Fintype I]
variable (ρ : Measure S) [IsProbabilityMeasure ρ]
variable {W : S → ℝ} {V : S → EuclideanSpace ℝ I}
variable (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
variable (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)

include hWm hVm hW hV

lemma vectorPartition_exp_terminal (c : ℝ) (a : EuclideanSpace ℝ I) :
    (∫ s, Real.exp (W s+inner ℝ (V s) a-c) ∂ρ) =
      Real.exp (vectorLogPartition ρ W (fun s => innerSL ℝ (V s)) a-c) := by
  have hm : Measurable (fun s => innerSL ℝ (V s)) := (innerSL ℝ).continuous.measurable.comp hVm
  have hb : ∀ s, ‖innerSL ℝ (V s)‖ ≤ C := by simpa only [innerSL_apply_norm] using hV
  simp only [Real.exp_sub,integral_div,vectorLogPartition]
  rw [Real.exp_log (vectorPartition_pos ρ hWm hm hW hb a)]
  rfl

lemma indexedGaussian_spin_partition (n : ℕ) (root : I → ℝ) (step : ℕ → I → ℝ)
    (b : IndexedCascadeBase n) (c : ℝ) (g : ℕ → ℝ) :
    tiltPartition (ρ.prod (indexedLeafProbability n b)) (fun x => W x.1+
      countableGaussianField (indexedGaussianRow n (hierarchyRowCoefficients n root step) V)
        (indexedGaussianRowLength (I := I) n) g x-c) 1 =
    ∫ l, Real.exp (vectorLogPartition ρ W (fun s => innerSL ℝ (V s))
      (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
        ((fun _ => diagonalMark root (indexedGaussianDisorder n I g).1),
          (indexedGaussianDisorder n I g).2) l 0)-c) ∂indexedLeafProbability n b := by
  let F : S×IndexedLeaf n → ℝ := fun x => W x.1+
      countableGaussianField (indexedGaussianRow n (hierarchyRowCoefficients n root step) V)
        (indexedGaussianRowLength (I := I) n) g x-c
  have hm : Measurable F := ((hWm.comp measurable_fst).add
    ((countableGaussianField_measurable (indexedGaussianRow_measurable n _ hVm)
      (indexedGaussianRowLength_measurable n)).comp (measurable_const.prodMk measurable_id))).sub measurable_const
  change (∫ x, Real.exp (1*F x) ∂ρ.prod (indexedLeafProbability n b)) = _
  simp only [one_mul]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le) hm.exp.aestronglyMeasurable,
    lintegral_prod_symm _ hm.exp.ennreal_ofReal.aemeasurable]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (measurable_of_countable _).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro l
  let a := indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
    ((fun _ => diagonalMark root (indexedGaussianDisorder n I g).1),
      (indexedGaussianDisorder n I g).2) l 0
  have he (s : S) : F (s,l) = W s+inner ℝ (V s) a-c := by
    dsimp only [F]
    rw [indexedGaussianRow_diagonal_identity]
  simp_rw [he]
  rw [← vectorPartition_exp_terminal ρ hWm hVm hW hV c a]
  apply (ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  have hv' : ∀ s, ‖innerSL ℝ (V s)‖ ≤ C := by simpa only [innerSL_apply_norm] using hV
  have hi := vectorPartition_integrable ρ hWm ((innerSL ℝ).continuous.measurable.comp hVm) hW hv' a
  simpa only [Real.exp_sub,Function.comp_apply,innerSL_apply_apply] using hi.div_const (Real.exp c)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma enrichedIncrementMap_profile {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) (j : ℕ) :
    enrichedIncrementMap p d h j = diagonalMark (profileGaussianStep (enrichedCoordinateLevel p d h) j) := by
  by_cases hj : j<k
  · rw [enrichedIncrementMap,dite_eq_left hj]
    congr 1
    funext i
    simp only [profileGaussianStep,dite_eq_left hj]
  · apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [enrichedIncrementMap,profileGaussianStep,hj,diagonalMark_apply]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCoupling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceEnrichedFeature_measurable (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ) :
    Measurable (sourceEnrichedFeature N p u) :=
  (enrichedFeature_continuous N N p (Real.sqrt N) (perturbationAmplitude N u)).measurable

lemma enrichedIndexedHamiltonian_spin_partition (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (g : ℕ → ℝ)
    (b : IndexedCascadeBase k) :
    tiltPartition (enrichedIndexedBaseMeasure n k b)
      (enrichedIndexedHamiltonian n M k f a p d h u g) 1 =
    ∫ l, Real.exp (enrichedTerminal n M f a p u (h (Fin.last k))
      (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
        ((fun _ => enrichedRootMap p d h (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1),
          (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2) l 0))
      ∂indexedLeafProbability k b := by
  let root := profileGaussianRoot (enrichedCoordinateLevel p d h)
  let step := profileGaussianStep (enrichedCoordinateLevel p d h)
  have hWc : Continuous (normalizedPatternEnergy (n+1) M f a) :=
    (normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_const.prodMk continuous_id)
  have hWm := hWc.measurable
  have hp := indexedGaussian_spin_partition (unitSphereLaw (n+1)) hWm
    (sourceEnrichedFeature_measurable (n+1) p u)
    (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => (sourceEnrichedFeature_norm (n+1) p u x).le) k root step b ((n+1:ℕ)*h (Fin.last k)) g
  have hA : enrichedIncrementMap p d h = fun j => diagonalMark (step j) :=
    funext (enrichedIncrementMap_profile p d h)
  have hR : enrichedRootMap p d h = diagonalMark root := rfl
  rw [hA,hR]
  unfold enrichedIndexedBaseMeasure
  convert hp using 2
  · funext x
    unfold enrichedIndexedHamiltonian countableGaussianHamiltonian enrichedIndexedBoundedEnergy sourceGaussianRow
    dsimp only [root,step]
    ring
  · rfl

lemma enrichedIndexedHamiltonian_partition (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (g : ℕ → ℝ)
    (b : IndexedCascadeBase k) (hb : IndexedCascadeGood k b)
    (hb' : 0 < ((indexedLeafMeasure k b) univ).toReal) :
    Real.log (tiltPartition (enrichedIndexedBaseMeasure n k b)
      (enrichedIndexedHamiltonian n M k f a p d h u g) 1) =
      enrichedCascadeLog n M k f a p d u h
        ((indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1,
          indexedCascadeRealize k (b,(indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2)) := by
  rw [enrichedIndexedHamiltonian_spin_partition]
  have hH : Measurable (fun x : ℕ → EnrichedMark (n+1) (n+1) p =>
      enrichedTerminal n M f a p u (h (Fin.last k)) (x 0)) :=
    (enrichedTerminal_lipschitz n M f a p u _).continuous.measurable.comp (measurable_pi_apply 0)
  rw [indexedLeafProbability_terminal_integral
    (gaussianMarkLaw : ProbabilityMeasure (EnrichedMark (n+1) (n+1) p))
    (gaussianLinearMarkStep_measurable (enrichedIncrementMap p d h)) hH k b hb hb']
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedVarianceBound
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceCascadeRealization_preserving (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    MeasurePreserving (sourceCascadeRealization n k p)
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)
      (enrichedDisorderLaw n k p z) := by
  let E := EnrichedMark (n+1) (n+1) p
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let R := stdGaussian E
  let M := (indexedCascadeMarksLaw (gaussianMarkLaw (E := E)) k : Measure (IndexedCascadeMarks E k))
  have hg : MeasurePreserving (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p))
      countableGaussianLaw (R.prod M) :=
    ⟨indexedGaussianDisorder_measurable k _,indexedGaussianDisorder_law k _⟩
  have hr : MeasurePreserving (fun a : IndexedCascadeBase k × (E × IndexedCascadeMarks E k) =>
      (a.2.1,(a.1,a.2.2))) (B.prod (R.prod M)) (R.prod (B.prod M)) :=
    ⟨by fun_prop,prod_rotate_front B R M⟩
  have hc : MeasurePreserving (indexedCascadeRealize (S := E) k) (B.prod M)
      (decoratedCascadeLaw (gaussianMarkLaw (E := E)) k z) :=
    ⟨indexedCascadeRealize_measurable k,indexedCascadeRealize_law _ k z⟩
  exact (((MeasurePreserving.id R).prod hc).comp hr).comp ((MeasurePreserving.id B).prod hg)

lemma sourceDisorderRealization_preserving (n k : ℕ) (p : Fin (n+1) → ℕ)
    (z : Fin k → ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceDisorderRealization n k p) (sourceIndexedDisorderLaw n k z t)
      (enrichedPoissonDisorderLaw n k p z t) :=
  (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
    (sourceCascadeRealization_preserving n k p z))

lemma sourceIndexedPressure_memLp (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    MemLp (sourceIndexedPressure n k f p d u h) 2 (sourceIndexedDisorderLaw n k z t) := by
  have hp := (enrichedPoissonLog_variance n k f p d u h z hz hz0 hz1 ((n+1:ℕ)*t)).1
  exact (hp.const_mul (1/(n+1:ℕ))).comp_measurePreserving
    (sourceDisorderRealization_preserving n k p z t)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CouplingKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceDisorderReassoc_preserving (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceDisorderReassoc n k)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) (sourceIndexedDisorderLaw n k z t) := by
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  exact ((MeasurePreserving.id K).prod (measurePreserving_prodAssoc R B countableGaussianLaw)).comp
    (measurePreserving_prodAssoc K (R.prod B) countableGaussianLaw)

lemma sourceBaseData_regular (n k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ∀ᵐ a ∂sourceBaseDataLaw n k z t, IndexedCascadeGood k a.2.2 ∧
      0 < ((indexedLeafMeasure k a.2.2) univ).toReal := by
  have hp : MeasurePreserving (fun a : SourceBaseData n k => a.2.2)
      (sourceBaseDataLaw n k z t) (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) :=
    measurePreserving_snd.comp measurePreserving_snd
  exact hp.quasiMeasurePreserving.ae ((indexedCascadeGood_ae k z hz0 hz1).and
    (indexedLeafMeasure_regular k z hz hz0 hz1))

lemma sourceKernelPressure_eq (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (a : SourceBaseData n k × (ℕ → ℝ))
    (ha : IndexedCascadeGood k a.1.2.2) (ha' : 0 < ((indexedLeafMeasure k a.1.2.2) univ).toReal)
    (u : Fin (n+1) → ℝ) :
    sourceKernelPressure n k f p d u h a = sourceIndexedPressure n k f p d u h (sourceDisorderReassoc n k a) := by
  rw [sourceKernelPressure,sourceSpinLeafKernel_apply,enrichedIndexedHamiltonian_partition _ _ _ _ _ _ _ _ _ _ _ ha ha']
  rfl

lemma sourceKernelPressure_ae (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw, ∀ u,
      sourceKernelPressure n k f p d u h a = sourceIndexedPressure n k f p d u h (sourceDisorderReassoc n k a) := by
  filter_upwards [(measurePreserving_fst (μ := sourceBaseDataLaw n k z t)
    (ν := countableGaussianLaw)).quasiMeasurePreserving.ae (sourceBaseData_regular n k z hz hz0 hz1 t)] with a ha u
  exact sourceKernelPressure_eq n k f p d h a ha.1 ha.2 u

lemma sourceKernelPressure_memLp_oai (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    MemLp (sourceKernelPressure n k f p d u h) 2 ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
  have hl := (sourceIndexedPressure_memLp n k f p d u h z hz hz0 hz1 t).comp_measurePreserving
    (sourceDisorderReassoc_preserving n k z t)
  apply hl.ae_eq
  exact (sourceKernelPressure_ae n k f p d h z hz hz0 hz1 t).mono fun a ha => (ha u).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_memLp_oai := @OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_memLp_oai
