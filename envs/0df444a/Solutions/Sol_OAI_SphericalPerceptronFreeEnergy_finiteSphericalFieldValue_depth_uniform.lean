-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:23:55.685982+00:00
-- url     : https://prove2.me/submissions/cf02dd81-9e24-4536-862e-d81e0fec99b4

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

lemma cgf_second_nonneg
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    0 ≤ deriv (deriv (cgf X μ)) t := by
  have hh := iteratedDeriv_two_cgf_eq_integral
    (mem_interior_integrableExpSet_of_all μ hX t)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hh
  rw [hh]
  exact div_nonneg (integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (mgf_pos (hX t)).le

lemma cgf_deriv_monotone
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    Monotone (deriv (cgf X μ)) :=
  monotone_of_deriv_nonneg (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt)
    (cgf_second_nonneg μ hX)

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

lemma entropicMean_monotone (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    Monotone (fun p => entropicMean μ p X) := by
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  intro p q hpq
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => p*t))).intervalIntegrable 0 1)
    ((hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => q*t))).intervalIntegrable 0 1)
  intro t ht
  exact cgf_deriv_monotone μ hX (mul_le_mul_of_nonneg_right hpq ht.1)

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

lemma gaussian_integrable_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (σ : ℝ) (x : E) :
    Integrable (fun y : E => f (x+σ • y)) μ := by
  have he : integrableExpSet (fun y : E => f (x+σ • y)) μ=univ :=
    Set.eq_univ_of_forall (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)
  have ht : (0:ℝ) ∈ interior (integrableExpSet (fun y : E => f (x+σ • y)) μ) := by simp [he]
  exact (memLp_of_mem_interior_integrableExpSet ht (1:ℝ≥0)).integrable (by simp)

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussianEntropic_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p σ : ℝ} (hp : 0 ≤ p) :
    LipschitzWith L (gaussianEntropic μ p σ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,gaussianEntropic]
  apply entropicMean_bounded_difference μ
    (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)
    (fun a => gaussian_integrable_exp_lipschitz μ hf a σ y) hp
  exact ae_of_all _ fun z => by
    simpa only [Real.dist_eq,dist_add_right] using hf.dist_le_mul (x+σ • z) (y+σ • z)

lemma gaussianEntropic_mono_parameter {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (σ : ℝ) (x : E) :
    Monotone (fun p => gaussianEntropic μ p σ f x) :=
  entropicMean_monotone μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)

lemma gaussianEntropic_zero {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (σ : ℝ) (x : E) :
    gaussianEntropic μ 0 σ f x=∫ y, f (x+σ • y) ∂μ :=
  entropicMean_zero μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)

lemma gaussianEntropic_pos {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p : ℝ} (hp : p ≠ 0) (σ : ℝ) (x : E) :
    gaussianEntropic μ p σ f x=Real.log (∫ y, Real.exp (p*f (x+σ • y)) ∂μ)/p :=
  entropicMean_eq_div μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) hp

lemma gaussianEntropic_mono {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) {p : ℝ} (hp : 0 ≤ p)
    (σ : ℝ) (hfg : ∀ x, f x ≤ g x) (x : E) :
    gaussianEntropic μ p σ f x ≤ gaussianEntropic μ p σ g x :=
  entropicMean_mono_variable μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)
    (fun a => gaussian_integrable_exp_lipschitz μ hg a σ x)
    (ae_of_all _ fun noise => hfg (x+σ • noise)) hp

lemma gaussianEntropic_add_const {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (p σ c : ℝ) (x : E) :
    gaussianEntropic μ p σ (fun z => f z+c) x=gaussianEntropic μ p σ f x+c :=
  entropicMean_add_const μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) p c

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_FiniteTerminal
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

lemma canonicalRadialMass_apply {n : ℕ} {b : ℝ} (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) :
    canonicalRadialMass n b A = ENNReal.ofReal (∫ x in A, canonicalRadialDensity n b x) := by
  rw [canonicalRadialMass,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal (canonicalRadialDensity_integrable n hb).integrableOn
    (Eventually.of_forall fun x => (canonicalRadialDensity_pos n b x).le)).symm

lemma canonicalRadial_mass_le {n : ℕ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A)
    (hc : ∀ x ∈ A, -(a/2)*‖x‖^2 ≤ c-(b/2)*‖x‖^2) :
    canonicalRadialMass n a A ≤ ENNReal.ofReal (Real.exp c * b ^ (-((n+1 : ℕ) : ℝ)/2)) := by
  rw [canonicalRadialMass_apply ha hA]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ x in A, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_mono_on (canonicalRadialDensity_integrable n ha).integrableOn
        ((canonicalRadialDensity_integrable n hb).const_mul _).integrableOn hA
      intro x hx
      unfold canonicalRadialDensity
      calc
        _ ≤ radialNormalizer n * Real.exp (c-(b/2)*‖x‖^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hc x hx)) (radialNormalizer_pos n).le
        _ = _ := by rw [Real.exp_sub,neg_mul,Real.exp_neg]; ring
    _ ≤ ∫ x, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_le_integral ((canonicalRadialDensity_integrable n hb).const_mul _)
      exact Eventually.of_forall fun x => (mul_pos (Real.exp_pos c) (canonicalRadialDensity_pos n b x)).le
    _ = _ := by rw [integral_const_mul,canonicalRadialDensity_integral n hb]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_NormSquareBand
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
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

lemma canonicalRadial_upper_tail (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    canonicalRadialMass n 1 {x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2} ≤
      ENNReal.ofReal (Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ))) := by
  have hd : 0 < 1+ε := by linarith
  have hb : 0 ≤ 1-(1+ε)⁻¹ := by
    apply sub_nonneg.mpr
    exact (inv_le_one₀ hd).mpr (by linarith)
  have hid : (1-(1+ε)⁻¹)*(1+ε) = ε := by field_simp; ring
  have h := canonicalRadial_mass_le (n := n) (a := 1) (b := (1+ε)⁻¹)
    (A := {x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2})
    (c := -((n+1 : ℕ) : ℝ)*ε/2) (by norm_num) (inv_pos.mpr hd)
    (measurableSet_le measurable_const (continuous_norm.pow 2).measurable) (by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left hx hb
      have he : (1-(1+ε)⁻¹)*(((n+1 : ℕ) : ℝ)*(1+ε)) = ((n+1 : ℕ) : ℝ)*ε := by
        calc
          _ = ((n+1 : ℕ) : ℝ)*((1-(1+ε)⁻¹)*(1+ε)) := by ring
          _ = _ := by rw [hid]
      rw [he] at hh
      nlinarith)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [Real.rpow_def_of_pos (inv_pos.mpr hd),Real.log_inv,← Real.exp_add]
  congr 1
  ring

lemma canonicalRadial_lower_tail (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    canonicalRadialMass n 1 {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)} ≤
      ENNReal.ofReal (Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ))) := by
  have hd : 0 < 1-ε := sub_pos.mpr hε1
  have hb : 0 ≤ (1-ε)⁻¹-1 := by
    apply sub_nonneg.mpr
    exact (one_le_inv₀ hd).mpr (by linarith)
  have hid : ((1-ε)⁻¹-1)*(1-ε) = ε := by field_simp; ring
  have h := canonicalRadial_mass_le (n := n) (a := 1) (b := (1-ε)⁻¹)
    (A := {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)})
    (c := ((n+1 : ℕ) : ℝ)*ε/2) (by norm_num) (inv_pos.mpr hd)
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const) (by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left hx hb
      have he : ((1-ε)⁻¹-1)*(((n+1 : ℕ) : ℝ)*(1-ε)) = ((n+1 : ℕ) : ℝ)*ε := by
        calc
          _ = ((n+1 : ℕ) : ℝ)*(((1-ε)⁻¹-1)*(1-ε)) := by ring
          _ = _ := by rw [hid]
      rw [he] at hh
      nlinarith)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [Real.rpow_def_of_pos (inv_pos.mpr hd),Real.log_inv,← Real.exp_add]
  congr 1
  ring

lemma normSquareBand_measurable (n : ℕ) (ε : ℝ) : MeasurableSet (normSquareBand n ε) :=
  (measurableSet_le measurable_const (continuous_norm.pow 2).measurable).inter
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const)

lemma canonicalRadial_band_compl_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    canonicalRadialMass n 1 (normSquareBand n ε)ᶜ ≤
      ENNReal.ofReal (Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ)))+
      ENNReal.ofReal (Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ))) := by
  calc
    _ ≤ canonicalRadialMass n 1
        ({x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2} ∪ {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)}) :=
      measure_mono (by
        intro x hx
        change ¬ (_ ∧ _) at hx
        rcases not_and_or.mp hx with h | h
        · exact Or.inr (le_of_not_ge h)
        · exact Or.inl (le_of_not_ge h))
    _ ≤ _ := (measure_union_le _ _).trans
      (add_le_add (canonicalRadial_upper_tail n hε) (canonicalRadial_lower_tail n hε hε1))

lemma exp_neg_mul_nat_succ_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

lemma canonicalRadial_band_eventually_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε) := by
  have hu : 0 < (ε-Real.log (1+ε))/2 := by
    have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1+ε) (by linarith : 1+ε ≠ 1)
    linarith
  have hl : 0 < (-ε-Real.log (1-ε))/2 := by
    have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1-ε) (by linarith : 1-ε ≠ 1)
    linarith
  have ht := (exp_neg_mul_nat_succ_tendsto hu).add (exp_neg_mul_nat_succ_tendsto hl)
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ))+
      Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ)) < 1/2 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)+0 < 1/2))
  filter_upwards [hev] with n hn
  have h := canonicalRadial_band_compl_le n hε hε1
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le] at h
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at h'
  change (canonicalRadialMass n 1).real (normSquareBand n ε)ᶜ ≤ _ at h'
  rw [measureReal_compl (normSquareBand_measurable n ε), probReal_univ] at h'
  linarith

lemma canonicalRadialMass_real_apply {n : ℕ} {b : ℝ} (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) :
    (canonicalRadialMass n b).real A = ∫ x in A, canonicalRadialDensity n b x := by
  rw [Measure.real,canonicalRadialMass_apply hb hA,ENNReal.toReal_ofReal]
  exact integral_nonneg fun x => (canonicalRadialDensity_pos n b x).le

lemma canonicalRadialDensity_tilt (n : ℕ) (b : ℝ) (x : RadialSpace n) :
    canonicalRadialDensity n b x = Real.exp (((1-b)/2)*‖x‖^2)*canonicalRadialDensity n 1 x := by
  unfold canonicalRadialDensity
  rw [mul_left_comm (Real.exp _) (radialNormalizer n),← Real.exp_add]
  congr 2
  ring

lemma normSquareBand_tilt_bounds (n : ℕ) {ε b : ℝ} {x : RadialSpace n}
    (hx : x ∈ normSquareBand n ε) :
    ((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2) ≤ ((1-b)/2)*‖x‖^2 ∧
    ((1-b)/2)*‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2) := by
  have ha : |‖x‖^2-((n+1 : ℕ) : ℝ)| ≤ ((n+1 : ℕ) : ℝ)*ε := by
    rcases hx with ⟨hl,hu⟩
    apply abs_le.mpr
    constructor <;> nlinarith
  have hm := mul_le_mul_of_nonneg_left ha (abs_nonneg (1-b))
  rw [← abs_mul] at hm
  obtain ⟨hl,hu⟩ := abs_le.mp hm
  constructor <;> nlinarith

lemma canonicalRadial_band_mass_bounds (n : ℕ) {b ε : ℝ} (hb : 0 < b)
    (hhalf : (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε)) :
    Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 ≤
      (canonicalRadialMass n b).real (normSquareBand n ε) ∧
    (canonicalRadialMass n b).real (normSquareBand n ε) ≤
      Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2)) := by
  have hm := normSquareBand_measurable n ε
  have hlo : Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))*
      (canonicalRadialMass n 1).real (normSquareBand n ε) ≤
      (canonicalRadialMass n b).real (normSquareBand n ε) := by
    rw [canonicalRadialMass_real_apply hb hm,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) hm,
      ← integral_const_mul]
    apply setIntegral_mono_on
      ((canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1)).const_mul _).integrableOn
      (canonicalRadialDensity_integrable n hb).integrableOn hm
    intro x hx
    rw [canonicalRadialDensity_tilt n b x]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (normSquareBand_tilt_bounds n hx).1)
      (canonicalRadialDensity_pos n 1 x).le
  have hup : (canonicalRadialMass n b).real (normSquareBand n ε) ≤
      Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2))*
      (canonicalRadialMass n 1).real (normSquareBand n ε) := by
    rw [canonicalRadialMass_real_apply hb hm,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) hm,
      ← integral_const_mul]
    apply setIntegral_mono_on
      (canonicalRadialDensity_integrable n hb).integrableOn
      ((canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1)).const_mul _).integrableOn hm
    intro x hx
    rw [canonicalRadialDensity_tilt n b x]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (normSquareBand_tilt_bounds n hx).2)
      (canonicalRadialDensity_pos n 1 x).le
  constructor
  · have h := mul_le_mul_of_nonneg_left hhalf (Real.exp_pos (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))).le
    have h' : Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 ≤
        Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))*
        (canonicalRadialMass n 1).real (normSquareBand n ε) := by simpa only [mul_one_div] using h
    exact h'.trans hlo
  · apply hup.trans
    exact mul_le_of_le_one_right (Real.exp_pos _).le (measureReal_le_one)

lemma canonicalRadial_band_log_bounds (n : ℕ) {b ε : ℝ} (hb : 0 < b)
    (hhalf : (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε)) :
    (1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ) ≤
      Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ∧
    Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ≤
      (1-b)/2+|1-b| *ε/2 := by
  obtain ⟨hl,hu⟩ := canonicalRadial_band_mass_bounds n hb hhalf
  have hlpos : 0 < Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 := by positivity
  have hmpos := hlpos.trans_le hl
  have hl' := Real.log_le_log hlpos hl
  have hu' := Real.log_le_log hmpos hu
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2:ℝ) ≠ 0),Real.log_exp] at hl'
  rw [Real.log_exp] at hu'
  have hn : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  constructor
  · apply (le_div_iff₀ hn).mpr
    have he : ((1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ))*((n+1 : ℕ) : ℝ) =
        ((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2)-Real.log 2 := by field_simp
    rw [he]
    exact hl'
  · exact (div_le_iff₀ hn).mpr (by nlinarith)

lemma sphericalExp_mono (n : ℕ) (z : Spin (n+1)) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) : sphericalExp n z r ≤ sphericalExp n z s := by
  rw [sphericalExp_eq_cosh,sphericalExp_eq_cosh]
  apply integral_mono (unitSphere_continuous_integrable (by fun_prop))
    (unitSphere_continuous_integrable (by fun_prop))
  intro u
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg (hr.trans hrs)]
  exact mul_le_mul_of_nonneg_right hrs (abs_nonneg _)

section Polar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma polar_radial_lintegral (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g ‖x‖ ∂μ) = ∫⁻ r : Ioi (0:ℝ), g r ∂haarRadiusMeasure μ := by
  rw [polar_lintegral_normalized μ (fun x => g ‖x‖) (hg.comp measurable_norm)]
  apply lintegral_congr
  intro r
  have hnorm (u : Metric.sphere (0:E) 1) : ‖(r:ℝ) • (u:E)‖ = (r:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property]
    simp
  simp only [hnorm,lintegral_const,normalizedAngular,Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (angular_total_ne_zero μ) (measure_ne_top _ _),mul_one]

lemma polar_weighted_bounds (f : E → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) {L U : ℝ≥0∞}
    (hL : ∀ r : Ioi (0:ℝ), g r ≠ 0 →
      L ≤ ∫⁻ u : Metric.sphere (0:E) 1, f ((r:ℝ) • (u:E)) ∂normalizedAngular μ)
    (hU : ∀ r : Ioi (0:ℝ), g r ≠ 0 →
      (∫⁻ u : Metric.sphere (0:E) 1, f ((r:ℝ) • (u:E)) ∂normalizedAngular μ) ≤ U) :
    L * (∫⁻ x, g ‖x‖ ∂μ) ≤ (∫⁻ x, g ‖x‖ * f x ∂μ) ∧
      (∫⁻ x, g ‖x‖ * f x ∂μ) ≤ U * (∫⁻ x, g ‖x‖ ∂μ) := by
  rw [polar_radial_lintegral μ g hg,polar_weighted_lintegral μ f hf g hg]
  constructor
  · rw [← lintegral_const_mul (f := fun r : Ioi (0:ℝ) => g r) _ (hg.comp measurable_subtype_coe)]
    apply lintegral_mono
    intro r
    by_cases hr : g r = 0
    · simp [hr]
    · simpa only [mul_comm L] using mul_le_mul le_rfl (hL r hr) (by positivity) (by positivity)
  · rw [← lintegral_const_mul (f := fun r : Ioi (0:ℝ) => g r) _ (hg.comp measurable_subtype_coe)]
    apply lintegral_mono
    intro r
    by_cases hr : g r = 0
    · simp [hr]
    · simpa only [mul_comm U] using mul_le_mul le_rfl (hU r hr) (by positivity) (by positivity)

end Polar

lemma canonicalBandRadiusWeight_measurable (n : ℕ) (b ε : ℝ) :
    Measurable (canonicalBandRadiusWeight n b ε) := by
  apply Measurable.indicator (by fun_prop)
  exact (measurableSet_le measurable_const (continuous_id.pow 2).measurable).inter
    (measurableSet_le (continuous_id.pow 2).measurable measurable_const)

lemma canonicalBandRadiusWeight_integral (n : ℕ) (b ε : ℝ)
    (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, canonicalBandRadiusWeight n b ε ‖x‖ * F x) =
      ∫⁻ x in normSquareBand n ε, F x ∂canonicalRadialMass n b := by
  rw [canonicalRadialMass,setLIntegral_withDensity_eq_setLIntegral_mul _
    (canonicalRadialDensity_continuous n b).measurable.ennreal_ofReal hF
    (normSquareBand_measurable n ε),← lintegral_indicator (normSquareBand_measurable n ε) _]
  apply lintegral_congr
  intro x
  by_cases hx : ((n+1:ℕ):ℝ)*(1-ε) ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1+ε)
  all_goals simp only [canonicalBandRadiusWeight,normSquareBand,Set.indicator_apply,Set.mem_ofPred_eq,hx,and_self,ite_true,ite_false,zero_mul,Pi.mul_apply,canonicalRadialDensity]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma sphericalExp_gaussian_average (n : ℕ) (R σ : ℝ) (x : Spin (n+1)) :
    (∫ y, sphericalExp n (x+σ • y) R ∂stdGaussian (Spin (n+1)))=
      Real.exp (R^2*σ^2/2)*sphericalExp n x R := by
  let μ := stdGaussian (Spin (n+1))
  let ν := unitSphereLaw (n+1)
  have hI : Integrable (fun p : Spin (n+1)×Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))) (μ.prod ν) := by
    apply (((gaussian_integrable_exp_norm μ (|R| *|σ|)).const_mul (Real.exp (|R| *‖x‖))).comp_fst ν).mono' (by fun_prop)
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hu : ‖(p.2:Spin (n+1))‖=1 := by simp
      have hh := abs_real_inner_le_norm (x+σ • p.1) (p.2:Spin (n+1))
      rw [hu,mul_one] at hh
      have ht := norm_add_le x (σ • p.1)
      rw [norm_smul,Real.norm_eq_abs] at ht
      have hb := mul_le_mul_of_nonneg_left (hh.trans ht) (abs_nonneg R)
      rw [← abs_mul] at hb
      have hl := (le_abs_self (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))).trans hb
      nlinarith
  have H := integral_integral_swap (f := fun (y : Spin (n+1)) (u : Metric.sphere (0:Spin (n+1)) 1) =>
    Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1)))) hI
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_ at H
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_
  rw [H]
  have he (u : Metric.sphere (0:Spin (n+1)) 1) :
      (∫ y : Spin (n+1), Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂μ)=
        Real.exp (R^2*σ^2/2)*Real.exp (R*inner ℝ x (u:Spin (n+1))) := by
    simp only [inner_add_left,real_inner_smul_left,mul_add,Real.exp_add]
    rw [integral_const_mul]
    have hh := integral_exp_inner_stdGaussian (u:Spin (n+1)) (R*σ)
    have hu : ‖(u:Spin (n+1))‖=1 := by simp
    rw [hu] at hh
    simp only [one_pow,mul_one] at hh
    have hinner : (fun y : Spin (n+1) => Real.exp (R*(σ*inner ℝ y (u:Spin (n+1)))))=
        (fun y => Real.exp ((R*σ)*inner ℝ (u:Spin (n+1)) y)) := by
      funext y
      rw [real_inner_comm y (u:Spin (n+1))]
      congr 1
      ring
    rw [hinner,hh,mul_pow]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  rfl

lemma gaussianEntropic_logSphericalExp_one (n : ℕ) (R σ : ℝ) (x : Spin (n+1)) :
    gaussianEntropic (stdGaussian (Spin (n+1))) 1 σ (logSphericalExp n R) x=
      logSphericalExp n R x+R^2*σ^2/2 := by
  rw [gaussianEntropic_pos _ (logSphericalExp_lipschitz n R) (by norm_num)]
  simp only [one_mul,div_one,logSphericalExp]
  simp_rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n _ R))]
  rw [sphericalExp_gaussian_average,Real.log_mul (Real.exp_pos _).ne'
    (lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n x R)).ne',Real.log_exp]
  ring

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatTilt
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

lemma canonicalBandRadiusWeight_mass (n : ℕ) (b ε : ℝ) :
    (∫⁻ x : RadialSpace n, canonicalBandRadiusWeight n b ε ‖x‖) =
      canonicalRadialMass n b (normSquareBand n ε) := by
  simpa using canonicalBandRadiusWeight_integral n b ε (fun _ => 1) measurable_const

lemma canonicalWeighted_mass_le (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) {a b c : ℝ}
    (hc : ∀ x ∈ A, -(a/2)*‖x‖^2 ≤ c-(b/2)*‖x‖^2) :
    (∫⁻ x in A, F x ∂canonicalRadialMass n a) ≤
      ENNReal.ofReal (Real.exp c) * (∫⁻ x, F x ∂canonicalRadialMass n b) := by
  have hd (d : ℝ) : Measurable (fun x : RadialSpace n => ENNReal.ofReal (canonicalRadialDensity n d x)) :=
    (canonicalRadialDensity_continuous n d).measurable.ennreal_ofReal
  rw [canonicalRadialMass,setLIntegral_withDensity_eq_setLIntegral_mul _ (hd a) hF hA,
    canonicalRadialMass,lintegral_withDensity_eq_lintegral_mul _ (hd b) hF,
    ← lintegral_const_mul _ ((hd b).mul hF)]
  calc
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp c) *
        (ENNReal.ofReal (canonicalRadialDensity n b x) * F x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      change ENNReal.ofReal (canonicalRadialDensity n a x) * F x ≤ _
      rw [← mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos c).le]
      apply mul_le_mul (ENNReal.ofReal_le_ofReal ?_) le_rfl (by positivity) (by positivity)
      unfold canonicalRadialDensity
      calc
        _ ≤ radialNormalizer n * Real.exp (c-(b/2)*‖x‖^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hc x hx)) (radialNormalizer_pos n).le
        _ = _ := by rw [Real.exp_sub,neg_mul,Real.exp_neg]; ring
    _ ≤ _ := setLIntegral_le_lintegral _ _

lemma canonicalWeighted_upper_tail (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in {x : RadialSpace n | ((n+1:ℕ):ℝ)*(1+ε) ≤ ‖x‖^2}, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b-δ)) := by
  apply canonicalWeighted_mass_le n F hF
    (measurableSet_le measurable_const (continuous_norm.pow 2).measurable)
  intro x hx
  dsimp only [Set.mem_ofPred_eq,Pi.pow_apply] at hx
  have := mul_le_mul_of_nonneg_left hx hδ
  nlinarith

lemma canonicalWeighted_lower_tail (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in {x : RadialSpace n | ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1-ε)}, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b+δ)) := by
  apply canonicalWeighted_mass_le n F hF
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const)
  intro x hx
  dsimp only [Set.mem_ofPred_eq,Pi.pow_apply] at hx
  have := mul_le_mul_of_nonneg_left hx hδ
  nlinarith

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

lemma real_quadratic_complete_square {b : ℝ} (hb : b ≠ 0) (c d y : ℝ) :
    Real.exp (-b*y^2+c*y+d) =
      Real.exp (d+c^2/(4*b))*Real.exp (-b*(y-c/(2*b))^2) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

lemma real_quadratic_integrable {b : ℝ} (hb : 0 < b) (c d : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-b*y^2+c*y+d)) := by
  simp_rw [real_quadratic_complete_square hb.ne']
  exact ((integrable_exp_neg_mul_sq hb).comp_sub_right (c/(2*b))).const_mul _

lemma real_quadratic_integral {b : ℝ} (hb : 0 < b) (c d : ℝ) :
    (∫ y : ℝ, Real.exp (-b*y^2+c*y+d)) =
      Real.exp (d+c^2/(4*b))*Real.sqrt (Real.pi/b) := by
  simp_rw [real_quadratic_complete_square hb.ne']
  rw [integral_const_mul, integral_sub_right_eq_self (fun y : ℝ => Real.exp (-b*y^2)),integral_gaussian]

lemma standardGaussian_quadratic_density (a c d y : ℝ) :
    gaussianPDFReal 0 1 y * Real.exp (a*y^2+c*y+d) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-a)*y^2+c*y+d) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma standardGaussian_quadratic_integrable {a : ℝ} (ha : a < 1/2) (c d : ℝ) :
    Integrable (fun y : ℝ => Real.exp (a*y^2+c*y+d)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [smul_eq_mul]
  have he : (fun y : ℝ => (gaussianPDF 0 1 y).toReal * Real.exp (a*y^2+c*y+d)) =
      (fun y : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-a)*y^2+c*y+d)) := by
    funext y
    rw [toReal_gaussianPDF]
    exact standardGaussian_quadratic_density a c d y
  rw [he]
  exact (real_quadratic_integrable (by linarith : 0 < 1/2-a) c d).const_mul _

lemma standardGaussian_quadratic_integral {a : ℝ} (ha : a < 1/2) (c d : ℝ) :
    (∫ y, Real.exp (a*y^2+c*y+d) ∂gaussianReal 0 1) =
      Real.exp (d+c^2/(4*(1/2-a))) / Real.sqrt (1-2*a) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul,standardGaussian_quadratic_density]
  rw [integral_const_mul,real_quadratic_integral (by linarith : 0 < 1/2-a)]
  have hratio : Real.sqrt (Real.pi/(1/2-a)) = Real.sqrt (2*Real.pi)/Real.sqrt (1-2*a) := by
    rw [←Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  rw [hratio]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2*Real.pi))]

lemma gaussian_quadratic_fractional_integrable {b z σ : ℝ} (hb : 0 < b)
    (ha : 0 < b-z*σ^2) (c x : ℝ) :
    Integrable (fun y : ℝ => Real.exp (z*(c+(x+σ*y)^2/(2*b)))) (gaussianReal 0 1) := by
  have hhalf : z*σ^2/(2*b) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
    linarith
  convert standardGaussian_quadratic_integrable hhalf (z*x*σ/b) (z*c+z*x^2/(2*b)) using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  congr 1
  field_simp
  ring

lemma gaussian_quadratic_fractional_log {b z σ : ℝ} (hb : 0 < b) (hz : z ≠ 0)
    (ha : 0 < b-z*σ^2) (c x : ℝ) :
    Real.log (∫ y, Real.exp (z*(c+(x+σ*y)^2/(2*b))) ∂gaussianReal 0 1)/z =
      c+(Real.log b-Real.log (b-z*σ^2))/(2*z)+x^2/(2*(b-z*σ^2)) := by
  have hhalf : z*σ^2/(2*b) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
    linarith
  have hfun : (fun y : ℝ => Real.exp (z*(c+(x+σ*y)^2/(2*b)))) =
      (fun y : ℝ => Real.exp ((z*σ^2/(2*b))*y^2+(z*x*σ/b)*y+(z*c+z*x^2/(2*b)))) := by
    funext y
    congr 1
    field_simp
    ring
  have hprec : 1-2*(z*σ^2/(2*b)) = (b-z*σ^2)/b := by field_simp
  have hprec' : 1/2-z*σ^2/(2*b) = (b-z*σ^2)/(2*b) := by field_simp
  rw [hfun,standardGaussian_quadratic_integral hhalf,hprec,
    Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr (div_pos ha hb)).ne',
    Real.log_exp, Real.log_sqrt (div_pos ha hb).le,Real.log_div ha.ne' hb.ne',hprec']
  field_simp [hb.ne',hz,ha.ne']
  ring

lemma gaussianShiftStep_measurable (σ : ℕ → ℝ) : Measurable (gaussianShiftStep σ) := by
  unfold gaussianShiftStep
  fun_prop

lemma quadraticCascadePrecision_tail_pos (σ : ℕ → ℝ) (b : ℝ) (n : ℕ) (z : Fin (n+1) → ℝ)
    (hz : 0 ≤ z 0) (hp : 0 < quadraticCascadePrecision σ b (n+1) z) :
    0 < quadraticCascadePrecision σ b n (fun i => z i.succ) := by
  have hsq := mul_nonneg hz (sq_nonneg (σ n))
  dsimp [quadraticCascadePrecision] at hp
  linarith

theorem finiteCascade_quadratic_recursion (σ : ℕ → ℝ) (b c : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x : ℕ → ℝ, finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep σ) n z
      (fun x => c+(x 0)^2/(2*b)) x =
      c+quadraticCascadeOffset σ b n z+(x n)^2/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable standardGaussianMark (gaussianShiftStep σ)
      (fun x => c+(x 0)^2/(2*b)) n z := by
  induction n with
  | zero => exact ⟨fun _ => by simp [finiteCascadeLogRecursion,quadraticCascadeOffset,quadraticCascadePrecision],trivial⟩
  | succ n ih =>
    have hpt := quadraticCascadePrecision_tail_pos σ b n z (hz 0).le hp
    obtain ⟨heq,hint⟩ := ih (fun i => z i.succ) (fun i => hz i.succ) hpt
    constructor
    · intro x
      conv_lhs => rw [finiteCascadeLogRecursion]
      unfold fractionalLogMoment
      simp_rw [heq]
      change Real.log (∫ y, Real.exp (z 0 *
        (c+quadraticCascadeOffset σ b n (fun i => z i.succ)+
          (x (n+1)+σ n*y)^2/(2*quadraticCascadePrecision σ b n (fun i => z i.succ))))
          ∂gaussianReal 0 1)/(z 0) = _
      rw [gaussian_quadratic_fractional_log hpt (hz 0).ne' hp]
      dsimp [quadraticCascadeOffset,quadraticCascadePrecision]
      ring
    · refine ⟨?_,hint⟩
      intro x
      simp_rw [heq]
      exact gaussian_quadratic_fractional_integrable hpt hp
        (c+quadraticCascadeOffset σ b n (fun i => z i.succ)) (x (n+1))

lemma quadraticCascadePrecision_le (σ : ℕ → ℝ) (b : ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) : quadraticCascadePrecision σ b n z ≤ b := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have ht := ih (fun i => z i.succ) (fun i => hz i.succ)
    have hq := mul_nonneg (hz 0) (sq_nonneg (σ n))
    dsimp [quadraticCascadePrecision]
    linarith

lemma quadraticCascadePrecision_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ) (b : ℝ) :
    HasDerivAt (fun b => quadraticCascadePrecision σ b n z) 1 b := by
  induction n with
  | zero => exact hasDerivAt_id b
  | succ n ih => exact (ih (fun i => z i.succ)).sub_const _

lemma quadraticCascadeOffset_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) {b : ℝ} (hp : 0 < quadraticCascadePrecision σ b n z) :
    HasDerivAt (fun b => quadraticCascadeOffset σ b n z)
      (quadraticCascadeReciprocalSlope σ b n z) b := by
  induction n with
  | zero => exact hasDerivAt_const b 0
  | succ n ih =>
    have hpt := quadraticCascadePrecision_tail_pos σ b n z (hz 0) hp
    exact (ih (fun i => z i.succ) (fun i => hz i.succ) hpt).add
      ((((quadraticCascadePrecision_hasDerivAt σ n (fun i => z i.succ) b).log hpt.ne').sub
        ((quadraticCascadePrecision_hasDerivAt σ (n+1) z b).log hp.ne')).div_const (2*z 0))

lemma canonicalGaussianFreeValue_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (r : ℝ) {b : ℝ} (hp : 0 < quadraticCascadePrecision σ b n z) :
    HasDerivAt (canonicalGaussianFreeValue σ n z r)
      (-1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-r/(2*(quadraticCascadePrecision σ b n z)^2)) b := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b n z hz)
  have hq := quadraticCascadePrecision_hasDerivAt σ n z b
  have ht := (((Real.hasDerivAt_log hb.ne').neg.div_const 2).add
    (quadraticCascadeOffset_hasDerivAt σ n z hz hp)).add
      ((hasDerivAt_const b r).div (hq.const_mul 2) (by positivity))
  have hd : -b⁻¹/2+quadraticCascadeReciprocalSlope σ b n z+
      (0*(2*quadraticCascadePrecision σ b n z)-r*(2*1))/(2*quadraticCascadePrecision σ b n z)^2 =
      -1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-r/(2*(quadraticCascadePrecision σ b n z)^2) := by
    field_simp [hb.ne',hp.ne']
    ring
  exact ht.congr_deriv hd

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

lemma decoratedCascade_log_deviation_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))
      {η | ε ≤ |Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
        decoratedWeightedTotal step n (fun _ _ => 0) (x,η))-c|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  obtain ⟨hm,hbound⟩ := decoratedCascade_log_second_moment_bound ν step hstep n z hz hz0 hz1 F hF hI hM x c
  have he := decoratedCascade_log_identity ν step hstep n z hz hz0 hz1 F hF hI hM x c
  have hvar : variance (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ≤ cascadeLogFluctuationConstant n z := by
    rw [variance_eq_integral hm.aemeasurable,he]
    exact hbound
  have hc := meas_ge_le_variance_div_sq hm hε
  rw [he] at hc
  exact hc.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg ε)))

lemma finiteCascade_terminal_log_deviation_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X)
    {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))
      {η | ε ≤ |Real.log (decoratedTerminalTotal step H n (x,η) /
        decoratedTerminalTotal step (fun _ => 0) n (x,η))-finiteCascadeLogRecursion ν step n z H x|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_deviation_le ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x) hε

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

lemma fractional_log_moment_sum_pi {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) (b : ℝ) (f : ι → S → ℝ)
    (hI : ∀ i, Integrable (fun s => Real.exp (b*f i s)) (ν i)) :
    (Integrable (fun s : ι → S => Real.exp (b*∑ i, f i (s i))) (piMarkLaw ν)) ∧
    Real.log (∫ s, Real.exp (b*∑ i, f i (s i)) ∂(piMarkLaw ν : Measure (ι → S)))/b =
      ∑ i, Real.log (∫ s, Real.exp (b*f i s) ∂(ν i : Measure S))/b := by
  simp_rw [Finset.mul_sum,Real.exp_sum]
  constructor
  · exact Integrable.fintype_prod hI
  · change Real.log (∫ s, ∏ i, Real.exp (b*f i (s i)) ∂Measure.pi (fun i => (ν i : Measure S)))/b = _
    rw [integral_fintype_prod_eq_prod (fun i s => Real.exp (b*f i s)),Real.log_prod (fun i _ => (integral_exp_pos (hI i)).ne'),Finset.sum_div]

theorem finiteCascade_sum_pi {ι X S : Type} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) (step : ι → X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (H : ι → X → ℝ)
    (hI : ∀ i, finiteCascadeFractionalIntegrable (ν i) (step i) (H i) n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw ν)
      (fun p : (ι → X)×(ι → S) => fun i => step i (p.1 i,p.2 i)) n z
        (fun x => ∑ i, H i (x i)) x =
      ∑ i, finiteCascadeLogRecursion (ν i) (step i) n z (H i) (x i)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw ν)
      (fun p : (ι → X)×(ι → S) => fun i => step i (p.1 i,p.2 i))
        (fun x => ∑ i, H i (x i)) n z := by
  induction n with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ n ih =>
    obtain ⟨heq,htail⟩ := ih (fun j => z j.succ) (fun i => (hI i).2)
    constructor
    · intro x
      conv_lhs => rw [finiteCascadeLogRecursion]
      unfold fractionalLogMoment
      simp_rw [heq]
      exact (fractional_log_moment_sum_pi ν (z 0)
        (fun i s => finiteCascadeLogRecursion (ν i) (step i) n (fun j => z j.succ) (H i) (step i (x i,s)))
        (fun i => (hI i).1 (x i))).2
    · refine ⟨?_,htail⟩
      intro x
      simp_rw [heq]
      exact (fractional_log_moment_sum_pi ν (z 0)
        (fun i s => finiteCascadeLogRecursion (ν i) (step i) n (fun j => z j.succ) (H i) (step i (x i,s)))
        (fun i => (hI i).1 (x i))).1

theorem finiteCascade_quadratic_coordinates (d : ℕ) (σ : ℕ → ℝ) (b : ℝ) (c : Fin d → ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (fun p : (Fin d → ℕ → ℝ)×(Fin d → ℝ) => fun i => gaussianShiftStep σ (p.1 i,p.2 i)) n z
        (fun x => ∑ i, (c i+(x i 0)^2/(2*b))) x =
      (∑ i, c i) + d*quadraticCascadeOffset σ b n z+
        (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (fun p : (Fin d → ℕ → ℝ)×(Fin d → ℝ) => fun i => gaussianShiftStep σ (p.1 i,p.2 i))
        (fun x => ∑ i, (c i+(x i 0)^2/(2*b))) n z := by
  have hq := finiteCascade_sum_pi (fun _ : Fin d => standardGaussianMark)
    (fun _ => gaussianShiftStep σ) n z (fun i x => c i+(x 0)^2/(2*b))
    (fun i => (finiteCascade_quadratic_recursion σ b (c i) n z hz hp).2)
  refine ⟨?_,hq.2⟩
  intro x
  rw [hq.1]
  simp_rw [(finiteCascade_quadratic_recursion σ b _ n z hz hp).1]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_div]

lemma canonicalCoordinateStep_measurable (d : ℕ) (σ : ℕ → ℝ) :
    Measurable (canonicalCoordinateStep d σ) := by
  apply Measurable.of_eval
  intro i
  exact (gaussianShiftStep_measurable σ).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma canonicalCoordinatePotential_measurable (d : ℕ) (b : ℝ) :
    Measurable (canonicalCoordinatePotential d b) := by unfold canonicalCoordinatePotential; fun_prop

lemma canonical_coordinate_recursion (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) n z (canonicalCoordinatePotential d b) x =
      d*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
        (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) (canonicalCoordinatePotential d b) n z := by
  have he := finiteCascade_quadratic_coordinates d σ b (fun _ => -Real.log b/2) n z hz hp
  refine ⟨?_,he.2⟩
  intro x
  unfold canonicalCoordinateStep canonicalCoordinatePotential
  rw [he.1]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_add]

theorem canonical_coordinate_log_mean (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (x : Fin d → ℕ → ℝ) :
    (∫ η, canonicalCoordinateLog d n σ b (x,η)
      ∂decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z) =
      d*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
        (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z) := by
  unfold canonicalCoordinateLog
  rw [finiteCascade_terminal_log_recursion_of_fractional _ _ (canonicalCoordinateStep_measurable d σ)
    n z hz hz0 hz1 (canonicalCoordinatePotential_measurable d b)
    (canonical_coordinate_recursion d σ b n z hz0 hp).2]
  exact (canonical_coordinate_recursion d σ b n z hz0 hp).1 x

lemma canonical_coordinate_log_deviation_le (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (x : Fin d → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
      Measure (DecoratedCascade (Fin d → ℝ) n))
      {η | ε ≤ |canonicalCoordinateLog d n σ b (x,η)-
        (d*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
          (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z))|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  have he := finiteCascade_terminal_log_deviation_le _ _ (canonicalCoordinateStep_measurable d σ)
    n z hz hz0 hz1 (canonicalCoordinatePotential_measurable d b)
    (canonical_coordinate_recursion d σ b n z hz0 hp).2 x hε
  rw [(canonical_coordinate_recursion d σ b n z hz0 hp).1 x] at he
  exact he

lemma gaussian_square_memLp_two (r : ℝ≥0) : MemLp (fun y : ℝ => y^2) 2 (gaussianReal 0 r) := by
  have : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
    apply (ENNReal.holderTriple_coe_iff (p := 4) (q := 4) (r := 2) (by norm_num)).mpr
    norm_num [NNReal.holderTriple_iff]
  have h4 : MemLp (fun y : ℝ => y) (4 : ℝ≥0∞) (gaussianReal 0 r) := memLp_id_gaussianReal 4
  have hm : MemLp (fun y : ℝ => y*y) 2 (gaussianReal 0 r) :=
    h4.mul h4
  simpa [pow_two] using hm

lemma gaussian_square_mean (r : ℝ≥0) : (∫ y, y^2 ∂gaussianReal 0 r) = r := by
  have he := variance_fun_id_gaussianReal (μ := 0) (v := r)
  rw [variance_eq_integral (by fun_prop : AEMeasurable (fun x : ℝ => x) (gaussianReal 0 r))] at he
  simpa only [integral_id_gaussianReal,sub_zero] using he

lemma gaussian_square_sum_memLp_two (d : ℕ) (r : ℝ≥0) :
    MemLp (fun y : Fin d → ℝ => ∑ i, (y i)^2) 2 (Measure.pi (fun _ => gaussianReal 0 r)) := by
  exact memLp_finsetSum _ (fun i _ => (gaussian_square_memLp_two r).comp_measurePreserving (measurePreserving_eval _ i))

lemma gaussian_square_sum_mean (d : ℕ) (r : ℝ≥0) :
    (∫ y : Fin d → ℝ, ∑ i, (y i)^2 ∂Measure.pi (fun _ => gaussianReal 0 r)) = d*r := by
  have hi : ∀ i : Fin d, Integrable (fun y : Fin d → ℝ => (y i)^2) (Measure.pi (fun _ => gaussianReal 0 r)) :=
    fun i => ((gaussian_square_memLp_two r).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 r) i)).integrable (by norm_num)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  have hj : ∀ i : Fin d, (∫ y : Fin d → ℝ, (y i)^2 ∂Measure.pi (fun _ => gaussianReal 0 r)) = r := by
    intro i
    rw [integral_comp_eval (μ := fun _ : Fin d => gaussianReal 0 r) (i := i) (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y^2) (gaussianReal 0 r))]
    exact gaussian_square_mean r
  simp_rw [hj]
  simp

lemma gaussian_square_sum_variance (d : ℕ) (r : ℝ≥0) :
    variance (fun y : Fin d → ℝ => ∑ i, (y i)^2) (Measure.pi (fun _ => gaussianReal 0 r)) =
      d*variance (fun y : ℝ => y^2) (gaussianReal 0 r) := by
  have he := variance_sum_pi (μ := fun _ : Fin d => gaussianReal 0 r) (fun _ => gaussian_square_memLp_two r)
  have hs : (∑ i : Fin d, fun ω : Fin d → ℝ => (ω i)^2) = (fun ω => ∑ i, (ω i)^2) := by ext ω; simp
  rw [hs] at he
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using he

lemma gaussian_square_average_deviation_le (d : ℕ) (hd : 0 < d) (r : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 r))
      {y | ε ≤ |(∑ i, (y i)^2)/(d : ℝ)-r|} ≤
      ENNReal.ofReal (variance (fun y : ℝ => y^2) (gaussianReal 0 r)/(d*ε^2)) := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hc := meas_ge_le_variance_div_sq (gaussian_square_sum_memLp_two d r) (mul_pos hε hd')
  rw [gaussian_square_sum_mean,gaussian_square_sum_variance] at hc
  have hset : {y : Fin d → ℝ | ε ≤ |(∑ i, (y i)^2)/(d : ℝ)-r|} =
      {y | ε*(d : ℝ) ≤ |(∑ i, (y i)^2)-(d : ℝ)*r|} := by
    ext y
    have he : (∑ i, (y i)^2)/(d : ℝ)-r = ((∑ i, (y i)^2)-(d : ℝ)*r)/(d : ℝ) := by field_simp
    simp only [Set.mem_ofPred_eq,he,abs_div,abs_of_pos hd']
    exact le_div_iff₀ hd'
  rw [hset]
  convert hc using 2
  all_goals try with_reducible_and_instances rfl
  field_simp [hd'.ne',hε.ne']

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

lemma canonicalCoordinateLog_measurable (d n : ℕ) (σ : ℕ → ℝ) (b : ℝ) (z : Fin n → ℝ) :
    Measurable (canonicalCoordinateLog d n σ b) := by
  exact ((decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _
    (canonicalCoordinateStep_measurable d σ) (canonicalCoordinatePotential_measurable d b) n z).div
    (decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _
      (canonicalCoordinateStep_measurable d σ) measurable_const n z)).log

lemma product_deviation_le {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G : X → ℝ} (hF : Measurable F) (hG : Measurable G)
    (c ε : ℝ) (A : ℝ≥0∞)
    (hbound : ∀ x, ν {y | ε/2 ≤ |F (x,y)-G x|} ≤ A) :
    μ.prod ν {p | ε ≤ |F p-c|} ≤ A+μ {x | ε/2 ≤ |G x-c|} := by
  have hsub : {p : X×Y | ε ≤ |F p-c|} ⊆
      {p | ε/2 ≤ |F p-G p.1|} ∪ {p | ε/2 ≤ |G p.1-c|} := by
    intro p hp
    by_contra hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hh
    have ht := abs_sub_le (F p) (G p.1) c
    dsimp only [Set.mem_ofPred_eq] at hp
    linarith
  have hA : μ.prod ν {p : X×Y | ε/2 ≤ |F p-G p.1|} ≤ A := by
    rw [Measure.prod_apply (by measurability)]
    calc
      _ ≤ ∫⁻ _ : X, A ∂μ := lintegral_mono hbound
      _ = A := by simp
  have hB : μ.prod ν {p : X×Y | ε/2 ≤ |G p.1-c|} = μ {x | ε/2 ≤ |G x-c|} := by
    have hs : {p : X×Y | ε/2 ≤ |G p.1-c|} = {x | ε/2 ≤ |G x-c|} ×ˢ Set.univ := by ext p; simp
    rw [hs,Measure.prod_prod]
    simp
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [hB]; exact add_le_add hA le_rfl))

theorem canonical_coordinate_joint_deviation_le (d : ℕ) (hd : 0 < d) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (r : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
      (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
        Measure (DecoratedCascade (Fin d → ℝ) n)))
      {p | ε*(d : ℝ) ≤ |canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-
        d*canonicalGaussianFreeValue σ n z r b|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/(ε*d/2)^2)+
        ENNReal.ofReal (variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
          (d*(ε*quadraticCascadePrecision σ b n z)^2)) := by
  let P := quadraticCascadePrecision σ b n z
  let a := -Real.log b/2+quadraticCascadeOffset σ b n z
  let G := fun y : Fin d → ℝ => (d : ℝ)*a+(∑ i, (y i)^2)/(2*P)
  let F := fun p : (Fin d → ℝ)×DecoratedCascade (Fin d → ℝ) n =>
    canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)
  have hP : 0 < P := hp
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hF : Measurable F := (canonicalCoordinateLog_measurable d n σ b z).comp (by fun_prop)
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hc := product_deviation_le (Measure.pi (fun _ : Fin d => gaussianReal 0 r))
    (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
        Measure (DecoratedCascade (Fin d → ℝ) n)) hF hG
    (d*canonicalGaussianFreeValue σ n z r b) (ε*d)
    (ENNReal.ofReal (cascadeLogFluctuationConstant n z/(ε*d/2)^2))
    (fun y => canonical_coordinate_log_deviation_le d σ b n z hz hz0 hz1 hp
      (fun i _ => y i) (half_pos (mul_pos hε hd')))
  apply hc.trans
  apply add_le_add le_rfl
  have hset : {y : Fin d → ℝ | ε*(d : ℝ)/2 ≤ |G y-d*canonicalGaussianFreeValue σ n z r b|} =
      {y | ε*P ≤ |(∑ i, (y i)^2)/(d : ℝ)-r|} := by
    ext y
    have he : G y-d*canonicalGaussianFreeValue σ n z r b =
        ((d : ℝ)/(2*P))*((∑ i, (y i)^2)/(d : ℝ)-r) := by
      dsimp [G,a,canonicalGaussianFreeValue]
      change (d : ℝ)*(-Real.log b/2+quadraticCascadeOffset σ b n z)+
        (∑ i, (y i)^2)/(2*P)-d*(-Real.log b/2+quadraticCascadeOffset σ b n z+r/(2*P)) = _
      field_simp [hd'.ne',hP.ne']
      ring
    have hf : 0 < (d : ℝ)/(2*P) := by positivity
    simp only [Set.mem_ofPred_eq,he,abs_mul,abs_of_pos hf]
    rw [mul_comm ((d : ℝ)/(2*P)),←div_le_iff₀ hf]
    field_simp [hd'.ne',hP.ne']
  rw [hset]
  exact gaussian_square_average_deviation_le d hd r (mul_pos hε hP)

theorem canonical_coordinate_converges (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (r : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℕ =>
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n)))
        {p | ε*(d : ℝ) ≤ |canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-
          d*canonicalGaussianFreeValue σ n z r b|}) atTop (𝓝 0) := by
  have hd : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun d : ℕ => (ε*(d : ℝ)/2)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      ((hd.const_mul_atTop hε).atTop_div_const (by norm_num))
  have hu : Tendsto (fun d : ℕ => (d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2) atTop atTop :=
    hd.atTop_mul_const (sq_pos_of_pos (mul_pos hε hp))
  have ht0 : Tendsto (fun d : ℕ => cascadeLogFluctuationConstant n z/(ε*(d : ℝ)/2)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hu0 : Tendsto (fun d : ℕ => variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
      ((d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hu
  have hsum : Tendsto (fun d : ℕ => ENNReal.ofReal (cascadeLogFluctuationConstant n z/(ε*(d : ℝ)/2)^2)+
      ENNReal.ofReal (variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
        ((d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2))) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal ht0).add (ENNReal.tendsto_ofReal hu0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [eventually_gt_atTop 0] with d hdpos
    exact canonical_coordinate_joint_deviation_le d hdpos σ b n z hz hz0 hz1 hp r hε

lemma exponential_ratio_converges {Ω : ℕ → Type} [∀ d, MeasurableSpace (Ω d)] (μ : ∀ d, Measure (Ω d))
    (X Y : ∀ d, Ω d → ℝ) (x y a : ℝ) (hrate : y-x < a)
    (hX : ∀ ε > 0, Tendsto (fun d => μ d {p | ε*(d : ℝ) ≤ |X d p-d*x|}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun d => μ d {p | ε*(d : ℝ) ≤ |Y d p-d*y|}) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun d => μ d {p | ρ ≤ Real.exp (Y d p-X d p-(d : ℝ)*a)}) atTop (𝓝 0) := by
  let ε := (a-(y-x))/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ht : Tendsto (fun d : ℕ => ε*(d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hε
  have he : ∀ᶠ d : ℕ in atTop, -Real.log ρ < ε*(d : ℝ) := ht.eventually (eventually_gt_atTop _)
  have hb : ∀ᶠ d : ℕ in atTop,
      μ d {p | ρ ≤ Real.exp (Y d p-X d p-(d : ℝ)*a)} ≤
        μ d {p | ε*(d : ℝ) ≤ |X d p-d*x|}+μ d {p | ε*(d : ℝ) ≤ |Y d p-d*y|} := by
    filter_upwards [he,eventually_gt_atTop 0] with d hd hdpos
    apply le_trans (measure_mono (t :=
      {p | ε*(d : ℝ) ≤ |X d p-d*x|} ∪ {p | ε*(d : ℝ) ≤ |Y d p-d*y|}) ?_) (measure_union_le _ _)
    intro p hp
    by_contra hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hh
    have hx := (abs_lt.mp hh.1).1
    have hy := (abs_lt.mp hh.2).2
    have hp' : Real.log ρ ≤ Y d p-X d p-(d : ℝ)*a := by
      simpa only [Real.log_exp] using Real.log_le_log hρ hp
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
    have ha : a = y-x+4*ε := by dsimp [ε]; ring
    rw [ha] at hp'
    nlinarith
  have hs := (hX ε hε).add (hY ε hε)
  simp only [add_zero] at hs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Eventually.of_forall (fun _ => bot_le)) hb

theorem canonical_ratio_converges (σ : ℕ → ℝ) (b b' a : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z)
    (hp' : 0 < quadraticCascadePrecision σ b' n z) (r : ℝ≥0)
    (hrate : canonicalGaussianFreeValue σ n z r b'-canonicalGaussianFreeValue σ n z r b < a)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun d : ℕ =>
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n)))
        {p | ρ ≤ Real.exp
          (canonicalCoordinateLog d n σ b' ((fun i _ => p.1 i),p.2)-
            canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-(d : ℝ)*a)}) atTop (𝓝 0) := by
  apply exponential_ratio_converges _ _ _ _ _ _ hrate
  · exact fun ε hε => canonical_coordinate_converges σ b n z hz hz0 hz1 hp r hε
  · exact fun ε hε => canonical_coordinate_converges σ b' n z hz hz0 hz1 hp' r hε
  · exact hρ

lemma canonical_stationary_tail_rates (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (r b : ℝ) (hp : 0 < quadraticCascadePrecision σ b n z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-
      r/(2*(quadraticCascadePrecision σ b n z)^2) = -1/2)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      0 < quadraticCascadePrecision σ (b-δ) n z ∧
      0 < quadraticCascadePrecision σ (b+δ) n z ∧
      canonicalGaussianFreeValue σ n z r (b-δ)-canonicalGaussianFreeValue σ n z r b < δ*(1+ε)/2 ∧
      canonicalGaussianFreeValue σ n z r (b+δ)-canonicalGaussianFreeValue σ n z r b < -δ*(1-ε)/2 := by
  let C := canonicalGaussianFreeValue σ n z r
  have hf : HasDerivAt C (-1/2) b := by
    simpa only [hstat] using canonicalGaussianFreeValue_hasDerivAt σ n z hz r hp
  have hlin := hf.isLittleO.def (by positivity : 0 < ε/4)
  have hpos : ∀ᶠ t in 𝓝 b, 0 < quadraticCascadePrecision σ t n z :=
    (quadraticCascadePrecision_hasDerivAt σ n z b).continuousAt.eventually (eventually_gt_nhds hp)
  obtain ⟨η,hη,hboth⟩ := Metric.eventually_nhds_iff.mp (hlin.and hpos)
  let δ := η/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdη : δ < η := by dsimp [δ]; linarith
  have hleft : dist (b-δ) b < η := by simpa [Real.dist_eq,abs_of_nonneg hδ.le] using hdη
  have hright : dist (b+δ) b < η := by simpa [Real.dist_eq,abs_of_nonneg hδ.le] using hdη
  obtain ⟨hl,hlp⟩ := hboth hleft
  obtain ⟨hr,hrp⟩ := hboth hright
  simp only [Real.norm_eq_abs,smul_eq_mul] at hl hr
  have hdl : b-δ-b = -δ := by ring
  have hdr : b+δ-b = δ := by ring
  rw [hdl,abs_neg,abs_of_pos hδ] at hl
  rw [hdr,abs_of_pos hδ] at hr
  refine ⟨δ,hδ,hlp,hrp,?_,?_⟩
  · have := (abs_le.mp hl).2
    dsimp only [C] at this
    nlinarith [mul_pos hε hδ]
  · have := (abs_le.mp hr).2
    dsimp only [C] at this
    nlinarith [mul_pos hε hδ]

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

theorem canonical_coordinate_joint_mean (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (r : ℝ≥0) :
    let μ := (Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n))
    let F := fun p => canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)
    Integrable F μ ∧ (∫ p, F p ∂μ) = d*canonicalGaussianFreeValue σ n z r b := by
  let ν := decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 r)
  let F := fun p : (Fin d → ℝ)×DecoratedCascade (Fin d → ℝ) n =>
    canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)
  let P := quadraticCascadePrecision σ b n z
  let A := (d : ℝ)*(-Real.log b/2+quadraticCascadeOffset σ b n z)
  let G := fun x : Fin d → ℝ => A+(∑ i, (x i)^2)/(2*P)
  have hG : MemLp G 2 μ := by
    convert (memLp_const A).add ((gaussian_square_sum_memLp_two d r).mul_const (2*P)⁻¹) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [G,div_eq_mul_inv,Pi.add_apply]
  have hF : Measurable F := (canonicalCoordinateLog_measurable d n σ b z).comp
    ((Measurable.of_eval (fun i => Measurable.of_eval (fun _ =>
      (measurable_pi_apply i).comp measurable_fst))).prodMk measurable_snd)
  have hsec : ∀ x, MemLp (fun η => F (x,η)) 2 (ν : Measure _) ∧
      (∫ η, (F (x,η)-G x)^2 ∂ν) ≤ cascadeLogFluctuationConstant n z := by
    intro x
    have he := finiteCascade_terminal_log_second_moment_bound
      (piMarkLaw (fun _ : Fin d => standardGaussianMark)) (canonicalCoordinateStep d σ)
      (canonicalCoordinateStep_measurable d σ) n z hz hz0 hz1
      (canonicalCoordinatePotential_measurable d b) (canonical_coordinate_recursion d σ b n z hz0 hp).2
      (fun i _ => x i)
    rw [(canonical_coordinate_recursion d σ b n z hz0 hp).1 (fun i _ => x i)] at he
    exact he
  have hi : Integrable F (μ.prod ν) := integrable_prod_of_conditional_square μ ν hF hG
    (cascadeLogFluctuationConstant n z) (fun x => (hsec x).1) (fun x => (hsec x).2)
  refine ⟨hi,?_⟩
  change (∫ p, F p ∂μ.prod ν) = _
  rw [integral_prod _ hi]
  have he : ∀ x, (∫ η, F (x,η) ∂ν) = G x := by
    intro x
    exact canonical_coordinate_log_mean d σ b n z hz hz0 hz1 hp (fun i _ => x i)
  simp_rw [he]
  change (∫ x, A+(∑ i, (x i)^2)/(2*P) ∂μ) = _
  rw [integral_add (integrable_const A)
    ((gaussian_square_sum_memLp_two d r).integrable (by norm_num) |>.div_const (2*P)),integral_div]
  change (∫ _ : Fin d → ℝ, A ∂μ)+(∫ x : Fin d → ℝ, ∑ i, (x i)^2 ∂Measure.pi (fun _ => gaussianReal 0 r))/(2*P) = _
  rw [gaussian_square_sum_mean]
  simp only [integral_const,probReal_univ,one_smul]
  dsimp only [A,P,canonicalGaussianFreeValue]
  ring

lemma expected_eventually_gt_of_probability_lower
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hi : ∀ n, Integrable (X n) (μ n))
    (hn : ∀ n, 0 ≤ᵐ[μ n] X n) {c : ℝ}
    (hp : ∀ a : ℝ, a < c →
      Tendsto (fun n => (μ n).real {ω | a ≤ X n ω}) atTop (𝓝 1)) :
    ∀ b : ℝ, b < c → ∀ᶠ n in atTop, b < ∫ ω, X n ω ∂μ n := by
  intro b hb
  by_cases hb0 : b < 0
  · exact Eventually.of_forall fun n => hb0.trans_le (integral_nonneg_of_ae (hn n))
  · obtain ⟨a, hba, hac⟩ := exists_between hb
    have he := (hp a hac).const_mul a
    simp only [mul_one] at he
    have hev : ∀ᶠ n in atTop, b < a*(μ n).real {ω | a ≤ X n ω} :=
      he.eventually (lt_mem_nhds hba)
    filter_upwards [hev] with n hnb
    exact hnb.trans_le (mul_meas_ge_le_integral_of_nonneg (hn n) (hi n) a)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereBridge
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

lemma decoratedLeafIntegral_exp {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (H : X → ℝ) (n : ℕ) (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step (fun x => ENNReal.ofReal (Real.exp (H x))) n p =
      decoratedTerminalTotalE step H n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [decoratedLeafIntegral, decoratedTerminalTotalE, ih]

lemma decoratedLeafIntegral_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (hs : Measurable step) (F : X → ℝ≥0∞)
    (hF : Measurable F) (n : ℕ) : Measurable (decoratedLeafIntegral step F n) := by
  induction n with
  | zero => exact hF.comp measurable_fst
  | succ n ih =>
    have hm : Measurable (fun p : (X × DecoratedCascade S (n+1)) ×
        (ℝ × (S × DecoratedCascade S n)) =>
        ENNReal.ofReal (Real.exp p.2.1) *
          decoratedLeafIntegral step F n (step (p.1.1,p.2.2.1),p.2.2.2)) :=
      (measurable_snd.fst.exp.ennreal_ofReal).mul
        (ih.comp ((hs.comp (measurable_fst.fst.prodMk measurable_snd.snd.fst)).prodMk
          measurable_snd.snd.snd))
    exact hm.lintegral_kernel_prod_right' (κ := markedStableCountKernel.prodMkLeft X)

lemma decoratedLeafIntegral_param_measurable {A X S : Type}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (hs : Measurable step) (F : A × X → ℝ≥0∞)
    (hF : Measurable F) (n : ℕ) :
    Measurable (fun p : A × (X × DecoratedCascade S n) =>
      decoratedLeafIntegral step (fun x => F (p.1,x)) n p.2) := by
  induction n with
  | zero => exact hF.comp (measurable_fst.prodMk measurable_snd.fst)
  | succ n ih =>
    have hm : Measurable (fun p : (A × (X × DecoratedCascade S (n+1))) ×
        (ℝ × (S × DecoratedCascade S n)) =>
        ENNReal.ofReal (Real.exp p.2.1) *
          decoratedLeafIntegral step (fun x => F (p.1.1,x)) n
            (step (p.1.2.1,p.2.2.1),p.2.2.2)) :=
      (measurable_snd.fst.exp.ennreal_ofReal).mul
        (ih.comp (measurable_fst.fst.prodMk
          ((hs.comp (measurable_fst.snd.fst.prodMk measurable_snd.snd.fst)).prodMk
            measurable_snd.snd.snd)))
    exact hm.lintegral_kernel_prod_right'
      (κ := (markedStableCountKernel.prodMkLeft X).prodMkLeft A)

lemma decoratedLeafIntegral_mono {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) {F G : X → ℝ≥0∞} (h : ∀ x, F x ≤ G x)
    (n : ℕ) (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step F n p ≤ decoratedLeafIntegral step G n p := by
  induction n with
  | zero => exact h p.1
  | succ n ih =>
    exact lintegral_mono fun q => mul_le_mul_right (ih _) _

lemma decoratedLeafIntegral_const_mul {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (F : X → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (n : ℕ) (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step (fun x => c * F x) n p =
      c * decoratedLeafIntegral step F n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [decoratedLeafIntegral, ih, mul_left_comm _ c]
    exact lintegral_const_mul' _ _ hc

lemma decoratedLeafIntegral_lintegral {A X S : Type}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace S]
    (μ : Measure A) [SFinite μ] (step : X × S → X) (hs : Measurable step)
    (F : A × X → ℝ≥0∞) (hF : Measurable F) (n : ℕ)
    (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step (fun x => ∫⁻ a, F (a,x) ∂μ) n p =
      ∫⁻ a, decoratedLeafIntegral step (fun x => F (a,x)) n p ∂μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [decoratedLeafIntegral, ih]
    have hm : Measurable (fun q : (ℝ × (S × DecoratedCascade S n)) × A =>
        ENNReal.ofReal (Real.exp q.1.1) *
          decoratedLeafIntegral step (fun x => F (q.2,x)) n
            (step (p.1,q.1.2.1),q.1.2.2)) :=
      (measurable_fst.fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_param_measurable step hs F hF n).comp
          (measurable_snd.prodMk
            ((hs.comp (measurable_const.prodMk measurable_fst.snd.fst)).prodMk
              measurable_fst.snd.snd)))
    calc
      _ = ∫⁻ q : ℝ × (S × DecoratedCascade S n), ∫⁻ a,
          ENNReal.ofReal (Real.exp q.1) *
            decoratedLeafIntegral step (fun x => F (a,x)) n
              (step (p.1,q.2.1),q.2.2) ∂μ ∂markedStableCountKernel p.2 := by
        apply lintegral_congr
        intro q
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = _ := lintegral_lintegral_swap hm.aemeasurable

lemma decoratedFieldFactor_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (d : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin d)
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) :
    Measurable (decoratedFieldFactor d step field k p) := by
  let F : Spin d × X → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (inner ℝ (field q.2) q.1))
  have hF : Measurable F :=
    (((hf.comp measurable_snd).inner measurable_fst).exp.ennreal_ofReal)
  have hm : Measurable (fun q : Spin d × (X × DecoratedCascade S k) =>
      decoratedLeafIntegral step (fun y => F (q.1,y)) k q.2) :=
    decoratedLeafIntegral_param_measurable step hs F hF k
  have hp : Measurable (fun x : Spin d => (x,p)) := measurable_id.prodMk measurable_const
  change Measurable (fun x : Spin d => decoratedLeafIntegral step (fun y => F (x,y)) k p)
  have hh := hm.comp hp
  exact hh

lemma decoratedAngularFactor_eq {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) (r : ℝ) :
    decoratedAngularFactor n step field k p r =
      decoratedLeafIntegral step (fun y => ENNReal.ofReal (sphericalExp n (field y) r)) k p := by
  have h := decoratedLeafIntegral_lintegral (unitSphereLaw (n+1)) step hs
    (fun q : (Metric.sphere (0:Spin (n+1)) 1) × X =>
      ENNReal.ofReal (Real.exp (inner ℝ (field q.2) (r • (q.1:Spin (n+1))))))
    (((hf.comp measurable_snd).inner (measurable_fst.subtype_coe.const_smul r)).exp.ennreal_ofReal)
    k p
  change (∫⁻ a : Metric.sphere (0:Spin (n+1)) 1,
    decoratedLeafIntegral step (fun y => ENNReal.ofReal (Real.exp (inner ℝ (field y) (r • (a:Spin (n+1)))))) k p
      ∂unitSphereLaw (n+1)) = _
  rw [← h]
  congr 1
  funext y
  simp only [inner_smul_right]
  exact (ofReal_integral_eq_lintegral_ofReal
    (unitSphere_continuous_integrable (by fun_prop))
    (Eventually.of_forall fun u => (Real.exp_pos _).le)).symm

lemma decoratedAngularFactor_mono {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    decoratedAngularFactor n step field k p r ≤ decoratedAngularFactor n step field k p s := by
  rw [decoratedAngularFactor_eq n step hs field hf, decoratedAngularFactor_eq n step hs field hf]
  exact decoratedLeafIntegral_mono step
    (fun y => ENNReal.ofReal_le_ofReal (sphericalExp_mono n (field y) hr hrs)) k p

lemma decoratedAngularFactor_mass_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) (r : ℝ) :
    decoratedTerminalTotalE step (fun _ => 0) k p ≤ decoratedAngularFactor n step field k p r := by
  rw [decoratedAngularFactor_eq n step hs field hf, ← decoratedLeafIntegral_exp]
  apply decoratedLeafIntegral_mono
  intro y
  simpa using ENNReal.ofReal_le_ofReal (one_le_sphericalExp n (field y) r)

theorem decoratedCanonical_band_bounds {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) (b ε : ℝ) :
    decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) *
      canonicalRadialMass n b (normSquareBand n ε) ≤
        (∫⁻ x in normSquareBand n ε,
          decoratedFieldFactor (n+1) step field k p x ∂canonicalRadialMass n b) ∧
    (∫⁻ x in normSquareBand n ε,
      decoratedFieldFactor (n+1) step field k p x ∂canonicalRadialMass n b) ≤
      decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) *
        canonicalRadialMass n b (normSquareBand n ε) := by
  have hm := decoratedFieldFactor_measurable (n+1) step hs field hf k p
  have hh := polar_weighted_bounds (volume : Measure (RadialSpace n))
    (decoratedFieldFactor (n+1) step field k p) hm
    (canonicalBandRadiusWeight n b ε) (canonicalBandRadiusWeight_measurable n b ε)
    (L := decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))))
    (U := decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))))
  rw [canonicalBandRadiusWeight_integral n b ε _ hm,canonicalBandRadiusWeight_mass] at hh
  apply hh
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change _ ≤ decoratedAngularFactor n step field k p r
    apply decoratedAngularFactor_mono n step hs field hf k p (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff).mpr ⟨r.property.le,hb.1⟩
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change decoratedAngularFactor n step field k p r ≤ _
    apply decoratedAngularFactor_mono n step hs field hf k p r.property.le
    exact (Real.le_sqrt' r.property).mpr hb.2

lemma coordinateLeafField_measurable (d : ℕ) : Measurable (coordinateLeafField d) := by
  apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply 0).comp (measurable_pi_apply i)

lemma coordinateLeafField_norm_sq (d : ℕ) (x : Fin d → ℕ → ℝ) :
    ‖coordinateLeafField d x‖^2 = ∑ i, (x i 0)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [coordinateLeafField,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs]

lemma canonicalCoordinatePotential_eq_norm (d : ℕ) (b : ℝ) (x : Fin d → ℕ → ℝ) :
    canonicalCoordinatePotential d b x = - (d:ℝ)*Real.log b/2 + ‖coordinateLeafField d x‖^2/(2*b) := by
  rw [coordinateLeafField_norm_sq]
  simp only [canonicalCoordinatePotential,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_div]
  ring

theorem canonicalCoordinateTotalE_eq_radial (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
      (canonicalCoordinatePotential (n+1) b) k p =
      ∫⁻ x, decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
        (coordinateLeafField (n+1)) k p x ∂canonicalRadialMass n b := by
  let : SFinite (canonicalRadialMass n b) := by
    unfold canonicalRadialMass
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hf : Measurable (fun q : Spin (n+1) × (Fin (n+1) → ℕ → ℝ) =>
      ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) q.2) q.1))) :=
    (((coordinateLeafField_measurable (n+1)).comp measurable_snd).inner measurable_fst).exp.ennreal_ofReal
  have h := decoratedLeafIntegral_lintegral (canonicalRadialMass n b)
    (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep_measurable (n+1) σ) _ hf k p
  change _ = ∫⁻ x, decoratedLeafIntegral (canonicalCoordinateStep (n+1) σ)
    (fun y => ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) y) x))) k p
      ∂canonicalRadialMass n b
  rw [← h, ← decoratedLeafIntegral_exp]
  congr 1
  funext y
  change _ = ∫⁻ a, ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) y) a)) ∂canonicalRadialMass n b
  rw [canonicalRadial_linear_integral n hb,canonicalCoordinatePotential_eq_norm]

lemma decoratedLeafIntegral_holder {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (hs : Measurable step) {F G : X → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (k : ℕ)
    (p : X × DecoratedCascade S k) :
    decoratedLeafIntegral step (fun x => F x ^ a * G x ^ b) k p ≤
      decoratedLeafIntegral step F k p ^ a * decoratedLeafIntegral step G k p ^ b := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    let H : (ℝ × (S × DecoratedCascade S k)) → X × DecoratedCascade S k :=
      fun q => (step (p.1,q.2.1),q.2.2)
    have hH : Measurable H :=
      (hs.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd
    have hFm : Measurable (fun q => ENNReal.ofReal (Real.exp q.1) *
        decoratedLeafIntegral step F k (H q)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_measurable step hs F hF k).comp hH)
    have hGm : Measurable (fun q => ENNReal.ofReal (Real.exp q.1) *
        decoratedLeafIntegral step G k (H q)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_measurable step hs G hG k).comp hH)
    change (∫⁻ q, ENNReal.ofReal (Real.exp q.1) *
      decoratedLeafIntegral step (fun x => F x ^ a * G x ^ b) k (H q)
        ∂markedStableCountKernel p.2) ≤ _
    refine le_trans (lintegral_mono fun q => mul_le_mul_right (ih (H q)) _) ?_
    calc
      _ = ∫⁻ q, (ENNReal.ofReal (Real.exp q.1) * decoratedLeafIntegral step F k (H q)) ^ a *
          (ENNReal.ofReal (Real.exp q.1) * decoratedLeafIntegral step G k (H q)) ^ b
            ∂markedStableCountKernel p.2 := by
        congr 1
        funext q
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha,ENNReal.mul_rpow_of_nonneg _ _ hb]
        have he : ENNReal.ofReal (Real.exp q.1) ^ a * ENNReal.ofReal (Real.exp q.1) ^ b =
            ENNReal.ofReal (Real.exp q.1) := by
          rw [← ENNReal.rpow_add _ _ (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top,hab,ENNReal.rpow_one]
        calc
          _ = (ENNReal.ofReal (Real.exp q.1) ^ a * ENNReal.ofReal (Real.exp q.1) ^ b) *
              (decoratedLeafIntegral step F k (H q) ^ a * decoratedLeafIntegral step G k (H q) ^ b) := by rw [he]
          _ = _ := by ring
      _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le hFm.aemeasurable hGm.aemeasurable ha hb hab

lemma ofReal_exp_affine (x y a b : ℝ) :
    ENNReal.ofReal (Real.exp (a*x+b*y)) =
      ENNReal.ofReal (Real.exp x) ^ a * ENNReal.ofReal (Real.exp y) ^ b := by
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1 <;> rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp] <;> congr 1 <;> ring_nf

lemma sphericalExp_holder (n : ℕ) (z : Spin (n+1)) (r s : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ENNReal.ofReal (sphericalExp n z (a*r+b*s)) ≤
      ENNReal.ofReal (sphericalExp n z r)^a * ENNReal.ofReal (sphericalExp n z s)^b := by
  have he (t : ℝ) : ENNReal.ofReal (sphericalExp n z t) =
      ∫⁻ x : Metric.sphere (0 : Spin (n+1)) 1,
        ENNReal.ofReal (Real.exp (inner ℝ z (t • x.val))) ∂unitSphereLaw (n+1) := by
    simp only [inner_smul_right]
    exact ofReal_integral_eq_lintegral_ofReal
      (unitSphere_continuous_integrable (by fun_prop))
      (ae_of_all _ fun _ => (Real.exp_pos _).le)
  simp_rw [he]
  have h (x : Metric.sphere (0 : Spin (n+1)) 1) :
      ENNReal.ofReal (Real.exp (inner ℝ z ((a*r+b*s) • x.val))) =
        ENNReal.ofReal (Real.exp (inner ℝ z (r • x.val)))^a *
          ENNReal.ofReal (Real.exp (inner ℝ z (s • x.val)))^b := by
    simp only [inner_smul_right]
    rw [show (a*r+b*s)*inner ℝ z x.val = a*(r*inner ℝ z x.val)+b*(s*inner ℝ z x.val) by ring]
    exact ofReal_exp_affine _ _ _ _
  simp_rw [h]
  exact ENNReal.lintegral_mul_norm_pow_le (by fun_prop) (by fun_prop) ha hb hab

lemma decoratedAngularFactor_holder {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step)
    (z : X → Spin (n+1)) (hz : Measurable z) (k : ℕ) (p : X × DecoratedCascade S k)
    (r s : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    decoratedAngularFactor n step z k p (a*r+b*s) ≤
      decoratedAngularFactor n step z k p r ^ a * decoratedAngularFactor n step z k p s ^ b := by
  simp_rw [decoratedAngularFactor_eq n step hs z hz]
  refine (decoratedLeafIntegral_mono step (fun x => sphericalExp_holder n (z x) r s ha hb hab) k p).trans ?_
  apply decoratedLeafIntegral_holder step hs _ _ ha hb hab
  all_goals
    unfold sphericalExp
    apply ENNReal.measurable_ofReal.comp
    exact (show StronglyMeasurable (fun p : X × Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (_ * inner ℝ (z p.1) (p.2:Spin (n+1)))) from (by fun_prop)).integral_prod_right'.measurable

lemma decoratedTerminalTotal_pos_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X × S → X) (hs : Measurable step)
    (H : X → ℝ) (hH : Measurable H) (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hI : finiteCascadeFractionalIntegrable ν step H k z) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν k z : Measure (DecoratedCascade S k)),
      0 < decoratedTerminalTotal step H k (x,η) := by
  have hid := decoratedWeightedTotal_identDistrib ν step hs k z hz0 hz1
    (finiteCascadeShifts ν step k z H) (finiteCascadeShifts_measurable ν step hs k z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step k z
      (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step k z
      (fun j => (hz0 j).ne') H hI i y).2) x
  have hp := hid.symm.ae_snd measurableSet_Ioi (cascadeTotal_regular k z hz hz0 hz1).1
  filter_upwards [hp] with η hη
  rw [decoratedTerminalTotal_telescoping ν step H k z]
  exact mul_pos (Real.exp_pos _) hη

lemma decoratedTerminalTotal_zero_pos {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X × S → X) (hs : Measurable step)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν k z : Measure (DecoratedCascade S k)),
      0 < decoratedTerminalTotal step (fun _ => 0) k (x,η) := by
  have hid := decoratedWeightedTotal_identDistrib ν step hs k z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  simpa only [decoratedTerminalTotal_zero] using
    hid.symm.ae_snd measurableSet_Ioi (cascadeTotal_regular k z hz hz0 hz1).1

lemma canonicalCoordinateTotal_pos (d k : ℕ) (σ : ℕ → ℝ) (b : ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    ∀ᵐ p ∂coordinateCascadeLaw d k z r,
      0 < decoratedTerminalTotal (canonicalCoordinateStep d σ)
        (canonicalCoordinatePotential d b) k ((fun i _ => p.1 i),p.2) := by
  have hm : Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
      decoratedTerminalTotal (canonicalCoordinateStep d σ) (canonicalCoordinatePotential d b) k
        ((fun i _ => p.1 i),p.2)) :=
    (decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _ (canonicalCoordinateStep_measurable d σ)
      (canonicalCoordinatePotential_measurable d b) k z).comp
        (show Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
          ((fun (i : Fin d) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hm)).mpr
  exact ae_of_all _ fun x => decoratedTerminalTotal_pos_of_fractional
    (piMarkLaw (fun _ : Fin d => standardGaussianMark)) (canonicalCoordinateStep d σ)
    (canonicalCoordinateStep_measurable d σ) _ (canonicalCoordinatePotential_measurable d b)
    k z hz hz0 hz1 (canonical_coordinate_recursion d σ b k z hz0 hp).2 (fun i _ => x i)

lemma canonicalCoordinateBase_pos (d k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ≥0) :
    ∀ᵐ p ∂coordinateCascadeLaw d k z r,
      0 < decoratedTerminalTotal (canonicalCoordinateStep d σ)
        (fun _ => 0) k ((fun i _ => p.1 i),p.2) := by
  have hm : Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
      decoratedTerminalTotal (canonicalCoordinateStep d σ) (fun _ => 0) k
        ((fun i _ => p.1 i),p.2)) :=
    (decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _ (canonicalCoordinateStep_measurable d σ)
      measurable_const k z).comp
        (show Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
          ((fun (i : Fin d) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hm)).mpr
  exact ae_of_all _ fun x => decoratedTerminalTotal_zero_pos
    (piMarkLaw (fun _ : Fin d => standardGaussianMark)) (canonicalCoordinateStep d σ)
    (canonicalCoordinateStep_measurable d σ) k z hz hz0 hz1 (fun i _ => x i)

lemma sphericalExp_le_gaussian (n : ℕ) (z : Spin (n+1)) (R : ℝ) {b : ℝ} (hb : 0 < b) :
    sphericalExp n z R ≤ Real.exp (‖z‖^2/(2*b)+b*R^2/2) := by
  have h (u : Metric.sphere (0 : Spin (n+1)) 1) :
      R * inner ℝ z (u : Spin (n+1)) ≤ ‖z‖^2/(2*b)+b*R^2/2 := by
    have hn : ‖(u : Spin (n+1))‖ = 1 := by simp
    have hh := sq_nonneg ‖z - (b*R) • (u : Spin (n+1))‖
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,hn,Real.norm_eq_abs,mul_one,sq_abs] at hh
    calc
      _ ≤ (‖z‖^2+(b*R)^2)/(2*b) :=
        (le_div_iff₀ (by positivity : 0 < 2*b)).mpr (by nlinarith [hh])
      _ = _ := by field_simp
  unfold sphericalExp
  calc
    _ ≤ ∫ _ : Metric.sphere (0 : Spin (n+1)) 1,
        Real.exp (‖z‖^2/(2*b)+b*R^2/2) ∂unitSphereLaw (n+1) :=
      integral_mono (unitSphere_continuous_integrable (by fun_prop)) (integrable_const _)
        (fun u => Real.exp_le_exp.mpr (h u))
    _ = _ := by simp

lemma decoratedAngularFactor_le_canonical (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ) (coordinateLeafField (n+1)) k p R ≤
      ENNReal.ofReal (Real.exp (((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2)) *
        decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p := by
  rw [decoratedAngularFactor_eq n _ (canonicalCoordinateStep_measurable (n+1) σ) _
    (coordinateLeafField_measurable (n+1)), ← decoratedLeafIntegral_exp,
    ← decoratedLeafIntegral_const_mul _ _ _ ENNReal.ofReal_ne_top]
  apply decoratedLeafIntegral_mono
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,canonicalCoordinatePotential_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  convert sphericalExp_le_gaussian n (coordinateLeafField (n+1) x) R hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma coordinateAngularLog_regular (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p) :
    0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k p R).toReal ∧
      0 ≤ coordinateAngularLog n k σ R p ∧
      coordinateAngularLog n k σ R p ≤ canonicalCoordinateLog (n+1) k σ b p +
        ((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2 := by
  let A := decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p R
  let B := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p
  let C := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p
  let c := ((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2
  have hB : 0 < B.toReal := h0
  have hC : 0 < C.toReal := hc
  obtain ⟨hB₀,hBtop⟩ := ENNReal.toReal_pos_iff.mp hB
  obtain ⟨hC₀,hCtop⟩ := ENNReal.toReal_pos_iff.mp hC
  have hba : B ≤ A := decoratedAngularFactor_mass_le n _ (canonicalCoordinateStep_measurable (n+1) σ)
    _ (coordinateLeafField_measurable (n+1)) k p R
  have hac : A ≤ ENNReal.ofReal (Real.exp c)*C := decoratedAngularFactor_le_canonical n k σ R hb p
  have hAtop : A ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop.ne) hac
  have hA := ENNReal.toReal_pos (ne_of_gt (hB₀.trans_le hba)) hAtop
  have hba' := ENNReal.toReal_mono hAtop hba
  have hac' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop.ne) hac
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hac'
  refine ⟨hA,?_,?_⟩
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hba'))
  · have hh := Real.log_le_log (div_pos hA hB) (div_le_div_of_nonneg_right hac' hB.le)
    rw [Real.log_div (mul_pos (Real.exp_pos c) hC).ne' hB.ne',
      Real.log_mul (Real.exp_pos c).ne' hC.ne',Real.log_exp] at hh
    change Real.log (A.toReal/B.toReal) ≤ Real.log (C.toReal/B.toReal)+
      ((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2
    rw [Real.log_div hC.ne' hB.ne']
    dsimp only [c] at hh
    linarith

lemma coordinateAngularLog_convex (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p) :
    ConvexOn ℝ Set.univ (fun R => coordinateAngularLog n k σ R p) := by
  let A := fun R => decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p R
  let B := decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p
  have hA (R : ℝ) : 0 < (A R).toReal := (coordinateAngularLog_regular n k σ R hb p h0 hc).1
  have ht (R : ℝ) : A R ≠ ∞ := (ENNReal.toReal_pos_iff.mp (hA R)).2.ne
  refine ⟨convex_univ,?_⟩
  intro R _ S _ a c ha hc' hac
  have H := decoratedAngularFactor_holder n (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinateStep_measurable (n+1) σ) (coordinateLeafField (n+1))
    (coordinateLeafField_measurable (n+1)) k p R S ha hc' hac
  have Hr := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ha (ht R)) (ENNReal.rpow_ne_top_of_nonneg hc' (ht S))) H
  change (A (a*R+c*S)).toReal ≤ (A R ^ a * A S ^ c).toReal at Hr
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at Hr
  have Hlog := Real.log_le_log (hA (a*R+c*S)) Hr
  rw [Real.log_mul (Real.rpow_pos_of_pos (hA R) a).ne' (Real.rpow_pos_of_pos (hA S) c).ne',
    Real.log_rpow (hA R),Real.log_rpow (hA S)] at Hlog
  simp only [smul_eq_mul]
  change Real.log ((A (a*R+c*S)).toReal/B) ≤ a*Real.log ((A R).toReal/B)+c*Real.log ((A S).toReal/B)
  rw [Real.log_div (hA _).ne' h0.ne',Real.log_div (hA R).ne' h0.ne',Real.log_div (hA S).ne' h0.ne']
  have hh := congrArg (fun t : ℝ => t * Real.log B) hac
  nlinarith [Hlog, hh]

lemma coordinateAngularLog_measurable (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ) :
    Measurable (coordinateAngularLog n k σ R) := by
  let X := Fin (n+1) → ℕ → ℝ
  let S := Fin (n+1) → ℝ
  let F : Spin (n+1) × X → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) q.2) q.1))
  have hm := decoratedLeafIntegral_param_measurable (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinateStep_measurable (n+1) σ) F
    ((((coordinateLeafField_measurable (n+1)).comp measurable_snd).inner measurable_fst).exp.ennreal_ofReal) k
  have hmap : Measurable (fun q : (X × DecoratedCascade S k) × Metric.sphere (0:Spin (n+1)) 1 =>
      (R • (q.2:Spin (n+1)),q.1)) :=
    (measurable_snd.subtype_coe.const_smul R).prodMk measurable_fst
  have hh := hm.comp hmap
  have ha : Measurable (fun p : X × DecoratedCascade S k =>
      decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ) (coordinateLeafField (n+1)) k p R) :=
    hh.lintegral_prod_right'
  exact (ha.ennreal_toReal.div (decoratedTerminalTotal_measurable
    (piMarkLaw (fun _ : Fin (n+1) => standardGaussianMark)) _
    (canonicalCoordinateStep_measurable (n+1) σ) measurable_const k (fun _ => 0))).log

lemma coordinateAngularLog_integrable (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ} (R : ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    Integrable (fun p => coordinateAngularLog n k σ R ((fun i _ => p.1 i),p.2))
      (coordinateCascadeLaw (n+1) k z r) := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hm := (coordinateAngularLog_measurable n k σ R).comp
    (show Measurable (fun p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k =>
      ((fun (i : Fin (n+1)) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  have hi := (canonical_coordinate_joint_mean (n+1) σ b k z hz hz0 hz1 hp r).1
  apply (hi.add (integrable_const (((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2))).mono' hm.aestronglyMeasurable
  filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
    canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
  have h := coordinateAngularLog_regular n k σ R hb _ h0 hc
  simp only [Function.comp_apply, Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg h.2.1]
  linarith [h.2.2]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ShellBridge
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma canonicalWeighted_compl_band_le (n : ℕ) (F : RadialSpace n → ℝ≥0∞)
    (hF : Measurable F) (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in (normSquareBand n ε)ᶜ, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b-δ)) +
      ENNReal.ofReal (Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b+δ)) := by
  have hs : (normSquareBand n ε)ᶜ ⊆
      {x : RadialSpace n | ((n+1:ℕ):ℝ)*(1+ε) ≤ ‖x‖^2} ∪
      {x : RadialSpace n | ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1-ε)} := by
    intro x hx
    simp only [normSquareBand,mem_compl_iff,mem_ofPred_eq,not_and_or,not_le] at hx
    rcases hx with hx | hx
    · exact Or.inr hx.le
    · exact Or.inl hx.le
  exact (lintegral_mono_set hs).trans ((lintegral_union_le _ _ _).trans
    (add_le_add (canonicalWeighted_upper_tail n F hF b ε hδ)
      (canonicalWeighted_lower_tail n F hF b ε hδ)))

lemma exp_log_quotient_mul {x y u : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hu : 0 < u) (c : ℝ) :
    Real.exp (Real.log (y/u)-Real.log (x/u)+c)*x = Real.exp c*y := by
  rw [Real.exp_add,Real.exp_sub,Real.exp_log (div_pos hy hu),
    Real.exp_log (div_pos hx hu)]
  field_simp

lemma canonicalCoordinateBandTotalE_le (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ}
    (hb : 0 < b) (ε : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    canonicalCoordinateBandTotalE n k σ b ε p ≤
      decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p := by
  rw [canonicalCoordinateTotalE_eq_radial n k σ hb]
  exact setLIntegral_le_lintegral _ _

lemma canonicalCoordinate_half_band (n k : ℕ) (σ : ℕ → ℝ) {b δ : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hbm : 0 < b-δ) (ε : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) (b-δ)) k p)
    (hp : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) (b+δ)) k p)
    (hrm : Real.exp (canonicalCoordinateLog (n+1) k σ (b-δ) p -
      canonicalCoordinateLog (n+1) k σ b p - ((n+1:ℕ):ℝ)*(δ*(1+ε)/2)) ≤ 1/4)
    (hrp : Real.exp (canonicalCoordinateLog (n+1) k σ (b+δ) p -
      canonicalCoordinateLog (n+1) k σ b p - ((n+1:ℕ):ℝ)*(-δ*(1-ε)/2)) ≤ 1/4) :
    decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p / 2 ≤
      (canonicalCoordinateBandTotalE n k σ b ε p).toReal := by
  let F := decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p
  have hF : Measurable F := decoratedFieldFactor_measurable (n+1) _
    (canonicalCoordinateStep_measurable (n+1) σ) _ (coordinateLeafField_measurable (n+1)) k p
  let T := fun a => decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinatePotential (n+1) a) k p
  let B := canonicalCoordinateBandTotalE n k σ b ε p
  have ht : T b ≠ ∞ := (ENNReal.toReal_pos_iff.mp hc).2.ne
  have hmt : T (b-δ) ≠ ∞ := (ENNReal.toReal_pos_iff.mp hm).2.ne
  have hpt : T (b+δ) ≠ ∞ := (ENNReal.toReal_pos_iff.mp hp).2.ne
  have hBt : B ≠ ∞ := ne_top_of_le_ne_top ht (canonicalCoordinateBandTotalE_le n k σ hb ε p)
  have he := lintegral_add_compl F (μ := canonicalRadialMass n b) (normSquareBand_measurable n ε)
  have hu := canonicalWeighted_compl_band_le n F hF b ε hδ
  have hbp : 0 < b+δ := add_pos_of_pos_of_nonneg hb hδ
  have hid (a : ℝ) (ha : 0 < a) : (∫⁻ x, F x ∂canonicalRadialMass n a) = T a :=
    (canonicalCoordinateTotalE_eq_radial n k σ ha p).symm
  rw [hid b hb] at he
  rw [hid (b-δ) hbm,hid (b+δ) hbp] at hu
  have hbnd : T b ≤ B + (ENNReal.ofReal (Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)) * T (b-δ) +
      ENNReal.ofReal (Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)) * T (b+δ)) := by
    rw [← he]
    exact add_le_add le_rfl hu
  have hre := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hBt,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt⟩⟩) hbnd
  rw [ENNReal.toReal_add hBt (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt⟩),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt),ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hre
  have hem := exp_log_quotient_mul hc hm h0 (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)
  have hep := exp_log_quotient_mul hc hp h0 (δ*((n+1:ℕ):ℝ)*(1-ε)/2)
  change Real.exp (canonicalCoordinateLog (n+1) k σ (b-δ) p-
    canonicalCoordinateLog (n+1) k σ b p + _) * (T b).toReal =
      Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)*(T (b-δ)).toReal at hem
  change Real.exp (canonicalCoordinateLog (n+1) k σ (b+δ) p-
    canonicalCoordinateLog (n+1) k σ b p + _) * (T b).toReal =
      Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)*(T (b+δ)).toReal at hep
  change 0 < (T b).toReal at hc
  have hm' : Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)*(T (b-δ)).toReal ≤ (T b).toReal/4 := by
    rw [← hem]
    convert mul_le_mul_of_nonneg_right hrm hc.le using 1 <;> congr 1 <;> ring_nf
  have hp' : Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)*(T (b+δ)).toReal ≤ (T b).toReal/4 := by
    rw [← hep]
    convert mul_le_mul_of_nonneg_right hrp hc.le using 1 <;> congr 1 <;> ring_nf
  change (T b).toReal/2 ≤ B.toReal
  linarith

theorem canonicalCoordinate_bad_half_band_tendsto_zero (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => coordinateCascadeLaw (n+1) k z r
      {p | (canonicalCoordinateBandTotalE n k σ b ε ((fun i _ => p.1 i),p.2)).toReal <
        decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
          (canonicalCoordinatePotential (n+1) b) k ((fun i _ => p.1 i),p.2)/2}) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hpm,hpp,hrm,hrp⟩ := canonical_stationary_tail_rates σ k z
    (fun i => (hz0 i).le) r b hp hstat hε
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hbm : 0 < b-δ := hpm.trans_le (quadraticCascadePrecision_le σ (b-δ) k z (fun i => (hz0 i).le))
  let Xm := fun n (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) =>
    Real.exp (canonicalCoordinateLog (n+1) k σ (b-δ) ((fun i _ => p.1 i),p.2)-
      canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)-((n+1:ℕ):ℝ)*(δ*(1+ε)/2))
  let Xp := fun n (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) =>
    Real.exp (canonicalCoordinateLog (n+1) k σ (b+δ) ((fun i _ => p.1 i),p.2)-
      canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)-((n+1:ℕ):ℝ)*(-δ*(1-ε)/2))
  have htm : Tendsto (fun n => coordinateCascadeLaw (n+1) k z r {p | 1/4 ≤ Xm n p}) atTop (𝓝 0) :=
    (canonical_ratio_converges σ b (b-δ) (δ*(1+ε)/2) k z hz hz0 hz1 hp hpm r hrm
      (by norm_num : (0:ℝ)<1/4)).comp (tendsto_add_atTop_nat 1)
  have htp : Tendsto (fun n => coordinateCascadeLaw (n+1) k z r {p | 1/4 ≤ Xp n p}) atTop (𝓝 0) :=
    (canonical_ratio_converges σ b (b+δ) (-δ*(1-ε)/2) k z hz hz0 hz1 hp hpp r hrp
      (by norm_num : (0:ℝ)<1/4)).comp (tendsto_add_atTop_nat 1)
  have he := htm.add htp
  simp only [add_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  apply le_trans (measure_mono_ae (t := {p | 1/4 ≤ Xm n p} ∪ {p | 1/4 ≤ Xp n p}) ?_)
    (measure_union_le _ _)
  filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
    canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r,
    canonicalCoordinateTotal_pos (n+1) k σ (b-δ) z hz hz0 hz1 hpm r,
    canonicalCoordinateTotal_pos (n+1) k σ (b+δ) z hz hz0 hz1 hpp r] with p h0 hc hm hp'
  intro hbad
  by_cases hm' : 1/4 ≤ Xm n p
  · exact Or.inl hm'
  · right
    by_contra hp''
    have hhalf := canonicalCoordinate_half_band n k σ hb hδ.le hbm ε _ h0 hc hm hp'
      (not_le.mp hm').le (not_le.mp hp'').le
    exact (not_le.mpr hbad) hhalf

lemma canonicalCoordinate_shell_log_upper (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε)) :
    coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) p ≤
      canonicalCoordinateLog (n+1) k σ b p -
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε)) := by
  let A := decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε)))
  let T := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinatePotential (n+1) b) k p
  let M := canonicalRadialMass n b (normSquareBand n ε)
  have hA : 0 < A.toReal := (coordinateAngularLog_regular n k σ _ hb p h0 hc).1
  change 0 < T.toReal at hc
  change 0 < M.toReal at hm
  have hle : A*M ≤ T := (decoratedCanonical_band_bounds n _
    (canonicalCoordinateStep_measurable (n+1) σ) _ (coordinateLeafField_measurable (n+1)) k p b ε).1.trans
      (canonicalCoordinateBandTotalE_le n k σ hb ε p)
  have hr := ENNReal.toReal_mono (ENNReal.toReal_pos_iff.mp hc).2.ne hle
  rw [ENNReal.toReal_mul] at hr
  change A.toReal*M.toReal ≤ T.toReal at hr
  have hlog := Real.log_le_log (mul_pos hA hm) hr
  rw [Real.log_mul hA.ne' hm.ne'] at hlog
  change Real.log (A.toReal / _) ≤ Real.log (T.toReal / _) - Real.log M.toReal
  rw [Real.log_div hA.ne' h0.ne',Real.log_div hc.ne' h0.ne']
  linarith

lemma canonicalCoordinate_shell_log_lower (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε))
    (hh : decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p / 2 ≤
      (canonicalCoordinateBandTotalE n k σ b ε p).toReal) :
    canonicalCoordinateLog (n+1) k σ b p - Real.log 2 -
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε)) ≤
      coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) p := by
  let A := decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε)))
  let T := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinatePotential (n+1) b) k p
  let M := canonicalRadialMass n b (normSquareBand n ε)
  have hA : 0 < A.toReal := (coordinateAngularLog_regular n k σ _ hb p h0 hc).1
  change 0 < T.toReal at hc
  change 0 < M.toReal at hm
  have hle : canonicalCoordinateBandTotalE n k σ b ε p ≤ A*M :=
    (decoratedCanonical_band_bounds n _ (canonicalCoordinateStep_measurable (n+1) σ) _
      (coordinateLeafField_measurable (n+1)) k p b ε).2
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.toReal_pos_iff.mp hA).2.ne (ENNReal.toReal_pos_iff.mp hm).2.ne) hle
  rw [ENNReal.toReal_mul] at hr
  change T.toReal/2 ≤ _ at hh
  have hlog := Real.log_le_log (div_pos hc (by norm_num : (0:ℝ)<2)) (hh.trans hr)
  rw [Real.log_mul hA.ne' hm.ne',Real.log_div hc.ne' (by norm_num : (2:ℝ)≠0)] at hlog
  change Real.log (T.toReal / _) - Real.log 2 - Real.log M.toReal ≤ Real.log (A.toReal / _)
  rw [Real.log_div hc.ne' h0.ne',Real.log_div hA.ne' h0.ne']
  linarith

lemma convex_nonneg_radius_transfer {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hn : ∀ r, 0 ≤ f r) {R r s ε : ℝ} (hR : 0 < R)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : (1-ε)*R ≤ r) (hrR : r ≤ R)
    (hs : R ≤ s) (hsR : s ≤ (1+ε)*R) :
    f R ≤ f r + ε*f (2*R) ∧ f s ≤ f R + ε*f (2*R) := by
  have hr2 : 0 < 2*R-r := by linarith
  let c := (R-r)/(2*R-r)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hr2.le
  have hcε : c ≤ ε := (div_le_iff₀ hr2).mpr (by nlinarith)
  have hc1 : c ≤ 1 := hcε.trans hε1
  have hcEq : c*(2*R-r)=R-r := div_mul_cancel₀ _ hr2.ne'
  have he : (1-c)*r+c*(2*R) = R := by nlinarith [hcEq]
  have hl := hf.2 (mem_univ r) (mem_univ (2*R)) (sub_nonneg.mpr hc1) hc0 (by ring : 1-c+c=1)
  simp only [smul_eq_mul,he] at hl
  have hmix : (1-c)*f r+c*f (2*R) ≤ f r+ε*f (2*R) := by
    nlinarith [mul_nonneg hc0 (hn r),mul_le_mul_of_nonneg_right hcε (hn (2*R))]
  refine ⟨hl.trans hmix,?_⟩
  let d := (s-R)/R
  have hd0 : 0 ≤ d := div_nonneg (sub_nonneg.mpr hs) hR.le
  have hdε : d ≤ ε := (div_le_iff₀ hR).mpr (by nlinarith)
  have hd1 : d ≤ 1 := hdε.trans hε1
  have hdEq : d*R=s-R := div_mul_cancel₀ _ hR.ne'
  have he' : (1-d)*R+d*(2*R) = s := by nlinarith [hdEq]
  have hu := hf.2 (mem_univ R) (mem_univ (2*R)) (sub_nonneg.mpr hd1) hd0 (by ring : 1-d+d=1)
  simp only [smul_eq_mul,he'] at hu
  apply hu.trans
  nlinarith [mul_nonneg hd0 (hn R),mul_le_mul_of_nonneg_right hdε (hn (2*R))]

lemma sqrt_radius_band {d ε : ℝ} (hd : 0 < d) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1-ε)*Real.sqrt d ≤ Real.sqrt (d*(1-ε)) ∧
    Real.sqrt (d*(1-ε)) ≤ Real.sqrt d ∧
    Real.sqrt d ≤ Real.sqrt (d*(1+ε)) ∧
    Real.sqrt (d*(1+ε)) ≤ (1+ε)*Real.sqrt d := by
  have hs := Real.sq_sqrt hd.le
  have hre := Real.sq_sqrt (mul_nonneg hd.le (sub_nonneg.mpr hε1))
  have hse := Real.sq_sqrt (mul_nonneg hd.le (by linarith : 0≤1+ε))
  constructor
  · apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [mul_pow,hs]
    nlinarith [mul_nonneg (mul_nonneg hd.le hε) (sub_nonneg.mpr hε1)]
  constructor
  · exact Real.sqrt_le_sqrt (by nlinarith)
  constructor
  · exact Real.sqrt_le_sqrt (by nlinarith)
  · apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow,hs]
    nlinarith [mul_nonneg hd.le (sq_nonneg ε)]

lemma coordinateAngularLog_unit_radius_bounds (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p) :
    coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p ≤
      coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) p +
        ε*(canonicalCoordinateLog (n+1) k σ b p+((n+1:ℕ):ℝ)*(Real.log b/2+2*b)) ∧
    coordinateAngularLog n k σ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) p ≤
      coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p +
        ε*(canonicalCoordinateLog (n+1) k σ b p+((n+1:ℕ):ℝ)*(Real.log b/2+2*b)) := by
  have hd : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hr := sqrt_radius_band hd hε hε1
  have hconv := convex_nonneg_radius_transfer (coordinateAngularLog_convex n k σ hb p h0 hc)
    (fun r => (coordinateAngularLog_regular n k σ r hb p h0 hc).2.1)
    (Real.sqrt_pos.mpr hd) hε hε1 hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hbig := (coordinateAngularLog_regular n k σ (2*Real.sqrt (n+1:ℕ)) hb p h0 hc).2.2
  have he : ((n+1:ℕ):ℝ)*Real.log b/2+b*(2*Real.sqrt (n+1:ℕ))^2/2 =
      ((n+1:ℕ):ℝ)*(Real.log b/2+2*b) := by
    rw [mul_pow,Real.sq_sqrt hd.le]
    ring
  have hbige : coordinateAngularLog n k σ (2*Real.sqrt (n+1:ℕ)) p ≤
      canonicalCoordinateLog (n+1) k σ b p+((n+1:ℕ):ℝ)*(Real.log b/2+2*b) := by
    linarith [he]
  exact ⟨hconv.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbige hε)),
    hconv.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbige hε))⟩

lemma canonicalCoordinate_unitSphere_upper (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε)) :
    coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p ≤
      (1+ε)*canonicalCoordinateLog (n+1) k σ b p-
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))+
          ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b) := by
  have h₁ := canonicalCoordinate_shell_log_upper n k σ hb p h0 hc hm
  have h₂ := (coordinateAngularLog_unit_radius_bounds n k σ hb hε hε1 p h0 hc).1
  linarith

lemma canonicalCoordinate_unitSphere_lower (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε))
    (hh : decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k p / 2 ≤
      (canonicalCoordinateBandTotalE n k σ b ε p).toReal) :
    (1-ε)*canonicalCoordinateLog (n+1) k σ b p-Real.log 2-
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))-
          ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b) ≤
      coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) p := by
  have h₁ := canonicalCoordinate_shell_log_lower n k σ hb p h0 hc hm hh
  have h₂ := (coordinateAngularLog_unit_radius_bounds n k σ hb hε hε1 p h0 hc).2
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma normalizedCoordinateSphereLog_measurable (n k : ℕ) (σ : ℕ → ℝ) :
    Measurable (normalizedCoordinateSphereLog n k σ) := by
  have hm := (coordinateAngularLog_measurable n k σ (Real.sqrt (n+1:ℕ))).comp
    (show Measurable (fun p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k =>
      ((fun (i : Fin (n+1)) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  exact hm.div_const _

lemma normalizedCoordinateSphereLog_integrable (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    Integrable (normalizedCoordinateSphereLog n k σ) (coordinateCascadeLaw (n+1) k z r) :=
  (coordinateAngularLog_integrable n k σ (Real.sqrt (n+1:ℕ)) z hz hz0 hz1 hp r).div_const _

lemma normalizedCoordinateSphereLog_nonneg (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    0 ≤ᵐ[coordinateCascadeLaw (n+1) k z r] normalizedCoordinateSphereLog n k σ := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
    canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
  exact div_nonneg (coordinateAngularLog_regular n k σ _ hb _ h0 hc).2.1 (by positivity)

lemma expectedCoordinateSphereLog_upper (n k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : 0 < (canonicalRadialMass n b).real (normSquareBand n ε)) :
    expectedCoordinateSphereLog n k σ z r ≤
      (1+ε)*canonicalGaussianFreeValue σ k z r b-
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1:ℕ):ℝ)+
          ε*(Real.log b/2+2*b) := by
  let μ := coordinateCascadeLaw (n+1) k z r
  let C := fun p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k =>
    canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)
  let M := Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))
  let d : ℝ := n+1
  have hd : 0 < d := by dsimp [d]; positivity
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hi : Integrable C μ := (canonical_coordinate_joint_mean (n+1) σ b k z hz hz0 hz1 hp r).1
  have he : (∫ p, C p ∂μ) = d*canonicalGaussianFreeValue σ k z r b := by
    simpa [d,C,μ,coordinateCascadeLaw] using (canonical_coordinate_joint_mean (n+1) σ b k z hz hz0 hz1 hp r).2
  have hni := normalizedCoordinateSphereLog_integrable n k σ z hz hz0 hz1 hp r
  have hbi : Integrable (fun p => (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b)) μ :=
    (((hi.const_mul (1+ε)).div_const d).sub (integrable_const _)).add (integrable_const _)
  have hlo : ∀ᵐ p ∂μ, normalizedCoordinateSphereLog n k σ p ≤
      (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b) := by
    filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
      canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
    have hraw := canonicalCoordinate_unitSphere_upper n k σ hb hε hε1 _ h0 hc hm
    have hh := div_le_div_of_nonneg_right hraw hd.le
    have heq : ((1+ε)*C p-M+ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b))/d =
        (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b) := by
      dsimp only [d]
      push_cast
      field_simp
    change coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => p.1 i),p.2)/d ≤
      ((1+ε)*C p-M+ε*((n+1:ℕ):ℝ)*(Real.log b/2+2*b))/d at hh
    rw [heq] at hh
    simpa only [normalizedCoordinateSphereLog,d,Nat.cast_add,Nat.cast_one] using hh
  have hh := integral_mono_ae hni hbi hlo
  have hcalc : (∫ p, (1+ε)*C p/d-M/d+ε*(Real.log b/2+2*b) ∂μ) =
      (1+ε)*canonicalGaussianFreeValue σ k z r b-M/d+ε*(Real.log b/2+2*b) := by
    rw [integral_add (f := fun p => (1+ε)*C p/d-M/d)
      (g := fun _ => ε*(Real.log b/2+2*b))
      (((hi.const_mul (1+ε)).div_const d).sub (integrable_const (M/d)))
      (integrable_const (ε*(Real.log b/2+2*b))),
      integral_sub (f := fun p => (1+ε)*C p/d) (g := fun _ => M/d)
        ((hi.const_mul (1+ε)).div_const d) (integrable_const (M/d)),
      integral_div,integral_const_mul,he]
    simp only [integral_const,probReal_univ,one_smul]
    field_simp
  rw [hcalc] at hh
  simpa [expectedCoordinateSphereLog,M,d] using hh

lemma expectedCoordinateSphereLog_upper_eventually (k : ℕ) (σ : ℕ → ℝ) {b ε : ℝ}
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, expectedCoordinateSphereLog n k σ z r ≤
      canonicalGaussianFreeValue σ k z r b+(b-1)/2+
        ε*(canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2)+
          Real.log 2/((n+1:ℕ):ℝ) := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  filter_upwards [canonicalRadial_band_eventually_half hε hε1] with n hn
  have hm := (canonicalRadial_band_mass_bounds n hb hn).1
  have hmp : 0 < (canonicalRadialMass n b).real (normSquareBand n ε) :=
    (by positivity : 0 < Real.exp (((n+1:ℕ):ℝ)*((1-b)/2-|1-b| * ε/2))/2).trans_le hm
  have hu := expectedCoordinateSphereLog_upper n k σ z hz hz0 hz1 hp r hε.le hε1.le hmp
  have hl := (canonicalRadial_band_log_bounds n hb hn).1
  linarith

lemma normalizedCoordinateSphereLog_lower_probability (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2)
    {ε a : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (ha : a < canonicalGaussianFreeValue σ k z r b+(b-1)/2-
      ε*(canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2)) :
    Tendsto (fun n : ℕ => (coordinateCascadeLaw (n+1) k z r).real
      {p | a ≤ normalizedCoordinateSphereLog n k σ p}) atTop (𝓝 1) := by
  let C := canonicalGaussianFreeValue σ k z r b
  let K := Real.log b/2+2*b
  let L := C+(b-1)/2-ε*(C+K+|1-b|/2)
  let δ := L-a
  have hδ : 0 < δ := by
    apply sub_pos.mpr
    simpa [L,C,K,add_assoc] using ha
  let μ := fun n => coordinateCascadeLaw (n+1) k z r
  let F := fun n (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) =>
    canonicalCoordinateLog (n+1) k σ b ((fun i _ => p.1 i),p.2)
  let B := fun n => {p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k |
    (canonicalCoordinateBandTotalE n k σ b ε ((fun i _ => p.1 i),p.2)).toReal <
      decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (canonicalCoordinatePotential (n+1) b) k ((fun i _ => p.1 i),p.2)/2}
  let D := fun n => {p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k |
    (δ/2)*((n+1:ℕ):ℝ) ≤ |F n p-((n+1:ℕ):ℝ)*C|}
  have hB : Tendsto (fun n => μ n (B n)) atTop (𝓝 0) :=
    canonicalCoordinate_bad_half_band_tendsto_zero k σ z hz hz0 hz1 r b hp hstat hε
  have hD : Tendsto (fun n => μ n (D n)) atTop (𝓝 0) :=
    (canonical_coordinate_converges σ b k z hz hz0 hz1 hp r (half_pos hδ)).comp
      (tendsto_add_atTop_nat 1)
  have hsum := hB.add hD
  simp only [add_zero] at hsum
  have ht : Tendsto (fun n : ℕ => Real.log 2/((n+1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hev : ∀ᶠ n : ℕ in atTop, Real.log 2/((n+1:ℕ):ℝ) < δ/2 :=
    ht.eventually (gt_mem_nhds (half_pos hδ))
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hbad : Tendsto (fun n => μ n {p | normalizedCoordinateSphereLog n k σ p < a}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hev,canonicalRadial_band_eventually_half hε hε1] with n hn hhalf
    apply le_trans (measure_mono_ae (t := B n ∪ D n) ?_) (measure_union_le _ _)
    filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
      canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
    intro hbad
    by_cases hpB : p ∈ B n
    · exact Or.inl hpB
    · right
      by_contra hpD
      have hm := (canonicalRadial_band_mass_bounds n hb hhalf).1
      have hmp : 0 < (canonicalRadialMass n b).real (normSquareBand n ε) :=
        (by positivity : 0 < Real.exp (((n+1:ℕ):ℝ)*((1-b)/2-|1-b| * ε/2))/2).trans_le hm
      have hu := (canonicalRadial_band_log_bounds n hb hhalf).2
      have hraw := canonicalCoordinate_unitSphere_lower n k σ hb hε.le hε1.le _ h0 hc hmp
        (le_of_not_gt hpB)
      have hd : 0 < ((n+1:ℕ):ℝ) := by positivity
      have hlow := (div_le_div_of_nonneg_right hraw hd.le)
      have herr : |F n p-((n+1:ℕ):ℝ)*C| < (δ/2)*((n+1:ℕ):ℝ) := not_le.mp hpD
      have herr' : C-δ/2 < F n p/((n+1:ℕ):ℝ) := by
        apply (lt_div_iff₀ hd).mpr
        have hh := (abs_lt.mp herr).1
        nlinarith
      have he : ((1-ε)*F n p-Real.log 2-
          Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))-
          ε*((n+1:ℕ):ℝ)*K)/((n+1:ℕ):ℝ) =
          (1-ε)*(F n p/((n+1:ℕ):ℝ))-Real.log 2/((n+1:ℕ):ℝ)-
          Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1:ℕ):ℝ)-ε*K := by
        field_simp
      change ((1-ε)*F n p-Real.log 2-
          Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))-
          ε*((n+1:ℕ):ℝ)*K)/((n+1:ℕ):ℝ) ≤ normalizedCoordinateSphereLog n k σ p at hlow
      rw [he] at hlow
      have hmule := mul_lt_mul_of_pos_left herr' (sub_pos.mpr hε1)
      have haeq : a = L-δ := by dsimp [δ]; ring
      change normalizedCoordinateSphereLog n k σ p < a at hbad
      dsimp only [L] at haeq
      nlinarith [mul_nonneg hε.le hδ.le]
  have hreal : Tendsto (fun n => (μ n).real {p | normalizedCoordinateSphereLog n k σ p < a}) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp hbad
  have hone : Tendsto (fun n => 1-(μ n).real {p | normalizedCoordinateSphereLog n k σ p < a}) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hreal
  convert hone using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  have hmeas : MeasurableSet {p | normalizedCoordinateSphereLog n k σ p < a} :=
    measurableSet_lt (normalizedCoordinateSphereLog_measurable n k σ) measurable_const
  rw [← probReal_compl_eq_one_sub hmeas]
  congr 1
  ext p
  simp only [mem_compl_iff,mem_ofPred_eq,not_lt]

lemma expectedCoordinateSphereLog_lower_eventually (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ a : ℝ, a < canonicalGaussianFreeValue σ k z r b+(b-1)/2-
      ε*(canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2) →
    ∀ᶠ n : ℕ in atTop, a < expectedCoordinateSphereLog n k σ z r := by
  apply expected_eventually_gt_of_probability_lower
    (fun n => coordinateCascadeLaw (n+1) k z r) (fun n => normalizedCoordinateSphereLog n k σ)
    (fun n => normalizedCoordinateSphereLog_integrable n k σ z hz hz0 hz1 hp r)
    (fun n => normalizedCoordinateSphereLog_nonneg n k σ z hz hz0 hz1 hp r)
  exact fun a ha => normalizedCoordinateSphereLog_lower_probability k σ z hz hz0 hz1 r b hp hstat hε hε1 ha

theorem expectedCoordinateSphereLog_tendsto (k : ℕ) (σ : ℕ → ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r : ℝ≥0) (b : ℝ) (hp : 0 < quadraticCascadePrecision σ b k z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b k z-
      (r:ℝ)/(2*(quadraticCascadePrecision σ b k z)^2) = -1/2) :
    Tendsto (fun n : ℕ => expectedCoordinateSphereLog n k σ z r) atTop
      (𝓝 (canonicalGaussianFreeValue σ k z r b+(b-1)/2)) := by
  let T := canonicalGaussianFreeValue σ k z r b+(b-1)/2
  let A := canonicalGaussianFreeValue σ k z r b+Real.log b/2+2*b+|1-b|/2
  let e := fun j : ℕ => 1/((j+1:ℕ):ℝ)
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have he0 : ∀ j, 0 < e j := by intro j; dsimp [e]; positivity
  have he1 : ∀ᶠ j in atTop, e j < 1 := he.eventually (gt_mem_nhds zero_lt_one)
  have hl : Tendsto (fun j => T-e j*A) atTop (𝓝 T) := by
    simpa using tendsto_const_nhds.sub (he.mul_const A)
  have hu : Tendsto (fun j => T+e j*A) atTop (𝓝 T) := by
    simpa using tendsto_const_nhds.add (he.mul_const A)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨j,hj1,hja⟩ := (he1.and (hl.eventually (lt_mem_nhds ha))).exists
    exact expectedCoordinateSphereLog_lower_eventually k σ z hz hz0 hz1 r b hp hstat (he0 j) hj1 a hja
  · intro a ha
    obtain ⟨j,hj1,hja⟩ := (he1.and (hu.eventually (gt_mem_nhds ha))).exists
    have ht : Tendsto (fun n : ℕ => T+e j*A+Real.log 2/((n+1:ℕ):ℝ)) atTop (𝓝 (T+e j*A)) := by
      have hh : Tendsto (fun n : ℕ => Real.log 2/((n+1:ℕ):ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      simpa using tendsto_const_nhds.add hh
    filter_upwards [expectedCoordinateSphereLog_upper_eventually k σ z hz hz0 hz1 hp r (he0 j) hj1,
      ht.eventually (gt_mem_nhds hja)] with n hn hn'
    exact hn.trans_lt hn'

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AmplitudeConvex
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sphericalExp_field_holder (n : ℕ) (u v : Spin (n+1)) (R : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ENNReal.ofReal (sphericalExp n (a • u+b • v) R) ≤
      ENNReal.ofReal (sphericalExp n u R)^a * ENNReal.ofReal (sphericalExp n v R)^b := by
  have he (z : Spin (n+1)) : ENNReal.ofReal (sphericalExp n z R) =
      ∫⁻ x : Metric.sphere (0 : Spin (n+1)) 1,
        ENNReal.ofReal (Real.exp (R*inner ℝ z x.val)) ∂unitSphereLaw (n+1) :=
    ofReal_integral_eq_lintegral_ofReal
      (unitSphere_continuous_integrable (by fun_prop))
      (ae_of_all _ fun _ => (Real.exp_pos _).le)
  simp_rw [he]
  have h (x : Metric.sphere (0 : Spin (n+1)) 1) :
      ENNReal.ofReal (Real.exp (R*inner ℝ (a • u+b • v) x.val)) =
        ENNReal.ofReal (Real.exp (R*inner ℝ u x.val))^a *
          ENNReal.ofReal (Real.exp (R*inner ℝ v x.val))^b := by
    simp only [inner_add_left,real_inner_smul_left]
    rw [show R*(a*inner ℝ u x.val+b*inner ℝ v x.val)=
      a*(R*inner ℝ u x.val)+b*(R*inner ℝ v x.val) by ring]
    exact ofReal_exp_affine _ _ _ _
  simp_rw [h]
  exact ENNReal.lintegral_mul_norm_pow_le (by fun_prop) (by fun_prop) ha hb hab

lemma decoratedLeafIntegral_mixed_holder {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [AddCommMonoid X] [Module ℝ X]
    (s₁ s₂ s₃ : X × S → X) (hs₁ : Measurable s₁) (hs₂ : Measurable s₂)
    (F : X → ℝ≥0∞) (hF : Measurable F) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hstep : ∀ x y t, s₃ (a • x+b • y,t)=a • s₁ (x,t)+b • s₂ (y,t))
    (hconv : ∀ x y, F (a • x+b • y) ≤ F x^a*F y^b)
    (k : ℕ) (η : DecoratedCascade S k) (x y : X) :
    decoratedLeafIntegral s₃ F k (a • x+b • y,η) ≤
      decoratedLeafIntegral s₁ F k (x,η)^a*decoratedLeafIntegral s₂ F k (y,η)^b := by
  induction k generalizing x y with
  | zero => exact hconv x y
  | succ k ih =>
    have hm (s : X × S → X) (hs : Measurable s) (x : X) :
        Measurable (fun q : ℝ × (S × DecoratedCascade S k) =>
          ENNReal.ofReal (Real.exp q.1)*decoratedLeafIntegral s F k (s (x,q.2.1),q.2.2)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_measurable s hs F hF k).comp
          ((hs.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
    simp only [decoratedLeafIntegral,hstep]
    refine le_trans (lintegral_mono fun q => mul_le_mul_right (ih q.2.2 (s₁ (x,q.2.1)) (s₂ (y,q.2.1))) _) ?_
    calc
      _ = ∫⁻ q : ℝ × (S × DecoratedCascade S k),
          (ENNReal.ofReal (Real.exp q.1)*decoratedLeafIntegral s₁ F k (s₁ (x,q.2.1),q.2.2))^a *
          (ENNReal.ofReal (Real.exp q.1)*decoratedLeafIntegral s₂ F k (s₂ (y,q.2.1),q.2.2))^b
            ∂markedStableCountKernel η := by
        congr 1
        funext q
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha,ENNReal.mul_rpow_of_nonneg _ _ hb]
        have he : ENNReal.ofReal (Real.exp q.1)^a*ENNReal.ofReal (Real.exp q.1)^b =
            ENNReal.ofReal (Real.exp q.1) := by
          rw [← ENNReal.rpow_add _ _ (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top,hab,ENNReal.rpow_one]
        calc
          _ = (ENNReal.ofReal (Real.exp q.1)^a*ENNReal.ofReal (Real.exp q.1)^b)*
              (decoratedLeafIntegral s₁ F k (s₁ (x,q.2.1),q.2.2)^a*
                decoratedLeafIntegral s₂ F k (s₂ (y,q.2.1),q.2.2)^b) := by rw [he]
          _ = _ := by ring
      _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le (hm s₁ hs₁ x).aemeasurable
        (hm s₂ hs₂ y).aemeasurable ha hb hab

lemma canonicalCoordinateStep_affine (d : ℕ) (σ τ : ℕ → ℝ) (x y : Fin d → ℕ → ℝ)
    (t : Fin d → ℝ) (a b : ℝ) :
    canonicalCoordinateStep d (a • σ+b • τ) (a • x+b • y,t) =
      a • canonicalCoordinateStep d σ (x,t)+b • canonicalCoordinateStep d τ (y,t) := by
  funext i j
  simp only [canonicalCoordinateStep,gaussianShiftStep,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma coordinateLeafField_affine (d : ℕ) (x y : Fin d → ℕ → ℝ) (a b : ℝ) :
    coordinateLeafField d (a • x+b • y)=a • coordinateLeafField d x+b • coordinateLeafField d y := by
  ext i
  simp [coordinateLeafField]

lemma coordinateAngularFactor_amplitude_holder (n k : ℕ) (σ τ : ℕ → ℝ)
    (x y : Fin (n+1) → ℕ → ℝ) (η : DecoratedCascade (Fin (n+1) → ℝ) k)
    (R : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) (a • σ+b • τ))
      (coordinateLeafField (n+1)) k (a • x+b • y,η) R ≤
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k (x,η) R ^ a *
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) τ)
      (coordinateLeafField (n+1)) k (y,η) R ^ b := by
  simp_rw [decoratedAngularFactor_eq n _ (canonicalCoordinateStep_measurable _ _)
    _ (coordinateLeafField_measurable _) ]
  apply decoratedLeafIntegral_mixed_holder _ _ _ (canonicalCoordinateStep_measurable _ _)
    (canonicalCoordinateStep_measurable _ _)
    (fun x => ENNReal.ofReal (sphericalExp n (coordinateLeafField (n+1) x) R))
    ?_ ha hb hab (fun x y t => canonicalCoordinateStep_affine _ _ _ x y t a b)
  · intro x y
    rw [coordinateLeafField_affine]
    exact sphericalExp_field_holder n _ _ R ha hb hab
  · have hm := coordinateLeafField_measurable (n+1)
    unfold sphericalExp
    apply ENNReal.measurable_ofReal.comp
    exact (show StronglyMeasurable (fun p : (Fin (n+1) → ℕ → ℝ) ×
        Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (R*inner ℝ (coordinateLeafField (n+1) p.1) (p.2:Spin (n+1)))) from (by fun_prop)).integral_prod_right'.measurable

lemma decoratedLeafIntegral_constant_step {X Y S : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace S] (s : X × S → X) (t : Y × S → Y)
    (c : ℝ≥0∞) (k : ℕ) (η : DecoratedCascade S k) (x : X) (y : Y) :
    decoratedLeafIntegral s (fun _ => c) k (x,η)=
      decoratedLeafIntegral t (fun _ => c) k (y,η) := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [decoratedLeafIntegral]
    congr 1
    funext q
    rw [ih q.2.2 (s (x,q.2.1)) (t (y,q.2.1))]

lemma decoratedTerminalTotal_zero_step {X Y S : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace S] (s : X × S → X) (t : Y × S → Y)
    (k : ℕ) (η : DecoratedCascade S k) (x : X) (y : Y) :
    decoratedTerminalTotal s (fun _ => 0) k (x,η)=
      decoratedTerminalTotal t (fun _ => 0) k (y,η) := by
  unfold decoratedTerminalTotal
  rw [← decoratedLeafIntegral_exp,← decoratedLeafIntegral_exp]
  exact congrArg ENNReal.toReal (decoratedLeafIntegral_constant_step s t _ k η x y)

lemma quadraticCascadePrecision_add (σ : ℕ → ℝ) (b c : ℝ) (k : ℕ) (z : Fin k → ℝ) :
    quadraticCascadePrecision σ (b+c) k z=quadraticCascadePrecision σ b k z+c := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [quadraticCascadePrecision,ih]; ring

lemma exists_positive_canonical_precision (σ : ℕ → ℝ) (k : ℕ) (z : Fin k → ℝ) :
    ∃ b : ℝ, 0 < quadraticCascadePrecision σ b k z := by
  refine ⟨0+(1-quadraticCascadePrecision σ 0 k z),?_⟩
  rw [quadraticCascadePrecision_add]
  linarith

lemma coordinateAngularLog_amplitude_convex (n k : ℕ) (σ τ : ℕ → ℝ)
    (x y : Fin (n+1) → ℕ → ℝ) (η : DecoratedCascade (Fin (n+1) → ℝ) k)
    (R : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k (x,η))
    (hσ : 0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k (x,η) R).toReal)
    (hτ : 0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) τ)
      (coordinateLeafField (n+1)) k (y,η) R).toReal)
    (hm : 0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) (a • σ+b • τ))
      (coordinateLeafField (n+1)) k (a • x+b • y,η) R).toReal) :
    coordinateAngularLog n k (a • σ+b • τ) R (a • x+b • y,η) ≤
      a*coordinateAngularLog n k σ R (x,η)+b*coordinateAngularLog n k τ R (y,η) := by
  have H := coordinateAngularFactor_amplitude_holder n k σ τ x y η R ha hb hab
  have H' := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ha (ENNReal.toReal_pos_iff.mp hσ).2.ne)
    (ENNReal.rpow_ne_top_of_nonneg hb (ENNReal.toReal_pos_iff.mp hτ).2.ne)) H
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at H'
  have Hlog := Real.log_le_log hm H'
  rw [Real.log_mul (Real.rpow_pos_of_pos hσ a).ne' (Real.rpow_pos_of_pos hτ b).ne',
    Real.log_rpow hσ,Real.log_rpow hτ] at Hlog
  have he₁ := decoratedTerminalTotal_zero_step (canonicalCoordinateStep (n+1) (a • σ+b • τ))
    (canonicalCoordinateStep (n+1) σ) k η (a • x+b • y) x
  have he₂ := decoratedTerminalTotal_zero_step (canonicalCoordinateStep (n+1) τ)
    (canonicalCoordinateStep (n+1) σ) k η y x
  unfold coordinateAngularLog
  rw [he₁,he₂,Real.log_div hm.ne' h0.ne',Real.log_div hσ.ne' h0.ne',Real.log_div hτ.ne' h0.ne']
  have hh := congrArg (fun t : ℝ => t*Real.log (decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k (x,η))) hab
  nlinarith

lemma coordinateRootScale_preserving (d k : ℕ) (z : Fin k → ℝ) (r : ℝ) :
    MeasurePreserving (coordinateRootScale d k r) (coordinateCascadeLaw d k z 1)
      (coordinateCascadeLaw d k z ⟨r^2,sq_nonneg r⟩) := by
  have hp : MeasurePreserving (fun x : Fin d → ℝ => fun i => r*x i)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨r^2,sq_nonneg r⟩)) := by
    refine ⟨by fun_prop,?_⟩
    erw [Measure.pi_map_pi (fun _ => (measurable_id.const_mul r).aemeasurable)]
    congr 1
    funext i
    change (gaussianReal 0 1).map (fun x : ℝ => r*x)=gaussianReal 0 ⟨r^2,sq_nonneg r⟩
    rw [gaussianReal_map_const_mul,mul_zero,mul_one]
    rfl
  exact hp.prod (MeasurePreserving.id _)

lemma amplitudeSphereLog_integrable (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    Integrable (amplitudeSphereLog n k σ r) (coordinateCascadeLaw (n+1) k z 1) := by
  obtain ⟨b,hb⟩ := exists_positive_canonical_precision σ k z
  have hi := normalizedCoordinateSphereLog_integrable n k σ z hz hz0 hz1 hb ⟨r^2,sq_nonneg r⟩
  exact ((coordinateRootScale_preserving (n+1) k z r).integrable_comp hi.aestronglyMeasurable).mpr hi

lemma amplitudeSphereValue_eq (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ) (r : ℝ) :
    amplitudeSphereValue n k σ z r=
      expectedCoordinateSphereLog n k σ z ⟨r^2,sq_nonneg r⟩ := by
  have hp := coordinateRootScale_preserving (n+1) k z r
  have he := integral_map (μ := coordinateCascadeLaw (n+1) k z 1) hp.measurable.aemeasurable
    ((normalizedCoordinateSphereLog_measurable n k σ).aestronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm

lemma amplitudeSphereLog_nonneg (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    0 ≤ᵐ[coordinateCascadeLaw (n+1) k z 1] amplitudeSphereLog n k σ r := by
  obtain ⟨b,hb⟩ := exists_positive_canonical_precision σ k z
  exact (coordinateRootScale_preserving (n+1) k z r).quasiMeasurePreserving.ae
    (normalizedCoordinateSphereLog_nonneg n k σ z hz hz0 hz1 hb ⟨r^2,sq_nonneg r⟩)

lemma amplitudeSphereLog_regular (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    ∀ᵐ p ∂coordinateCascadeLaw (n+1) k z 1,
      0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0)
        k ((fun i _ => r*p.1 i),p.2) ∧
      0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
        (coordinateLeafField (n+1)) k ((fun i _ => r*p.1 i),p.2) (Real.sqrt (n+1:ℕ))).toReal := by
  obtain ⟨b,hb⟩ := exists_positive_canonical_precision σ k z
  have hb0 : 0 < b := hb.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have he : ∀ᵐ p ∂coordinateCascadeLaw (n+1) k z ⟨r^2,sq_nonneg r⟩,
      0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0)
        k ((fun i _ => p.1 i),p.2) ∧
      0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
        (coordinateLeafField (n+1)) k ((fun i _ => p.1 i),p.2) (Real.sqrt (n+1:ℕ))).toReal := by
    filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 ⟨r^2,sq_nonneg r⟩,
      canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hb ⟨r^2,sq_nonneg r⟩] with p h0 hc
    exact ⟨h0,(coordinateAngularLog_regular n k σ _ hb0 _ h0 hc).1⟩
  exact (coordinateRootScale_preserving (n+1) k z r).quasiMeasurePreserving.ae he

lemma amplitudeSphereValue_convex (n k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (σ τ : ℕ → ℝ) (r s : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    amplitudeSphereValue n k (a • σ+b • τ) z (a*r+b*s) ≤
      a*amplitudeSphereValue n k σ z r+b*amplitudeSphereValue n k τ z s := by
  have hi := amplitudeSphereLog_integrable n k (a • σ+b • τ) z hz hz0 hz1 (a*r+b*s)
  have hσ := amplitudeSphereLog_integrable n k σ z hz hz0 hz1 r
  have hτ := amplitudeSphereLog_integrable n k τ z hz hz0 hz1 s
  have he (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
      (fun (i : Fin (n+1)) (_ : ℕ) => (a*r+b*s)*p.1 i)=
        a • (fun (i : Fin (n+1)) (_ : ℕ) => r*p.1 i)+b • (fun (i : Fin (n+1)) (_ : ℕ) => s*p.1 i) := by
    funext i j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hle : amplitudeSphereLog n k (a • σ+b • τ) (a*r+b*s) ≤ᵐ[coordinateCascadeLaw (n+1) k z 1]
      (fun p => a*amplitudeSphereLog n k σ r p+b*amplitudeSphereLog n k τ s p) := by
    filter_upwards [amplitudeSphereLog_regular n k σ z hz hz0 hz1 r,
      amplitudeSphereLog_regular n k τ z hz hz0 hz1 s,
      amplitudeSphereLog_regular n k (a • σ+b • τ) z hz hz0 hz1 (a*r+b*s)] with p h1 h2 h3
    rw [he p] at h3
    have h := coordinateAngularLog_amplitude_convex n k σ τ _ _ p.2 _ ha hb hab h1.1 h1.2 h2.2 h3.2
    unfold amplitudeSphereLog
    rw [he p]
    calc
      _ ≤ (a*coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => r*p.1 i),p.2)+
          b*coordinateAngularLog n k τ (Real.sqrt (n+1:ℕ)) ((fun i _ => s*p.1 i),p.2))/(n+1:ℕ) :=
        div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by ring
  have hh := integral_mono_ae hi ((hσ.const_mul a).add (hτ.const_mul b)) hle
  change (∫ p, amplitudeSphereLog n k (a • σ+b • τ) (a*r+b*s) p ∂coordinateCascadeLaw (n+1) k z 1) ≤
    ∫ p, a*amplitudeSphereLog n k σ r p+b*amplitudeSphereLog n k τ s p ∂coordinateCascadeLaw (n+1) k z 1 at hh
  rw [integral_add (hσ.const_mul a) (hτ.const_mul b),integral_const_mul,integral_const_mul] at hh
  exact hh

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGFiniteCode
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma scaledStdGaussian_conv (σ τ : ℝ) :
    (scaledStdGaussian (E := E) σ) ∗ (scaledStdGaussian τ)=
      scaledStdGaussian (Real.sqrt (σ^2+τ^2)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv]
  simp only [scaledStdGaussian,charFun_map_smul,charFun_stdGaussian]
  rw [← Complex.exp_add]
  congr 1
  have hr : -‖σ • t‖^2/2 + -‖τ • t‖^2/2 = -‖Real.sqrt (σ^2+τ^2) • t‖^2/2 := by
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      Real.sq_sqrt (add_nonneg (sq_nonneg σ) (sq_nonneg τ))]
    ring
  exact_mod_cast hr

lemma stdGaussian_integral_add {F : E → ℝ} (hF : Continuous F) (σ τ : ℝ)
    (hI : Integrable (fun y : E => F (Real.sqrt (σ^2+τ^2) • y)) (stdGaussian E)) :
    (∫ y, ∫ z, F (σ • y+τ • z) ∂stdGaussian E ∂stdGaussian E)=
      ∫ y, F (Real.sqrt (σ^2+τ^2) • y) ∂stdGaussian E := by
  have hi : Integrable F (scaledStdGaussian (E := E) (Real.sqrt (σ^2+τ^2))) := by
    exact (integrable_map_measure hF.aestronglyMeasurable (by fun_prop)).mpr hI
  rw [← scaledStdGaussian_conv σ τ] at hi
  have H := integral_conv hi
  rw [scaledStdGaussian_conv σ τ] at H
  simp only [scaledStdGaussian] at H
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable] at H
  have hm : StronglyMeasurable (fun y : E => ∫ z : E, F (y+z) ∂(stdGaussian E).map (τ • ·)) :=
    ((hF.comp (continuous_fst.add continuous_snd)).stronglyMeasurable).integral_prod_right'
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable] at H
  have HH : ∀ y : E, (∫ z, F (σ • y+z) ∂(stdGaussian E).map (τ • ·))=
      ∫ z, F (σ • y+τ • z) ∂stdGaussian E := by
    intro y
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [HH] at H
  exact H.symm

lemma gaussianEntropic_semigroup {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p : ℝ} (hp : 0 ≤ p) (σ τ : ℝ) (x : E) :
    gaussianEntropic (stdGaussian E) p σ (gaussianEntropic (stdGaussian E) p τ f) x=
      gaussianEntropic (stdGaussian E) p (Real.sqrt (σ^2+τ^2)) f x := by
  have hfc := hf.continuous
  have hinner := gaussianEntropic_lipschitz (stdGaussian E) hf (σ := τ) hp
  by_cases hp0 : p=0
  · subst p
    rw [gaussianEntropic_zero _ hinner,gaussianEntropic_zero _ hf]
    simp_rw [gaussianEntropic_zero _ hf]
    have H := stdGaussian_integral_add (F := fun y => f (x+y)) (by fun_prop) σ τ
      (gaussian_integrable_lipschitz (stdGaussian E) hf _ x)
    simpa only [add_assoc] using H
  · rw [gaussianEntropic_pos _ hinner hp0,gaussianEntropic_pos _ hf hp0]
    have he (y : E) : Real.exp (p*gaussianEntropic (stdGaussian E) p τ f (x+σ • y))=
        ∫ z, Real.exp (p*f (x+σ • y+τ • z)) ∂stdGaussian E := by
      rw [gaussianEntropic_pos _ hf hp0]
      rw [mul_div_cancel₀ _ hp0]
      apply Real.exp_log
      exact mgf_pos (gaussian_integrable_exp_lipschitz (stdGaussian E) hf p τ _)
    simp_rw [he]
    have H := stdGaussian_integral_add (F := fun y => Real.exp (p*f (x+y))) (by fun_prop) σ τ
      (gaussian_integrable_exp_lipschitz (stdGaussian E) hf p _ x)
    simpa only [add_assoc] using congrArg (fun a : ℝ => Real.log a/p) H

lemma gaussianEntropic_variance_zero {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (p : ℝ) (x : E) :
    gaussianEntropic (stdGaussian E) p 0 f x=f x := by
  by_cases hp : p=0
  · subst p
    simp [gaussianEntropic_zero _ hf]
  · rw [gaussianEntropic_pos _ hf hp]
    simp [hp]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBackward
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussianBackward_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (hl : ∀ a ∈ l, 0 ≤ a.1) :
    LipschitzWith L (gaussianBackward μ l f) := by
  induction l with
  | nil => exact hf
  | cons a l ih =>
    exact gaussianEntropic_lipschitz μ (ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)))
      (hl a (List.mem_cons_self))

lemma gaussianBackward_add_const {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (ℝ×ℝ)) (hl : ∀ a ∈ l, 0 ≤ a.1) (c : ℝ) :
    gaussianBackward μ l (fun x => f x+c)=(fun x => gaussianBackward μ l f x+c) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have htail := fun b hb => hl b (List.mem_cons_of_mem a hb)
    simp only [gaussianBackward,ih htail]
    funext x
    exact gaussianEntropic_add_const μ (gaussianBackward_lipschitz μ hf l htail) _ _ _ _

lemma gaussianBackward_append {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsGaussian μ] (l m : List (ℝ×ℝ)) (f : E → ℝ) :
    gaussianBackward μ (l++m) f=gaussianBackward μ l (gaussianBackward μ m f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append,gaussianBackward,ih]

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CascadeHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma cascadeHeatWord_nonneg (σ : ℕ → ℝ) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∀ c ∈ cascadeHeatWord σ k z, 0 ≤ c.1 := by
  induction k with
  | zero => simp [cascadeHeatWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma coordinateDepthField_step (d j : ℕ) (σ : ℕ → ℝ)
    (x : Fin d → ℕ → ℝ) (g : Fin d → ℝ) :
    coordinateDepthField d j (canonicalCoordinateStep d σ (x,g))=
      coordinateDepthField d (j+1) x+σ j • WithLp.toLp 2 g := by
  rfl

lemma integral_pi_standardGaussian (d : ℕ) {F : Spin d → ℝ} (hF : Continuous F) :
    (∫ g, F (WithLp.toLp 2 g) ∂(piMarkLaw (fun _ : Fin d => standardGaussianMark) : Measure (Fin d → ℝ)))=
      ∫ y, F y ∂stdGaussian (Spin d) := by
  rw [← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable]
  rfl

lemma integrable_pi_standardGaussian (d : ℕ) {F : Spin d → ℝ} (hF : Continuous F)
    (hI : Integrable F (stdGaussian (Spin d))) :
    Integrable (fun g => F (WithLp.toLp 2 g))
      (piMarkLaw (fun _ : Fin d => standardGaussianMark)) := by
  rw [← map_pi_eq_stdGaussian] at hI
  exact (integrable_map_measure hF.aestronglyMeasurable (by fun_prop)).mp hI

lemma coordinateRecursion_eq_backward (d : ℕ) (σ : ℕ → ℝ)
    {f : Spin d → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) k z (fun x => f (coordinateLeafField d x)) x=
        gaussianBackward (stdGaussian (Spin d)) (cascadeHeatWord σ k z) f (coordinateDepthField d k x)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (canonicalCoordinateStep d σ) (fun x => f (coordinateLeafField d x)) k z := by
  induction k with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ k ih =>
    have H := ih (fun i => z i.succ) (fun i => hz i.succ)
    have hl := gaussianBackward_lipschitz (stdGaussian (Spin d)) hf
      (cascadeHeatWord σ k (fun i => z i.succ))
      (cascadeHeatWord_nonneg σ k _ (fun i => (hz i.succ).le))
    let g := gaussianBackward (stdGaussian (Spin d)) (cascadeHeatWord σ k (fun i => z i.succ)) f
    have hg : LipschitzWith L g := hl
    have hcont (x : Fin d → ℕ → ℝ) : Continuous (fun y : Spin d =>
        Real.exp (z 0*g (coordinateDepthField d (k+1) x+σ k • y))) := by
      exact Real.continuous_exp.comp (continuous_const.mul (hg.continuous.comp
        (continuous_const.add (continuous_id.const_smul (σ k)))))
    constructor
    · intro x
      simp only [finiteCascadeLogRecursion,fractionalLogMoment,H.1,coordinateDepthField_step,
        cascadeHeatWord,gaussianBackward]
      rw [gaussianEntropic_pos _ hg (hz 0).ne']
      exact congrArg (fun t : ℝ => Real.log t / z 0) (integral_pi_standardGaussian d (hcont x))
    · constructor
      · intro x
        simp only [H.1,coordinateDepthField_step]
        exact integrable_pi_standardGaussian d (hcont x)
          (gaussian_integrable_exp_lipschitz (stdGaussian (Spin d)) hg (z 0) (σ k)
            (coordinateDepthField d (k+1) x))
      · exact H.2

lemma decoratedAngularFactor_eq_terminal_log (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k p R).toReal=
      decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ)
        (fun x => logSphericalExp n R (coordinateLeafField (n+1) x)) k p := by
  rw [decoratedAngularFactor_eq n _ (canonicalCoordinateStep_measurable (n+1) σ) _
    (coordinateLeafField_measurable (n+1))]
  unfold decoratedTerminalTotal
  rw [← decoratedLeafIntegral_exp]
  congr 2
  funext x
  rw [logSphericalExp,Real.exp_log (lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n _ R))]

lemma coordinateAngularLog_conditional_expectation (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (x : Fin (n+1) → ℕ → ℝ) :
    (∫ η, coordinateAngularLog n k σ R (x,η)
      ∂decoratedCascadeLaw (piMarkLaw (fun _ : Fin (n+1) => standardGaussianMark)) k z)=
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n R) (coordinateDepthField (n+1) k x) := by
  have H := coordinateRecursion_eq_backward (n+1) σ (logSphericalExp_lipschitz n R) k z hz0
  simp only [coordinateAngularLog,decoratedAngularFactor_eq_terminal_log]
  exact (finiteCascade_terminal_log_recursion_of_fractional _ _
    (canonicalCoordinateStep_measurable (n+1) σ) k z hz hz0 hz1
    ((logSphericalExp_lipschitz n R).continuous.measurable.comp
      (coordinateLeafField_measurable (n+1))) H.2 x).trans (H.1 x)

lemma amplitudeSphereValue_eq_backward (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    amplitudeSphereValue n k σ z r=
      gaussianBackward (stdGaussian (Spin (n+1))) ((0,r)::cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) 0/(n+1:ℕ) := by
  have hl := gaussianBackward_lipschitz (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) (cascadeHeatWord σ k z)
    (cascadeHeatWord_nonneg σ k z (fun i => (hz0 i).le))
  unfold amplitudeSphereValue coordinateCascadeLaw
  rw [integral_prod _ (amplitudeSphereLog_integrable n k σ z hz hz0 hz1 r)]
  simp only [amplitudeSphereLog,integral_div,coordinateAngularLog_conditional_expectation n k σ
    (Real.sqrt (n+1:ℕ)) z hz hz0 hz1]
  rw [gaussianBackward,gaussianEntropic_zero _ hl]
  simp only [zero_add]
  congr 1
  exact integral_pi_standardGaussian (n+1) (hl.continuous.comp (continuous_id.const_smul r))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepStationary
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

lemma quadraticCascadePrecision_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    quadraticCascadePrecision σ (D (Fin.last k))⁻¹ k z = (D 0)⁻¹ := by
  induction k with
  | zero => simp [quadraticCascadePrecision,Fin.fin_one_eq_zero]
  | succ k ih =>
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun i => hD i.succ) (fun i => hgap i.succ) (fun i => by
        have hs := hσ i.succ
        have he : k+1-1-(i.succ).val=k-1-i.val := by simp only [Fin.val_succ]; omega
        simpa only [he,Fin.castSucc_succ] using hs)
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht
    have hs := hσ 0
    simp only [Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero,Fin.castSucc_zero,Fin.succ_zero_eq_one] at hs
    have hg := hgap 0
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one] at hg
    dsimp only [quadraticCascadePrecision]
    rw [ht,hs]
    have h0 := (hD 0).ne'
    have h1 := (hD 1).ne'
    field_simp
    nlinarith

lemma quadraticCascadeReciprocalSlope_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i) (hz : ∀ i, 0 < z i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    quadraticCascadeReciprocalSlope σ (D (Fin.last k))⁻¹ k z = -(q (Fin.last k)-q 0)/2 := by
  induction k with
  | zero => simp [quadraticCascadeReciprocalSlope,Fin.fin_one_eq_zero]
  | succ k ih =>
    have hst : ∀ i : Fin k, (σ (k-1-i.val))^2 =
        (q i.succ.succ-q i.castSucc.succ)/(D i.castSucc.succ*D i.succ.succ) := by
      intro i
      have hs := hσ i.succ
      have he : k+1-1-(i.succ).val=k-1-i.val := by simp only [Fin.val_succ]; omega
      simpa only [he,Fin.castSucc_succ] using hs
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun i => hD i.succ) (fun i => hz i.succ) (fun i => hgap i.succ) hst
    have hp := quadraticCascadePrecision_stationary (k+1) σ q D z hD hgap hσ
    have hpt := quadraticCascadePrecision_stationary k σ (fun i => q i.succ)
      (fun i => D i.succ) (fun i => z i.succ) (fun i => hD i.succ) (fun i => hgap i.succ) hst
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht hpt
    have hg := hgap 0
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one] at hg
    rw [quadraticCascadeReciprocalSlope,ht,hp,hpt]
    simp only [one_div,inv_inv]
    have hz0 := (hz 0).ne'
    field_simp
    nlinarith

lemma quadraticCascadeOffset_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    quadraticCascadeOffset σ (D (Fin.last k))⁻¹ k z = stepLogRatios k D z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hst : ∀ i : Fin k, (σ (k-1-i.val))^2 =
        (q i.succ.succ-q i.castSucc.succ)/(D i.castSucc.succ*D i.succ.succ) := by
      intro i
      have hs := hσ i.succ
      have he : k+1-1-(i.succ).val=k-1-i.val := by simp only [Fin.val_succ]; omega
      simpa only [he,Fin.castSucc_succ] using hs
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun i => hD i.succ) (fun i => hgap i.succ) hst
    have hp := quadraticCascadePrecision_stationary (k+1) σ q D z hD hgap hσ
    have hpt := quadraticCascadePrecision_stationary k σ (fun i => q i.succ)
      (fun i => D i.succ) (fun i => z i.succ) (fun i => hD i.succ) (fun i => hgap i.succ) hst
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht hpt
    rw [quadraticCascadeOffset,ht,hp,hpt,stepLogRatios]
    simp only [Real.log_inv]
    ring

lemma canonicalGaussianFreeValue_stationary (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i)
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    canonicalGaussianFreeValue σ k z (q 0/(D 0)^2) (D (Fin.last k))⁻¹ =
      Real.log (D (Fin.last k))/2+stepLogRatios k D z+q 0/(2*D 0) := by
  rw [canonicalGaussianFreeValue,quadraticCascadePrecision_stationary k σ q D z hD hgap hσ,
    quadraticCascadeOffset_stationary k σ q D z hD hgap hσ,Real.log_inv]
  have h0 := (hD 0).ne'
  field_simp

lemma canonicalGaussianFreeValue_stationarity (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hD : ∀ i, 0 < D i) (hz : ∀ i, 0 < z i)
    (hend : D (Fin.last k)=1-q (Fin.last k))
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ)) :
    -1/(2*(D (Fin.last k))⁻¹)+quadraticCascadeReciprocalSlope σ (D (Fin.last k))⁻¹ k z-
      (q 0/(D 0)^2)/(2*(quadraticCascadePrecision σ (D (Fin.last k))⁻¹ k z)^2) = -1/2 := by
  rw [quadraticCascadePrecision_stationary k σ q D z hD hgap hσ,
    quadraticCascadeReciprocalSlope_stationary k σ q D z hD hz hgap hσ]
  have h0 := (hD 0).ne'
  have ht := (hD (Fin.last k)).ne'
  field_simp
  nlinarith

theorem expectedCoordinateSphereLog_stationary_data (k : ℕ) (σ : ℕ → ℝ)
    (q D : Fin (k+1) → ℝ) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (hD : ∀ i, 0 < D i)
    (hend : D (Fin.last k)=1-q (Fin.last k))
    (hgap : ∀ i : Fin k, D i.castSucc-D i.succ=z i*(q i.succ-q i.castSucc))
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=(q i.succ-q i.castSucc)/(D i.castSucc*D i.succ))
    (r : ℝ≥0) (hr : (r:ℝ)=q 0/(D 0)^2) :
    Tendsto (fun n : ℕ => expectedCoordinateSphereLog n k σ z r) atTop
      (𝓝 (Real.log (D (Fin.last k))/2+stepLogRatios k D z+q 0/(2*D 0)+
        ((D (Fin.last k))⁻¹-1)/2)) := by
  have hp : 0 < quadraticCascadePrecision σ (D (Fin.last k))⁻¹ k z := by
    rw [quadraticCascadePrecision_stationary k σ q D z hD hgap hσ]
    exact inv_pos.mpr (hD 0)
  have hstat := canonicalGaussianFreeValue_stationarity k σ q D z hD hz0 hend hgap hσ
  rw [← hr] at hstat
  have ht := expectedCoordinateSphereLog_tendsto k σ z hz hz0 hz1 r (D (Fin.last k))⁻¹ hp hstat
  rw [hr,canonicalGaussianFreeValue_stationary k σ q D z hD hgap hσ] at ht
  exact ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma timeTail_atom_integral (q t : Time) (w : ℝ) :
    (∫ s in Ici t, (if q ≤ s then w else 0) ∂timeLaw) = w*(1-max (q:ℝ) (t:ℝ)) := by
  change (∫ s in Ici t, (Ici q).indicator (fun _ => w) s ∂timeLaw) = _
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  rw [Ici_inter_Ici]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,timeLaw_eq_volume,
    unitInterval.volume_Ici,ENNReal.toReal_ofReal (sub_nonneg.mpr (max q t).2.2),smul_eq_mul]
  rcases le_total q t with h | h
  · rw [max_eq_right h,max_eq_right (show (q:ℝ) ≤ (t:ℝ) from h)]
    ring
  · rw [max_eq_left h,max_eq_left (show (t:ℝ) ≤ (q:ℝ) from h)]
    ring

lemma tailIntegral_weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : Time) :
    tailIntegral (weightedStepTrial w q hw hw1) t = ∑ i, w i*(1-max (q i:ℝ) (t:ℝ)) := by
  unfold tailIntegral
  change (∫ s in Ici t, ∑ i, if q i ≤ s then w i else 0 ∂timeLaw) = _
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => timeTail_atom_integral (q i) t (w i))
  · intro i _
    exact (integrable_const (w i)).indicator measurableSet_Ici

lemma weightedStepTail_continuous {I : Type*} [Fintype I] (w q : I → ℝ) :
    Continuous (weightedStepTail w q) := by
  unfold weightedStepTail
  fun_prop

lemma weightedStepTail_lower {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B t : ℝ}
    (hq : ∀ i, q i ≤ B) (ht : t ≤ B) :
    1-B ≤ weightedStepTail w q t := by
  calc
    1-B = ∑ i, w i*(1-B) := by rw [← Finset.sum_mul,hw1,one_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_left (max_le (hq i) ht) 1) (hw i)

lemma weightedStepTail_upper {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : ℝ) :
    weightedStepTail w q t ≤ 1-t := by
  calc
    _ ≤ ∑ i, w i*(1-t) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_left (le_max_right (q i) t) 1) (hw i)
    _ = _ := by rw [← Finset.sum_mul,hw1,one_mul]

lemma weightedStepTail_of_le {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw1 : ∑ i, w i = 1) {t : ℝ} (hq : ∀ i, q i ≤ t) :
    weightedStepTail w q t = 1-t := by
  simp only [weightedStepTail,max_eq_right (hq _)]
  rw [← Finset.sum_mul,hw1,one_mul]

lemma weightedStepTail_pos {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B t : ℝ}
    (hB : B < 1) (hq : ∀ i, q i ≤ B) (ht : t ≤ B) :
    0 < weightedStepTail w q t :=
  (sub_pos.mpr hB).trans_le (weightedStepTail_lower w q hw hw1 hq ht)

lemma weightedStepTail_inv_continuousOn {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B : ℝ}
    (hB : B < 1) (hq : ∀ i, q i ≤ B) :
    ContinuousOn (fun t => (weightedStepTail w q t)⁻¹) (Icc 0 B) :=
  (weightedStepTail_continuous w q).continuousOn.inv₀
    (fun _ ht => (weightedStepTail_pos w q hw hw1 hB hq ht.2).ne')

lemma integral_one_sub_inv {B : ℝ} (hB : B < 1) :
    (∫ t in (0:ℝ)..B, (1-t)⁻¹) = -Real.log (1-B) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
  simp only [sub_zero]
  rw [integral_inv_of_pos (sub_pos.mpr hB) zero_lt_one,one_div,Real.log_inv]

theorem entropy_weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i : ℝ) ≤ B) :
    entropy (weightedStepTrial w q hw hw1) = ENNReal.ofReal
      (((∫ t in (0:ℝ)..B, (weightedStepTail w (fun i => (q i:ℝ)) t)⁻¹)+Real.log (1-B))/2) := by
  let D := weightedStepTail w (fun i => (q i:ℝ))
  let F : ℝ → ℝ := fun t => (D t)⁻¹-(1-t)⁻¹
  have hD (t : ℝ) (ht : t ≤ B) : 0 < D t := weightedStepTail_pos _ _ hw hw1 hB1 hq ht
  have hF : ContinuousOn F (Icc 0 B) :=
    (weightedStepTail_inv_continuousOn _ _ hw hw1 hB1 hq).sub
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t ht => by
        have : t < 1 := ht.2.trans_lt hB1
        exact (sub_pos.mpr this).ne'))
  have hF0 : ∀ t ∈ Icc 0 B, 0 ≤ F t := by
    intro t ht
    exact sub_nonneg.mpr (inv_le_inv₀ (sub_pos.mpr (ht.2.trans_lt hB1)) (hD t ht.2) |>.mpr
      (weightedStepTail_upper _ _ hw hw1 t))
  have he (t : Time) : (ENNReal.ofReal (tailIntegral (weightedStepTrial w q hw hw1) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ = (Iic B).indicator (fun t => ENNReal.ofReal (F t)) (t:ℝ) := by
    rw [tailIntegral_weightedStepTrial]
    change (ENNReal.ofReal (D (t:ℝ)))⁻¹-_ = _
    by_cases ht : (t:ℝ) ≤ B
    · rw [Set.indicator_of_mem (show (t:ℝ) ∈ Iic B from ht)]
      dsimp [F]
      rw [ENNReal.ofReal_sub _ (inv_nonneg.mpr (sub_nonneg.mpr t.2.2)),
        ENNReal.ofReal_inv_of_pos (hD t ht),
        ENNReal.ofReal_inv_of_pos (sub_pos.mpr (ht.trans_lt hB1))]
    · rw [Set.indicator_of_notMem (show (t:ℝ) ∉ Iic B from ht)]
      have hd : D (t:ℝ) = 1-(t:ℝ) := weightedStepTail_of_le _ _ hw1
        (fun i => (hq i).trans (le_of_not_ge ht))
      rw [hd,tsub_self]
  have hset : Iic B ∩ Icc (0:ℝ) 1 = Icc 0 B := by
    ext t
    constructor
    · rintro ⟨ht,h0,h1⟩
      exact ⟨h0,ht⟩
    · rintro ⟨h0,ht⟩
      exact ⟨ht,h0,ht.trans hB1.le⟩
  have hel : (∫⁻ t : Time, (ENNReal.ofReal (tailIntegral (weightedStepTrial w q hw hw1) t))⁻¹-
      (ENNReal.ofReal (1-(t:ℝ)))⁻¹ ∂timeLaw) = ENNReal.ofReal (∫ t in Icc 0 B, F t) := by
    rw [lintegral_congr he]
    change (∫⁻ t : Icc (0:ℝ) 1, (Iic B).indicator (fun t => ENNReal.ofReal (F t)) t.val
      ∂Measure.comap Subtype.val volume) = _
    rw [lintegral_subtype_comap measurableSet_Icc,lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic,hset]
    exact (ofReal_integral_eq_lintegral_ofReal hF.integrableOn_Icc
      ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hF0 t ht))).symm
  have hInt : (∫ t in Icc 0 B, F t) = (∫ t in (0:ℝ)..B, (D t)⁻¹)+Real.log (1-B) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hB0]
    have hiD : IntervalIntegrable (fun t => (D t)⁻¹) volume 0 B :=
      (weightedStepTail_inv_continuousOn _ _ hw hw1 hB1 hq).intervalIntegrable_of_Icc hB0
    have hiR : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 B :=
      ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t (ht : t ∈ Icc (0:ℝ) B) =>
        (sub_pos.mpr (ht.2.trans_lt hB1)).ne')).intervalIntegrable_of_Icc hB0
    rw [show F = (fun t => (D t)⁻¹-(1-t)⁻¹) from rfl,
      intervalIntegral.integral_sub hiD hiR,integral_one_sub_inv hB1,sub_neg_eq_add]
  rw [entropy,hel,hInt,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num
  rfl

lemma weightedStepTail_affine {k : ℕ} (w q : Fin (k+1) → ℝ) (hq : Monotone q)
    (i : Fin k) {t : ℝ} (ht : t ∈ Icc (q i.castSucc) (q i.succ)) :
    weightedStepTail w q t = weightedStepTail w q (q i.castSucc)-
      stepCumulative w i*(t-q i.castSucc) := by
  unfold weightedStepTail stepCumulative
  rw [Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ≤ i.castSucc
  · rw [ite_eq_left hj,max_eq_right ((hq hj).trans ht.1),max_eq_right (hq hj)]
    ring
  · have hj' : i.succ ≤ j := by exact Fin.le_iff_val_le_val.mpr (by
      have hh := Fin.lt_def.mp (lt_of_not_ge hj)
      simp only [Fin.val_castSucc,Fin.val_succ] at *
      omega)
    rw [ite_eq_right hj,max_eq_left (ht.2.trans (hq hj')),max_eq_left
      ((hq (Fin.castSucc_le_succ i)).trans (hq hj'))]
    ring

lemma weightedStepTail_below_min {I : Type*} [Fintype I] (w q : I → ℝ)
    {a t : ℝ} (hq : ∀ i, a ≤ q i) (ht : t ≤ a) :
    weightedStepTail w q t = weightedStepTail w q a := by
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_left (ht.trans (hq i)),max_eq_left (hq i)]

lemma affine_pos_on {A B a b z : ℝ} (_hab : a ≤ b) (hB : 0 < B) (hz : 0 < z)
    (hrel : A-z*(b-a)=B) {x : ℝ} (hx : x ∈ Icc a b) : 0 < A-z*(x-a) := by
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hz.le
  linarith

lemma integral_positive_affine_inv {A B a b z : ℝ} (hab : a ≤ b) (_hA : 0 < A)
    (hB : 0 < B) (hz : 0 < z) (hrel : A-z*(b-a)=B) :
    (∫ x in a..b, (A-z*(x-a))⁻¹) = (Real.log A-Real.log B)/z := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun x => -(Real.log (A-z*(x-a)))/z) (A-z*(x-a))⁻¹ x := by
    have hd := (((hasDerivAt_id x).sub_const a).const_mul z).const_sub A
    have he := ((hd.log (affine_pos_on hab hB hz hrel hx).ne').neg).div_const z
    have hv : -(-(z*1)/(A-z*(id x-a)))/z = (A-z*(x-a))⁻¹ := by
      dsimp only [id_eq]
      field_simp [hz.ne',(affine_pos_on hab hB hz hrel hx).ne']
    rw [hv] at he
    exact he
  have hi : IntervalIntegrable (fun x => (A-z*(x-a))⁻¹) volume a b :=
    ((continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.inv₀
      (fun x hx => (affine_pos_on hab hB hz hrel hx).ne')).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx)) hi]
  rw [hrel]
  simp only [sub_self,mul_zero,sub_zero]
  ring

lemma integral_positive_affine_inv_sq {A B a b z : ℝ} (hab : a ≤ b) (hA : 0 < A)
    (hB : 0 < B) (hz : 0 < z) (hrel : A-z*(b-a)=B) :
    (∫ x in a..b, 1/(A-z*(x-a))^2) = (b-a)/(A*B) := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun x => (A-z*(x-a))⁻¹/z) (1/(A-z*(x-a))^2) x := by
    have hd := (((hasDerivAt_id x).sub_const a).const_mul z).const_sub A
    have he := (hd.inv (affine_pos_on hab hB hz hrel hx).ne').div_const z
    have hv : (- -(z*1)/(A-z*(id x-a))^2)/z = 1/(A-z*(x-a))^2 := by
      dsimp only [id_eq]
      field_simp [hz.ne',(affine_pos_on hab hB hz hrel hx).ne']
    rw [hv] at he
    exact he
  have hi : IntervalIntegrable (fun x => 1/(A-z*(x-a))^2) volume a b := by
    have hc : ContinuousOn (fun x => (A-z*(x-a))⁻¹) (Icc a b) :=
      (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.inv₀
        (fun x hx => (affine_pos_on hab hB hz hrel hx).ne')
    have hh := (hc.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
    change IntervalIntegrable (fun x => ((A-z*(x-a))⁻¹)^2) volume a b at hh
    simpa only [one_div,inv_pow] using hh
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa only [uIcc_of_le hab] using hx)) hi]
  rw [hrel]
  simp only [sub_self,mul_zero,sub_zero]
  have hAn := hA.ne'
  have hBn := hB.ne'
  have hzn := hz.ne'
  field_simp
  nlinarith

lemma integral_eq_stepLogRatios (k : ℕ) (F : ℝ → ℝ) (q D : Fin (k+1) → ℝ)
    (z : Fin k → ℝ) (hq : Monotone q) (hc : ContinuousOn F (Icc (q 0) (q (Fin.last k))))
    (hseg : ∀ i : Fin k, (∫ x in q i.castSucc..q i.succ, F x) =
      (Real.log (D i.castSucc)-Real.log (D i.succ))/z i) :
    (∫ x in q 0..q (Fin.last k), F x) = 2*stepLogRatios k D z := by
  induction k with
  | zero => simp [stepLogRatios,Fin.fin_one_eq_zero]
  | succ k ih =>
    have h01 : q 0 ≤ q 1 := hq (Fin.zero_le _)
    have h1t : q 1 ≤ q (Fin.last (k+1)) := hq (Fin.le_last 1)
    have hct : ContinuousOn F (Icc ((fun i : Fin (k+1) => q i.succ) 0)
        ((fun i : Fin (k+1) => q i.succ) (Fin.last k))) := by
      exact hc.mono (Icc_subset_Icc h01 le_rfl)
    have ht := ih (fun i => q i.succ) (fun i => D i.succ) (fun i => z i.succ)
      (fun a b hab => hq (Fin.succ_le_succ_iff.mpr hab)) hct
      (fun i => by simpa only [Fin.castSucc_succ] using hseg i.succ)
    simp only [Fin.succ_zero_eq_one,Fin.succ_last] at ht
    have h0 := hseg 0
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one] at h0
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hc.mono (Icc_subset_Icc le_rfl h1t)).intervalIntegrable_of_Icc h01)
      ((hc.mono (Icc_subset_Icc h01 le_rfl)).intervalIntegrable_of_Icc h1t),h0,ht,
      stepLogRatios]
    ring

lemma weightedStep_integral_inv {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last k) < 1) (hz : ∀ i, 0 < stepCumulative w i) :
    (∫ t in (0:ℝ)..q (Fin.last k), (weightedStepTail w q t)⁻¹) =
      q 0/weightedStepTail w q (q 0)+
        2*stepLogRatios k (fun i => weightedStepTail w q (q i)) (stepCumulative w) := by
  let D := weightedStepTail w q
  have hqi (i : Fin (k+1)) : q i ≤ q (Fin.last k) := hq (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D (q i) := weightedStepTail_pos _ _ hw hw1 hq1 hqi (hqi i)
  have hc := weightedStepTail_inv_continuousOn w q hw hw1 hq1 hqi
  have h0t : q 0 ≤ q (Fin.last k) := hqi 0
  have hseg (i : Fin k) : (∫ x in q i.castSucc..q i.succ, (D x)⁻¹) =
      (Real.log (D (q i.castSucc))-Real.log (D (q i.succ)))/stepCumulative w i := by
    have hab : q i.castSucc ≤ q i.succ := hq (Fin.castSucc_le_succ i)
    have he := weightedStepTail_affine w q hq i (t := q i.succ) ⟨hab,le_rfl⟩
    calc
      _ = ∫ x in q i.castSucc..q i.succ,
          (D (q i.castSucc)-stepCumulative w i*(x-q i.castSucc))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        dsimp only
        rw [show D t = _ from weightedStepTail_affine w q hq i ht]
      _ = _ := integral_positive_affine_inv hab (hD i.castSucc) (hD i.succ) (hz i) he.symm
  have htail := integral_eq_stepLogRatios k (fun t => (D t)⁻¹) q
    (fun i => D (q i)) (stepCumulative w) hq (hc.mono (Icc_subset_Icc hq0 le_rfl)) hseg
  have hroot : (∫ t in (0:ℝ)..q 0, (D t)⁻¹) = q 0/D (q 0) := by
    calc
      _ = ∫ _t in (0:ℝ)..q 0, (D (q 0))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hq0] at ht
        dsimp only
        rw [show D t = D (q 0) from weightedStepTail_below_min w q (fun i => hq (Fin.zero_le i)) ht.2]
      _ = _ := by simp [div_eq_mul_inv]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (Icc_subset_Icc le_rfl h0t)).intervalIntegrable_of_Icc hq0)
    ((hc.mono (Icc_subset_Icc hq0 le_rfl)).intervalIntegrable_of_Icc h0t),hroot,htail]

lemma weightedStepA_root {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) :
    weightedStepA w q (q 0) = q 0/(weightedStepTail w q (q 0))^2 := by
  unfold weightedStepA
  calc
    _ = ∫ _t in (0:ℝ)..q 0, 1/(weightedStepTail w q (q 0))^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hq0] at ht
      dsimp only
      rw [weightedStepTail_below_min w q (fun i => hq (Fin.zero_le i)) ht.2]
    _ = _ := by simp [div_eq_mul_inv]

lemma weightedStepA_increment {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last k) < 1) (i : Fin k) (hz : 0 < stepCumulative w i) :
    weightedStepA w q (q i.succ)-weightedStepA w q (q i.castSucc) =
      (q i.succ-q i.castSucc)/(weightedStepTail w q (q i.castSucc)*weightedStepTail w q (q i.succ)) := by
  let D := weightedStepTail w q
  have hqi (i : Fin (k+1)) : q i ≤ q (Fin.last k) := hq (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D (q i) := weightedStepTail_pos _ _ hw hw1 hq1 hqi (hqi i)
  have hc : ContinuousOn (fun t => 1/(D t)^2) (Icc 0 (q (Fin.last k))) := by
    have hh := (weightedStepTail_inv_continuousOn w q hw hw1 hq1 hqi).pow 2
    change ContinuousOn (fun t => ((D t)⁻¹)^2) _ at hh
    simpa only [one_div,inv_pow] using hh
  have h0i : 0 ≤ q i.castSucc := hq0.trans (hq (Fin.zero_le _))
  have hij : q i.castSucc ≤ q i.succ := hq (Fin.castSucc_le_succ i)
  have hi := (hc.mono (Icc_subset_Icc le_rfl (hqi i.castSucc))).intervalIntegrable_of_Icc (μ := volume) h0i
  have hj := (hc.mono (Icc_subset_Icc h0i (hqi i.succ))).intervalIntegrable_of_Icc (μ := volume) hij
  have ha := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hseg : (∫ t in q i.castSucc..q i.succ, 1/(D t)^2) =
      (q i.succ-q i.castSucc)/(D (q i.castSucc)*D (q i.succ)) := by
    have he := weightedStepTail_affine w q hq i (t := q i.succ) ⟨hij,le_rfl⟩
    calc
      _ = ∫ t in q i.castSucc..q i.succ,
          1/(D (q i.castSucc)-stepCumulative w i*(t-q i.castSucc))^2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hij] at ht
        dsimp only
        rw [show D t = _ from weightedStepTail_affine w q hq i ht]
      _ = _ := integral_positive_affine_inv_sq hij (hD i.castSucc) (hD i.succ) hz he.symm
  change (∫ t in (0:ℝ)..q i.succ, 1/(D t)^2)-
    (∫ t in (0:ℝ)..q i.castSucc, 1/(D t)^2) = _
  rw [← ha,hseg]
  ring

lemma weightedStep_truncated_entropy_nonneg {I : Type*} [Fintype I] (w q : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, q i ≤ B) :
    0 ≤ ((∫ t in (0:ℝ)..B, (weightedStepTail w q t)⁻¹)+Real.log (1-B))/2 := by
  have hiD := (weightedStepTail_inv_continuousOn w q hw hw1 hB1 hq).intervalIntegrable_of_Icc (μ := volume) hB0
  have hiR : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 B :=
    ((continuous_const.sub continuous_id).continuousOn.inv₀
      (fun t (ht : t ∈ Icc (0:ℝ) B) => (sub_pos.mpr (ht.2.trans_lt hB1)).ne')).intervalIntegrable_of_Icc hB0
  have hle := intervalIntegral.integral_mono_on hB0 hiR hiD (fun t ht =>
    (inv_le_inv₀ (sub_pos.mpr (ht.2.trans_lt hB1))
      (weightedStepTail_pos w q hw hw1 hB1 hq ht.2)).mpr
        (weightedStepTail_upper w q hw hw1 t))
  rw [integral_one_sub_inv hB1] at hle
  linarith

lemma entropy_weightedStepTrial_toReal {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i : ℝ) ≤ B) :
    (entropy (weightedStepTrial w q hw hw1)).toReal =
      ((∫ t in (0:ℝ)..B, (weightedStepTail w (fun i => (q i:ℝ)) t)⁻¹)+Real.log (1-B))/2 := by
  rw [entropy_weightedStepTrial w q hw hw1 B hB0 hB1 hq,ENNReal.toReal_ofReal
    (weightedStep_truncated_entropy_nonneg w (fun i => (q i:ℝ)) hw hw1 hB0 hB1 hq)]

lemma entropy_weightedStepTrial_toReal_finite_formula {k : ℕ} (w : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hz : ∀ i, 0 < stepCumulative w i) :
    (entropy (weightedStepTrial w q hw hw1)).toReal =
      Real.log (tailIntegral (weightedStepTrial w q hw hw1) (q (Fin.last k)))/2+
        stepLogRatios k (fun i => tailIntegral (weightedStepTrial w q hw hw1) (q i)) (stepCumulative w)+
        (q 0:ℝ)/(2*tailIntegral (weightedStepTrial w q hw hw1) (q 0)) := by
  have hqr : Monotone (fun i => (q i:ℝ)) := fun i j hij => hq hij
  have hqmax (i : Fin (k+1)) : (q i:ℝ) ≤ (q (Fin.last k):ℝ) := hqr (Fin.le_last i)
  rw [entropy_weightedStepTrial_toReal w q hw hw1 (q (Fin.last k)) (q (Fin.last k)).2.1 hq1 hqmax,
    weightedStep_integral_inv w (fun i => (q i:ℝ)) hw hw1 hqr (q 0).2.1 hq1 hz]
  simp only [tailIntegral_weightedStepTrial]
  change _ = Real.log (weightedStepTail w (fun i => (q i:ℝ)) (q (Fin.last k)))/2+
      stepLogRatios k (fun i => weightedStepTail w (fun i => (q i:ℝ)) (q i)) (stepCumulative w)+
      (q 0:ℝ)/(2*weightedStepTail w (fun i => (q i:ℝ)) (q 0))
  rw [weightedStepTail_of_le w (fun i => (q i:ℝ)) hw1 hqmax]
  ring

lemma stepCumulative_pos {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) (i : Fin k) :
    0 < stepCumulative w i := by
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> first | exact (hw j).le | rfl
  · exact ⟨0,Finset.mem_univ _,by simpa only [ite_eq_left (Fin.zero_le _)] using hw 0⟩

lemma stepCumulative_lt_one {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : Fin k) :
    stepCumulative w i < 1 := by
  rw [← hw1]
  apply Finset.sum_lt_sum
  · intro j _
    split_ifs <;> first | rfl | exact (hw j).le
  · refine ⟨Fin.last k,Finset.mem_univ _,?_⟩
    have hnot : ¬Fin.last k ≤ i.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]
      omega
    simpa only [ite_eq_right hnot] using hw (Fin.last k)

lemma stepCumulative_strictMono {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) : StrictMono (stepCumulative w) := by
  intro i j hij
  apply Finset.sum_lt_sum
  · intro a _
    by_cases hai : a ≤ i.castSucc
    · have haj : a ≤ j.castSucc := hai.trans (Fin.castSucc_le_castSucc_iff.mpr hij.le)
      simp only [ite_eq_left hai,ite_eq_left haj,le_refl]
    · simp only [ite_eq_right hai]
      split_ifs <;> first | exact (hw a).le | rfl
  · refine ⟨j.castSucc,Finset.mem_univ _,?_⟩
    have hnot : ¬j.castSucc ≤ i.castSucc := by simpa only [Fin.castSucc_le_castSucc_iff] using not_le.mpr hij
    simpa only [ite_eq_right hnot,ite_eq_left le_rfl] using hw j.castSucc

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Entropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma reciprocal_supporting_inequality {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y-x)/y^2 ≤ x⁻¹-y⁻¹ := by
  have he : x⁻¹-y⁻¹-(y-x)/y^2=(x-y)^2/(x*y^2) := by
    field_simp [hx.ne',hy.ne']
    ring
  have hp := div_nonneg (sq_nonneg (x-y)) (mul_pos hx (sq_pos_of_pos hy)).le
  rw [← he] at hp
  linarith

lemma max_difference_support {p q t : ℝ} :
    (if t ≤ q then p-q else 0) ≤ max p t-max q t := by
  split_ifs with ht
  · rw [max_eq_left ht]
    exact sub_le_sub_right (le_max_left _ _) _
  · rw [max_eq_right (le_of_not_ge ht)]
    exact sub_nonneg.mpr (le_max_right _ _)

theorem entropy_weightedStep_support {I : Type*} [Fintype I]
    (w : I → ℝ) (p q : I → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ i, (p i:ℝ) ≤ B) (hq : ∀ i, (q i:ℝ) ≤ B) :
    (∑ i, w i*((p i:ℝ)-(q i:ℝ))*weightedStepA w (fun j => (q j:ℝ)) (q i))/2 ≤
      (entropy (weightedStepTrial w p hw hw1)).toReal-
        (entropy (weightedStepTrial w q hw hw1)).toReal := by
  classical
  let P : I → ℝ := fun i => p i
  let Q : I → ℝ := fun i => q i
  let Dp := weightedStepTail w P
  let Dq := weightedStepTail w Q
  have hcP := weightedStepTail_inv_continuousOn w P hw hw1 hB1 hp
  have hcQ := weightedStepTail_inv_continuousOn w Q hw hw1 hB1 hq
  have hiP := hcP.intervalIntegrable_of_Icc (μ := volume) hB0
  have hiQ := hcQ.intervalIntegrable_of_Icc (μ := volume) hB0
  have hcQ2 : ContinuousOn (fun t => 1/(Dq t)^2) (Icc 0 B) := by
    have hh := hcQ.pow 2
    change ContinuousOn (fun t => ((Dq t)⁻¹)^2) _ at hh
    simpa only [one_div,inv_pow] using hh
  have hiQ2 := hcQ2.intervalIntegrable_of_Icc (μ := volume) hB0
  let F : I → ℝ → ℝ := fun i => (Iic (Q i)).indicator (fun t => 1/(Dq t)^2)
  have hFi (i : I) : IntervalIntegrable (F i) volume 0 B :=
    ⟨hiQ2.1.indicator measurableSet_Iic,hiQ2.2.indicator measurableSet_Iic⟩
  have hl (t : ℝ) (ht : t ∈ Icc 0 B) :
      (∑ i, w i*(P i-Q i)*F i t) ≤ (Dp t)⁻¹-(Dq t)⁻¹ := by
    have hDtP : 0 < Dp t := weightedStepTail_pos w P hw hw1 hB1 hp ht.2
    have hDtQ : 0 < Dq t := weightedStepTail_pos w Q hw hw1 hB1 hq ht.2
    have hmax : (∑ i, w i*(if t ≤ Q i then P i-Q i else 0)) ≤ Dq t-Dp t := by
      change _ ≤ (∑ i, w i*(1-max (Q i) t))-(∑ i, w i*(1-max (P i) t))
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      have hm := mul_le_mul_of_nonneg_left (@max_difference_support (P i) (Q i) t) (hw i)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hmax (by positivity : 0 ≤ 1/(Dq t)^2)
    have he : (∑ i, w i*(P i-Q i)*F i t) =
        (∑ i, w i*(if t ≤ Q i then P i-Q i else 0))*(1/(Dq t)^2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [F,Set.indicator_apply,mem_Iic]
      split_ifs <;> ring
    rw [he]
    calc
      _ ≤ (Dq t-Dp t)*(1/(Dq t)^2) := hmul
      _ = (Dq t-Dp t)/(Dq t)^2 := by ring
      _ ≤ _ := reciprocal_supporting_inequality hDtP hDtQ
  have hiF : IntervalIntegrable (fun t => ∑ i, w i*(P i-Q i)*F i t) volume 0 B := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => (hFi i).const_mul (w i*(P i-Q i)))
    have he : (∑ i, fun t => w i*(P i-Q i)*F i t) =
        (fun t => ∑ i, w i*(P i-Q i)*F i t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [he] at hh
    exact hh
  have hInt := intervalIntegral.integral_mono_on hB0 hiF (hiP.sub hiQ) hl
  have hIntF (i : I) : (∫ t in (0:ℝ)..B, F i t) = weightedStepA w Q (Q i) := by
    exact intervalIntegral.integral_indicator ⟨(q i).2.1,hq i⟩
  rw [intervalIntegral.integral_sub hiP hiQ,
    intervalIntegral.integral_finsetSum (fun i _ => (hFi i).const_mul _)] at hInt
  simp only [intervalIntegral.integral_const_mul,hIntF] at hInt
  rw [entropy_weightedStepTrial_toReal w p hw hw1 B hB0 hB1 hp,
    entropy_weightedStepTrial_toReal w q hw hw1 B hB0 hB1 hq]
  change (∑ i, w i*(P i-Q i)*weightedStepA w Q (Q i))/2 ≤
    ((∫ t in (0:ℝ)..B, (Dp t)⁻¹)+Real.log (1-B))/2-
      ((∫ t in (0:ℝ)..B, (Dq t)⁻¹)+Real.log (1-B))/2
  linarith

theorem stationary_finite_entropy_minimizes {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q p : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hp : Monotone p)
    (hq1 : (q (Fin.last k):ℝ) < 1) (hp1 : (p (Fin.last k):ℝ) < 1)
    (hstat : ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ) ≤
      (entropy (weightedStepTrial w p hw hw1)).toReal-∑ i, w i*h i*(p i:ℝ) := by
  let B := max (p (Fin.last k):ℝ) (q (Fin.last k):ℝ)
  have hB0 : 0 ≤ B := (p (Fin.last k)).2.1.trans (le_max_left _ _)
  have hB1 : B < 1 := max_lt hp1 hq1
  have hP (i : Fin (k+1)) : (p i:ℝ) ≤ B :=
    (show (p i:ℝ) ≤ (p (Fin.last k):ℝ) from hp (Fin.le_last i)).trans (le_max_left _ _)
  have hQ (i : Fin (k+1)) : (q i:ℝ) ≤ B :=
    (show (q i:ℝ) ≤ (q (Fin.last k):ℝ) from hq (Fin.le_last i)).trans (le_max_right _ _)
  have hs := entropy_weightedStep_support w p q hw hw1 B hB0 hB1 hP hQ
  have he : (∑ i, w i*((p i:ℝ)-(q i:ℝ))*weightedStepA w (fun j => (q j:ℝ)) (q i))/2 =
      (∑ i, w i*h i*(p i:ℝ))-(∑ i, w i*h i*(q i:ℝ)) := by
    rw [Finset.sum_div,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hstat i]
    ring
  rw [he] at hs
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepDual
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma finite_weighted_increment_identity (k : ℕ) (a h : Fin (k+1) → ℝ) :
    h (Fin.last k)-∑ j, a j*h j = h 0*(1-∑ j, a j)+
      ∑ i : Fin k, (h i.succ-h i.castSucc)*(1-∑ j : Fin (k+1), if i.castSucc < j then a j else 0) := by
  classical
  induction k with
  | zero => simp [Fin.fin_one_eq_zero]; ring
  | succ k ih =>
    have ht := ih (fun j => a j.succ) (fun j => h j.succ)
    have hl0 : (∑ j : Fin (k+2), if (0:Fin (k+2)) < j then a j else 0) =
        ∑ j : Fin (k+1), a j.succ := by
      rw [Fin.sum_univ_succ]
      simp only [lt_self_iff_false,ite_false,Fin.succ_pos,ite_true,zero_add]
    have hlt (i : Fin k) : (∑ j : Fin (k+2), if i.castSucc.succ < j then a j else 0) =
        ∑ j : Fin (k+1), if i.castSucc < j then a j.succ else 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.not_lt_zero,ite_false,zero_add,Fin.succ_lt_succ_iff]
    rw [Fin.sum_univ_succ (fun j => a j*h j),Fin.sum_univ_succ a,
      Fin.sum_univ_succ (fun i : Fin (k+1) =>
        (h i.succ-h i.castSucc)*(1-∑ j : Fin (k+2), if i.castSucc < j then a j else 0))]
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one,Fin.castSucc_succ]
    erw [hl0]
    simp only [hlt]
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht
    linear_combination ht

lemma weightedStepTail_root {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw1 : ∑ i, w i = 1) (hq : Monotone q) :
    weightedStepTail w q (q 0) = 1-∑ i, w i*q i := by
  unfold weightedStepTail
  simp only [max_eq_left (hq (Fin.zero_le _)),mul_sub,mul_one]
  rw [Finset.sum_sub_distrib,hw1]

lemma weightedStepTail_cut {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw1 : ∑ i, w i = 1) (hq : Monotone q) (i : Fin k) :
    weightedStepTail w q (q i.castSucc)+stepCumulative w i*q i.castSucc =
      1-∑ j : Fin (k+1), if i.castSucc < j then w j*q j else 0 := by
  unfold weightedStepTail stepCumulative
  rw [Finset.sum_mul,← Finset.sum_add_distrib,← hw1,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ≤ i.castSucc
  · rw [ite_eq_left hj,ite_eq_right (not_lt.mpr hj),max_eq_right (hq hj)]
    rw [hw1]
    ring
  · rw [ite_eq_right hj,ite_eq_left (lt_of_not_ge hj),max_eq_left (hq (le_of_not_ge hj))]
    rw [hw1]
    ring

lemma finite_sum_successive_differences (k : ℕ) (v : Fin (k+1) → ℝ) :
    (∑ i : Fin k, (v i.succ-v i.castSucc)) = v (Fin.last k)-v 0 := by
  have h1 := Fin.sum_univ_succ v
  have h2 := Fin.sum_univ_castSucc v
  rw [Finset.sum_sub_distrib]
  linarith

lemma stationary_field_shift_identity {k : ℕ} (w q h : Fin (k+1) → ℝ)
    (hw1 : ∑ i, w i = 1) (hq : Monotone q)
    (hD : ∀ i, 0 < weightedStepTail w q (q i))
    (hroot : 2*h 0=q 0/(weightedStepTail w q (q 0))^2)
    (hinc : ∀ i : Fin k, 2*(h i.succ-h i.castSucc)=
      (q i.succ-q i.castSucc)/(weightedStepTail w q (q i.castSucc)*weightedStepTail w q (q i.succ))) :
    2*(h (Fin.last k)-∑ i, w i*h i*q i) = (weightedStepTail w q (q (Fin.last k)))⁻¹-1 := by
  let D := fun i => weightedStepTail w q (q i)
  have hgap (i : Fin k) : D i.castSucc-D i.succ = stepCumulative w i*(q i.succ-q i.castSucc) := by
    have he := weightedStepTail_affine w q hq i (t := q i.succ) ⟨hq (Fin.castSucc_le_succ i),le_rfl⟩
    change D i.succ = D i.castSucc-stepCumulative w i*(q i.succ-q i.castSucc) at he
    linarith
  have hroot' : 2*h 0*(1-∑ i, w i*q i) = q 0/D 0 := by
    rw [← weightedStepTail_root w q hw1 hq,hroot]
    change (q 0/(D 0)^2)*D 0=q 0/D 0
    field_simp [(hD 0).ne']
  have hinc' (i : Fin k) : 2*(h i.succ-h i.castSucc)*
      (1-∑ j : Fin (k+1), if i.castSucc < j then w j*q j else 0) =
        q i.succ/D i.succ-q i.castSucc/D i.castSucc := by
    rw [← weightedStepTail_cut w q hw1 hq i,hinc i]
    change ((q i.succ-q i.castSucc)/(D i.castSucc*D i.succ))*
      (D i.castSucc+stepCumulative w i*q i.castSucc)=_
    have hg := hgap i
    have h1 : D i.castSucc ≠ 0 := (hD i.castSucc).ne'
    have h2 : D i.succ ≠ 0 := (hD i.succ).ne'
    field_simp [h1,h2]
    linear_combination -q i.castSucc * hg
  have he := finite_weighted_increment_identity k (fun i => w i*q i) h
  have hend : D (Fin.last k) = 1-q (Fin.last k) :=
    weightedStepTail_of_le w q hw1 (fun i => hq (Fin.le_last i))
  calc
    _ = 2*h 0*(1-∑ i, w i*q i)+∑ i : Fin k,
        2*(h i.succ-h i.castSucc)*(1-∑ j : Fin (k+1), if i.castSucc < j then w j*q j else 0) := by
      simp only [mul_right_comm (w _) (h _) (q _)]
      rw [he,mul_add,Finset.mul_sum]
      ring_nf
    _ = q 0/D 0+∑ i : Fin k, (q i.succ/D i.succ-q i.castSucc/D i.castSucc) := by
      rw [hroot']
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hinc' i)
    _ = q (Fin.last k)/D (Fin.last k) := by
      rw [finite_sum_successive_differences k (fun i => q i/D i)]
      ring
    _ = _ := by
      change q (Fin.last k)/D (Fin.last k)=(D (Fin.last k))⁻¹-1
      have hn : D (Fin.last k) ≠ 0 := (hD (Fin.last k)).ne'
      field_simp [hn]
      linarith

lemma stepFieldIncrement_sq (k : ℕ) (h : Fin (k+1) → ℝ) (hh : Monotone h) (i : Fin k) :
    (stepFieldIncrement k h (k-1-i.val))^2 = 2*(h i.succ-h i.castSucc) := by
  have hi : k-1-i.val < k := by omega
  have he : Fin.rev (⟨k-1-i.val,hi⟩ : Fin k) = i := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [stepFieldIncrement,dite_eq_left hi,he,Real.sq_sqrt]
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hh (Fin.castSucc_le_succ i)))

theorem finiteSphericalFieldValue_stationary {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hstat : ∀ i, 2*h i = weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
      (𝓝 ((entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-
        ∑ i, w i*h i*(q i:ℝ))) := by
  let Q : Fin (k+1) → ℝ := fun i => q i
  let D : Fin (k+1) → ℝ := fun i => weightedStepTail w Q (Q i)
  have hm : Monotone Q := fun i j hij => hq hij
  have h0 : 0 ≤ Q 0 := (q 0).2.1
  have hmax (i : Fin (k+1)) : Q i ≤ Q (Fin.last k) := hm (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D i :=
    weightedStepTail_pos w Q (fun i => (hw i).le) hw1 hq1 hmax (hmax i)
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hroot : 2*h 0=Q 0/(D 0)^2 :=
    (hstat 0).trans (weightedStepA_root w Q hm h0)
  have hinc (i : Fin k) : 2*(h i.succ-h i.castSucc)=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) := by
    calc
      _ = weightedStepA w Q (Q i.succ)-weightedStepA w Q (Q i.castSucc) := by
        linarith [hstat i.succ,hstat i.castSucc]
      _ = _ := weightedStepA_increment w Q (fun i => (hw i).le) hw1 hm h0 hq1 i (hz0 i)
  have hh : Monotone h := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hp := div_nonneg (sub_nonneg.mpr (hm (Fin.castSucc_le_succ i)))
      (mul_pos (hD i.castSucc) (hD i.succ)).le
    rw [← hinc i] at hp
    linarith
  have hr0 : 0 ≤ 2*h 0 := by rw [hroot]; positivity
  have hr : (Real.toNNReal (2*h 0):ℝ)=Q 0/(D 0)^2 := by rw [Real.coe_toNNReal _ hr0,hroot]
  have hend : D (Fin.last k) = 1-Q (Fin.last k) := weightedStepTail_of_le w Q hw1 hmax
  have hgap (i : Fin k) : D i.castSucc-D i.succ=stepCumulative w i*(Q i.succ-Q i.castSucc) := by
    have he := weightedStepTail_affine w Q hm i (t := Q i.succ) ⟨hm (Fin.castSucc_le_succ i),le_rfl⟩
    change D i.succ=D i.castSucc-stepCumulative w i*(Q i.succ-Q i.castSucc) at he
    linarith
  have hσ (i : Fin k) : (stepFieldIncrement k h (k-1-i.val))^2=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) :=
    (stepFieldIncrement_sq k h hh i).trans (hinc i)
  have ht := (expectedCoordinateSphereLog_stationary_data k (stepFieldIncrement k h)
    Q D (stepCumulative w) hz hz0 hz1 hD hend hgap hσ _ hr).sub_const (h (Fin.last k))
  have he := entropy_weightedStepTrial_toReal_finite_formula w q (fun i => (hw i).le) hw1 hq hq1 hz0
  simp only [tailIntegral_weightedStepTrial] at he
  change (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal =
    Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0) at he
  have hs := stationary_field_shift_identity w Q h hw1 hm hD hroot hinc
  have hv : Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0)+
      ((D (Fin.last k))⁻¹-1)/2-h (Fin.last k) =
      (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-∑ i, w i*h i*Q i := by
    rw [he]
    change 2*(h (Fin.last k)-∑ i, w i*h i*Q i)=(D (Fin.last k))⁻¹-1 at hs
    linarith
  rw [hv] at ht
  exact ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StationaryExistence
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma stepTailSum_zero {k : ℕ} (v : Fin k → ℝ) : stepTailSum v 0=∑ j, v j := by
  simp only [stepTailSum,Fin.zero_le,ite_true]

lemma stepTailSum_last {k : ℕ} (v : Fin k → ℝ) : stepTailSum v (Fin.last k)=0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : ¬Fin.last k ≤ j.castSucc := by simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]; omega
  exact ite_eq_right hj

lemma stepTailSum_difference {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    stepTailSum v i.castSucc-stepTailSum v i.succ=v i := by
  classical
  unfold stepTailSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin k, if j=i then v j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j=i
      · subst j
        have hi : ¬i.succ ≤ i.castSucc := by simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]; omega
        simp only [ite_eq_left le_rfl,ite_eq_right hi,sub_zero,ite_true]
      · have he : (i.castSucc ≤ j.castSucc) ↔ (i.succ ≤ j.castSucc) := by
          simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc]
          have hv : i.val ≠ j.val := by intro hij; exact hji (Fin.ext hij.symm)
          omega
        simp only [he,sub_self,ite_eq_right hji]
    _ = _ := by simp

lemma stepTailSum_le_zero {k : ℕ} (v : Fin k → ℝ) (hv : ∀ j, 0 ≤ v j) (i : Fin (k+1)) :
    stepTailSum v i ≤ stepTailSum v 0 := by
  rw [stepTailSum_zero]
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> first | rfl | exact hv j

lemma finitePrecisionShift_le_root {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) (i : Fin (k+1)) :
    finitePrecisionShift z h i ≤ finitePrecisionShift z h 0 :=
  stepTailSum_le_zero _ (fun j => mul_nonneg (mul_nonneg (by norm_num) (hz j))
    (sub_nonneg.mpr (hh (Fin.castSucc_le_succ j)))) i

lemma finitePrecisionTail_pos {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin (k+1)) : 0 < finitePrecisionTail z h b i :=
  inv_pos.mpr (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i).trans_lt hb))

lemma finitePrecisionTail_gap {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin k) : finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ =
      z i*finiteOverlapIncrement z h b i := by
  have h1 : b-finitePrecisionShift z h i.castSucc ≠ 0 :=
    (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i.castSucc).trans_lt hb)).ne'
  have h2 : b-finitePrecisionShift z h i.succ ≠ 0 :=
    (sub_pos.mpr ((finitePrecisionShift_le_root z h hz hh i.succ).trans_lt hb)).ne'
  have he := stepTailSum_difference (fun j => 2*z j*(h j.succ-h j.castSucc)) i
  change finitePrecisionShift z h i.castSucc-finitePrecisionShift z h i.succ =
    2*z i*(h i.succ-h i.castSucc) at he
  unfold finiteOverlapIncrement finitePrecisionTail
  field_simp [h1,h2]
  linear_combination he

lemma finiteOverlapIncrement_nonneg {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) {b : ℝ} (hb : finitePrecisionShift z h 0 < b)
    (i : Fin k) : 0 ≤ finiteOverlapIncrement z h b i := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hh (Fin.castSucc_le_succ i))))
    (finitePrecisionTail_pos z h hz hh hb i.castSucc).le) (finitePrecisionTail_pos z h hz hh hb i.succ).le

lemma finiteStationarityMass_ge_root {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (hh : Monotone h) (hh0 : 0 ≤ h 0)
    {b : ℝ} (hb : finitePrecisionShift z h 0 < b) :
    finitePrecisionTail z h b 0 ≤ finiteStationarityMass z h b := by
  have hg (i : Fin k) : finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ ≤
      finiteOverlapIncrement z h b i := by
    rw [finitePrecisionTail_gap z h hz0 hh hb i]
    exact mul_le_of_le_one_left (finiteOverlapIncrement_nonneg z h hz0 hh hb i) (hz1 i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hg i)
  have ht := finite_sum_successive_differences k (finitePrecisionTail z h b)
  have he : (∑ i : Fin k, (finitePrecisionTail z h b i.castSucc-finitePrecisionTail z h b i.succ)) =
      finitePrecisionTail z h b 0-finitePrecisionTail z h b (Fin.last k) := by
    rw [Finset.sum_sub_distrib] at ht ⊢
    linarith
  rw [he] at hs
  have hn : 0 ≤ 2*h 0*(finitePrecisionTail z h b 0)^2 := by positivity
  unfold finiteStationarityMass
  linarith

lemma finiteStationarityMass_continuousOn {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hh : Monotone h) :
    ContinuousOn (finiteStationarityMass z h) (Ici (finitePrecisionShift z h 0+1)) := by
  have hc (i : Fin (k+1)) : ContinuousOn (fun b => finitePrecisionTail z h b i)
      (Ici (finitePrecisionShift z h 0+1)) := by
    apply (continuous_id.sub continuous_const).continuousOn.inv₀
    intro b hb
    have hi := finitePrecisionShift_le_root z h hz hh i
    change finitePrecisionShift z h 0+1 ≤ b at hb
    change b-finitePrecisionShift z h i ≠ 0
    exact (sub_pos.mpr (by linarith)).ne'
  exact ((continuousOn_const.mul (hc 0 |>.pow 2)).add
    (continuousOn_finsetSum Finset.univ (fun i _ =>
      (continuousOn_const.mul (hc i.castSucc)).mul (hc i.succ)))).add (hc (Fin.last k))

lemma finiteStationarityMass_tendsto {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) :
    Tendsto (finiteStationarityMass z h) atTop (𝓝 0) := by
  have ht (i : Fin (k+1)) : Tendsto (fun b => finitePrecisionTail z h b i) atTop (𝓝 0) := by
    simpa only [finitePrecisionTail,sub_eq_add_neg,Function.comp_def,id_eq] using
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-finitePrecisionShift z h i) tendsto_id))
  have hi (i : Fin k) : Tendsto (fun b => finiteOverlapIncrement z h b i) atTop (𝓝 0) := by
    simpa only [finiteOverlapIncrement,mul_zero] using ((ht i.castSucc).const_mul (2*(h i.succ-h i.castSucc))).mul (ht i.succ)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hf := (((ht 0).pow 2).const_mul (2*h 0)).add hs |>.add (ht (Fin.last k))
  change Tendsto (fun b => 2*h 0*(finitePrecisionTail z h b 0)^2+
    (∑ i, finiteOverlapIncrement z h b i)+finitePrecisionTail z h b (Fin.last k)) atTop (𝓝 0)
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,Finset.sum_const_zero,zero_add] using hf

theorem exists_finite_normalizing_precision {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ b : ℝ, finitePrecisionShift z h 0 < b ∧ finiteStationarityMass z h b=1 := by
  let a := finitePrecisionShift z h 0+1
  have ha : finitePrecisionShift z h 0 < a := by dsimp only [a]; linarith
  have hstart : 1 ≤ finiteStationarityMass z h a := by
    have hs := finiteStationarityMass_ge_root z h hz0 hz1 hh hh0 ha
    simpa only [finitePrecisionTail,a,add_sub_cancel_left,inv_one] using hs
  have hev := (finiteStationarityMass_tendsto z h).eventually_lt_const (by norm_num : (0:ℝ)<1)
  obtain ⟨b,hb,hend⟩ := ((eventually_ge_atTop a).and hev).exists
  have hc : ContinuousOn (finiteStationarityMass z h) (Icc a b) :=
    (finiteStationarityMass_continuousOn z h hz0 hh).mono Icc_subset_Ici_self
  obtain ⟨c,hc,he⟩ := intermediate_value_Icc' hb hc ⟨hend.le,hstart⟩
  exact ⟨c,ha.trans_le hc.1,he⟩

theorem exists_finite_stationary_quantile {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
      ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i) := by
  let z := stepCumulative w
  have hz0 : ∀ i, 0 < z i := stepCumulative_pos w hw
  have hz1 : ∀ i, z i < 1 := stepCumulative_lt_one w hw hw1
  obtain ⟨b,hb,hb1⟩ := exists_finite_normalizing_precision z h
    (fun i => (hz0 i).le) (fun i => (hz1 i).le) hh hh0
  let D := finitePrecisionTail z h b
  let v := finiteOverlapIncrement z h b
  let Q : Fin (k+1) → ℝ := fun i => 2*h 0*(D 0)^2+(∑ j, v j)-stepTailSum v i
  have hD (i : Fin (k+1)) : 0 < D i := finitePrecisionTail_pos z h (fun i => (hz0 i).le) hh hb i
  have hv (i : Fin k) : 0 ≤ v i := finiteOverlapIncrement_nonneg z h (fun i => (hz0 i).le) hh hb i
  have hQ0 : Q 0=2*h 0*(D 0)^2 := by simp only [Q,stepTailSum_zero]; ring
  have hQlast : Q (Fin.last k)=2*h 0*(D 0)^2+∑ j, v j := by simp only [Q,stepTailSum_last,sub_zero]
  have hQinc (i : Fin k) : Q i.succ-Q i.castSucc=v i := by
    have he := stepTailSum_difference v i
    dsimp only [Q]
    linarith
  have hQmono : Monotone Q := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have he := hQinc i
    linarith [hv i]
  have hQ0pos : 0 ≤ Q 0 := by rw [hQ0]; positivity
  have hnorm : Q (Fin.last k)+D (Fin.last k)=1 := by
    rw [hQlast]
    exact hb1
  have hQ1 : Q (Fin.last k) < 1 := by linarith [hD (Fin.last k)]
  have hgap (i : Fin k) : D i.castSucc-D i.succ=z i*(Q i.succ-Q i.castSucc) := by
    rw [hQinc]
    exact finitePrecisionTail_gap z h (fun i => (hz0 i).le) hh hb i
  let T : Fin (k+1) → ℝ := fun i => weightedStepTail w Q (Q i)
  have hTgap (i : Fin k) : T i.castSucc-T i.succ=z i*(Q i.succ-Q i.castSucc) := by
    have he := weightedStepTail_affine w Q hQmono i (t := Q i.succ) ⟨hQmono (Fin.castSucc_le_succ i),le_rfl⟩
    change T i.succ=T i.castSucc-z i*(Q i.succ-Q i.castSucc) at he
    linarith
  have hTlast : T (Fin.last k)=D (Fin.last k) := by
    have he := weightedStepTail_of_le w Q hw1 (fun i => hQmono (Fin.le_last i))
    change T (Fin.last k)=1-Q (Fin.last k) at he
    linarith
  have hconst (i : Fin (k+1)) : T i-D i=T 0-D 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => linarith [hTgap i,hgap i]
  have hTD (i : Fin (k+1)) : T i=D i := by
    have he := hconst (Fin.last k)
    rw [hTlast] at he
    linarith [hconst i]
  have hroot : 2*h 0=Q 0/(T 0)^2 := by
    rw [hTD,hQ0]
    have hn : D 0 ≠ 0 := (hD 0).ne'
    field_simp [hn]
  have hinc (i : Fin k) : 2*(h i.succ-h i.castSucc)=(Q i.succ-Q i.castSucc)/(T i.castSucc*T i.succ) := by
    rw [hQinc,hTD,hTD]
    change 2*(h i.succ-h i.castSucc)=
      (2*(h i.succ-h i.castSucc)*D i.castSucc*D i.succ)/(D i.castSucc*D i.succ)
    have hn : D i.castSucc ≠ 0 := (hD i.castSucc).ne'
    have hn' : D i.succ ≠ 0 := (hD i.succ).ne'
    field_simp [hn,hn']
  have hstat (i : Fin (k+1)) : 2*h i=weightedStepA w Q (Q i) := by
    induction i using Fin.induction with
    | zero => rw [weightedStepA_root w Q hQmono hQ0pos]; exact hroot
    | succ i ih =>
      have he := weightedStepA_increment w Q (fun i => (hw i).le) hw1 hQmono hQ0pos hQ1 i (hz0 i)
      change weightedStepA w Q (Q i.succ)-weightedStepA w Q (Q i.castSucc)=
        (Q i.succ-Q i.castSucc)/(T i.castSucc*T i.succ) at he
      linarith [hinc i]
  let q : Fin (k+1) → Time := fun i => ⟨Q i,⟨hQ0pos.trans (hQmono (Fin.zero_le i)),
    ((hQmono (Fin.le_last i)).trans_lt hQ1).le⟩⟩
  exact ⟨q,(fun i j hij => hQmono hij),hQ1,hstat⟩

theorem finiteSphericalFieldValue_pointwise_dual {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    ∃ q : Fin (k+1) → Time, Monotone q ∧ (q (Fin.last k):ℝ) < 1 ∧
      IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
        (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) ∧
      Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
        (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1))) := by
  obtain ⟨q,hq,hq1,hs⟩ := exists_finite_stationary_quantile w h hw hw1 hh hh0
  have hleast : IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
      (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) := by
    refine ⟨⟨q,⟨hq,hq1⟩,rfl⟩,?_⟩
    rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
    exact stationary_finite_entropy_minimizes w h q p (fun i => (hw i).le) hw1 hq hp hq1 hp1 hs
  refine ⟨q,hq,hq1,hleast,?_⟩
  rw [hleast.csInf_eq]
  exact finiteSphericalFieldValue_stationary w h q hw hw1 hq hq1 hs

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CoupledDual
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma Trial.ext_fun {m n : Trial} (h : ∀ t, m t=n t) : m=n := by
  cases m
  cases n
  congr 1
  exact funext h

lemma weightedStepTrial_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w : I → ℝ) (q : I → Time)
    (hc : ∀ a, 0 ≤ c a) (hc1 : ∑ a, c a=1)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepTrial c (fun a => q a.1) hc hc1=weightedStepTrial w q hw hw1 := by
  apply Trial.ext_fun
  intro t
  change (∑ a : I×J, if q a.1 ≤ t then c a else 0)=∑ i, if q i ≤ t then w i else 0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i ≤ t <;> simp [hi,hrow]

lemma weightedStepTrial_coupling_snd {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (v : J → ℝ) (p : J → Time)
    (hc : ∀ a, 0 ≤ c a) (hc1 : ∑ a, c a=1)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i=1)
    (hcol : ∀ j, ∑ i, c (i,j)=v j) :
    weightedStepTrial c (fun a => p a.2) hc hc1=weightedStepTrial v p hv hv1 := by
  apply Trial.ext_fun
  intro t
  change (∑ a : I×J, if p a.2 ≤ t then c a else 0)=∑ j, if p j ≤ t then v j else 0
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : p j ≤ t <;> simp [hj,hcol]

lemma coupling_sum_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w f : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    (∑ a, c a*f a.1)=∑ i, w i*f i := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul,hrow]

lemma coupling_sum_snd {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (v f : J → ℝ) (hcol : ∀ j, ∑ i, c (i,j)=v j) :
    (∑ a, c a*f a.2)=∑ j, v j*f j := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hcol]

lemma weightedStepTail_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w q : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepTail c (fun a => q a.1)=weightedStepTail w q := by
  funext t
  exact coupling_sum_fst c w (fun i => 1-max (q i) t) hrow

lemma weightedStepA_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w q : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepA c (fun a => q a.1)=weightedStepA w q := by
  unfold weightedStepA
  rw [weightedStepTail_coupling_fst c w q hrow]

lemma entropy_coupled_stationary_comparison {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w h : I → ℝ) (v g : J → ℝ) (q : I → Time) (p : J → Time)
    (hc : ∀ a, 0 ≤ c a) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hv : ∀ j, 0 ≤ v j) (hv1 : ∑ j, v j=1)
    (hrow : ∀ i, ∑ j, c (i,j)=w i) (hcol : ∀ j, ∑ i, c (i,j)=v j)
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i:ℝ) ≤ B) (hp : ∀ j, (p j:ℝ) ≤ B)
    (hstat : ∀ i, 2*h i=weightedStepA w (fun i => (q i:ℝ)) (q i)) :
    (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ) ≤
      (entropy (weightedStepTrial v p hv hv1)).toReal-∑ j, v j*g j*(p j:ℝ)+
        ∑ a, c a*|h a.1-g a.2| := by
  have hc1 : ∑ a, c a=1 := by rw [Fintype.sum_prod_type]; simp_rw [hrow]; exact hw1
  have hs := entropy_weightedStep_support c (fun a => p a.2) (fun a => q a.1)
    hc hc1 B hB0 hB1 (fun a => hp a.2) (fun a => hq a.1)
  rw [weightedStepTrial_coupling_fst c w q hc hc1 hw hw1 hrow,
    weightedStepTrial_coupling_snd c v p hc hc1 hv hv1 hcol,
    weightedStepA_coupling_fst c w (fun i => (q i:ℝ)) hrow] at hs
  have he : (∑ a, c a*((p a.2:ℝ)-(q a.1:ℝ))*weightedStepA w (fun i => (q i:ℝ)) (q a.1))/2 =
      (∑ a, c a*h a.1*(p a.2:ℝ))-(∑ i, w i*h i*(q i:ℝ)) := by
    simp only [mul_assoc]
    rw [← coupling_sum_fst c w (fun i => h i*(q i:ℝ)) hrow]
    simp only [← mul_assoc]
    rw [Finset.sum_div,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← hstat a.1]
    ring
  rw [he] at hs
  have hb : (∑ j, v j*g j*(p j:ℝ))-(∑ a, c a*h a.1*(p a.2:ℝ)) ≤
      ∑ a, c a*|h a.1-g a.2| := by
    simp only [mul_assoc]
    rw [← coupling_sum_snd c v (fun j => g j*(p j:ℝ)) hcol]
    simp only [← mul_assoc]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro a _
    have h₁ : (g a.2-h a.1)*(p a.2:ℝ) ≤ |h a.1-g a.2| := calc
      _ ≤ |g a.2-h a.1| *(p a.2:ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) (p a.2).2.1
      _ ≤ |g a.2-h a.1| *1 := mul_le_mul_of_nonneg_left (p a.2).2.2 (abs_nonneg _)
      _ = _ := by rw [mul_one,abs_sub_comm]
    have H := mul_le_mul_of_nonneg_left h₁ (hc a)
    nlinarith [H]
  linarith

lemma finiteSphericalDual_eq_stationary {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hs : ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    sInf (finiteSphericalDualValues w h hw hw1)=finiteSphericalDualObjective w h hw hw1 q := by
  apply IsLeast.csInf_eq
  refine ⟨⟨q,⟨hq,hq1⟩,rfl⟩,?_⟩
  rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
  exact stationary_finite_entropy_minimizes w h q p hw hw1 hq hp hq1 hp1 hs

theorem finiteSphericalDual_abs_sub_le {k : ℕ} (w h g : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) (hg : Monotone g) (hg0 : 0 ≤ g 0) :
    |sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)-
      sInf (finiteSphericalDualValues w g (fun i => (hw i).le) hw1)| ≤
        ∑ i, w i*|h i-g i| := by
  classical
  obtain ⟨q,hq,hq1,hsq⟩ := exists_finite_stationary_quantile w h hw hw1 hh hh0
  obtain ⟨p,hp,hp1,hsp⟩ := exists_finite_stationary_quantile w g hw hw1 hg hg0
  rw [finiteSphericalDual_eq_stationary w h q (fun i => (hw i).le) hw1 hq hq1 hsq,
    finiteSphericalDual_eq_stationary w g p (fun i => (hw i).le) hw1 hp hp1 hsp]
  let c : Fin (k+1)×Fin (k+1) → ℝ := fun a => if a.1=a.2 then w a.1 else 0
  have hc : ∀ a, 0 ≤ c a := by intro a; dsimp [c]; split_ifs; exact (hw a.1).le; rfl
  have hr : ∀ i, ∑ j, c (i,j)=w i := by intro i; simp [c]
  have he : ∀ j, ∑ i, c (i,j)=w j := by intro j; simp [c]
  let B := max (q (Fin.last k):ℝ) (p (Fin.last k):ℝ)
  have hB0 : 0 ≤ B := (q (Fin.last k)).2.1.trans (le_max_left _ _)
  have hB1 : B < 1 := max_lt hq1 hp1
  have hQ (i : Fin (k+1)) : (q i:ℝ) ≤ B :=
    (show (q i:ℝ) ≤ (q (Fin.last k):ℝ) from hq (Fin.le_last i)).trans (le_max_left _ _)
  have hP (i : Fin (k+1)) : (p i:ℝ) ≤ B :=
    (show (p i:ℝ) ≤ (p (Fin.last k):ℝ) from hp (Fin.le_last i)).trans (le_max_right _ _)
  have H := entropy_coupled_stationary_comparison c w h w g q p hc
    (fun i => (hw i).le) hw1 (fun i => (hw i).le) hw1 hr he B hB0 hB1 hQ hP hsq
  have H' := entropy_coupled_stationary_comparison c w g w h p q hc
    (fun i => (hw i).le) hw1 (fun i => (hw i).le) hw1 hr he B hB0 hB1 hP hQ hsp
  have hsum : (∑ a, c a*|h a.1-g a.2|)=∑ i, w i*|h i-g i| := by
    simp only [Fintype.sum_prod_type,c,ite_mul,zero_mul]
    simp
  have hsum' : (∑ a, c a*|g a.1-h a.2|)=∑ i, w i*|h i-g i| := by
    simp only [Fintype.sum_prod_type,c,ite_mul,zero_mul]
    simp [abs_sub_comm]
  rw [hsum] at H
  rw [hsum'] at H'
  unfold finiteSphericalDualObjective
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatGrid
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianGrid_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p v : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) :
    LipschitzWith L (gaussianGrid N p v f) := by
  apply gaussianBackward_lipschitz _ hf
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  exact hp i

lemma gaussianGrid_succ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : ℕ) (p v : Fin (N+1) → ℝ) (f : E → ℝ) :
    gaussianGrid (N+1) p v f = gaussianEntropic (stdGaussian E) (p 0) (Real.sqrt (v 0))
      (gaussianGrid N (fun i => p i.succ) (fun i => v i.succ) f) := by
  simp only [gaussianGrid,List.ofFn_succ,gaussianBackward]

lemma gaussianGrid_zero {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) :
    gaussianGrid N p (fun _ => 0) f=f := by
  induction N with
  | zero => simp [gaussianGrid,gaussianBackward]
  | succ N ih =>
    rw [gaussianGrid_succ,Real.sqrt_zero,ih (fun i => p i.succ) (fun i => hp i.succ)]
    funext x
    exact gaussianEntropic_variance_zero hf _ _

lemma gaussianGrid_absorb {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p v : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hv : ∀ i, 0 ≤ v i)
    (j : Fin N) (a : ℝ) (ha : 0 ≤ a) (hpre : ∀ i, i < j → v i=0) :
    gaussianEntropic (stdGaussian E) (p j) (Real.sqrt a) (gaussianGrid N p v f)=
      gaussianGrid N p (fun i => v i+if i=j then a else 0) f := by
  induction N with
  | zero => exact j.elim0
  | succ N ih =>
    revert hpre
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hpre
      have ht := gaussianGrid_lipschitz hf N (fun i => p i.succ) (fun i => v i.succ)
        (fun i => hp i.succ)
      rw [gaussianGrid_succ,gaussianGrid_succ]
      simp only [ite_true,Fin.succ_ne_zero,ite_false,add_zero]
      funext x
      have H := gaussianEntropic_semigroup ht (hp 0) (Real.sqrt a) (Real.sqrt (v 0)) x
      rw [Real.sq_sqrt ha,Real.sq_sqrt (hv 0),add_comm a (v 0)] at H
      exact H
    · intro hpre
      have hv0 : v 0=0 := hpre 0 (by simp [Fin.lt_def])
      have ht := gaussianGrid_lipschitz hf N (fun i => p i.succ) (fun i => v i.succ)
        (fun i => hp i.succ)
      have ht' := gaussianGrid_lipschitz hf N (fun i => p i.succ)
        (fun i => v i.succ+if i=j then a else 0) (fun i => hp i.succ)
      have H := ih (fun i => p i.succ) (fun i => v i.succ) (fun i => hp i.succ)
        (fun i => hv i.succ) j (fun i hij => hpre i.succ (Fin.succ_lt_succ_iff.mpr hij))
      rw [gaussianGrid_succ,gaussianGrid_succ]
      simp only [hv0,(Ne.symm (Fin.succ_ne_zero j)),ite_false,add_zero,Real.sqrt_zero,Fin.succ_inj]
      have e₁ : gaussianEntropic (stdGaussian E) (p 0) 0
          (gaussianGrid N (fun i => p i.succ) (fun i => v i.succ) f)=
          gaussianGrid N (fun i => p i.succ) (fun i => v i.succ) f := by
        funext x; exact gaussianEntropic_variance_zero ht _ _
      have e₂ : gaussianEntropic (stdGaussian E) (p 0) 0
          (gaussianGrid N (fun i => p i.succ) (fun i => v i.succ+if i=j then a else 0) f)=
          gaussianGrid N (fun i => p i.succ) (fun i => v i.succ+if i=j then a else 0) f := by
        funext x; exact gaussianEntropic_variance_zero ht' _ _
      rw [e₁,e₂]
      exact H

end

lemma gridVariance_nonneg {N : ℕ} (l : List (Fin N×ℝ))
    (hl : ∀ c ∈ l, 0 ≤ c.2) (i : Fin N) : 0 ≤ gridVariance l i := by
  unfold gridVariance
  apply List.sum_nonneg
  intro x hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact hl c hc
  · exact le_rfl

lemma gridVariance_below {N : ℕ} (l : List (Fin N×ℝ)) {j i : Fin N}
    (hl : ∀ c ∈ l, j ≤ c.1) (hij : i < j) : gridVariance l i=0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
  rw [ite_eq_right (ne_of_gt (hij.trans_le (hl c hc)))]

lemma gridVariance_cons {N : ℕ} (c : Fin N×ℝ) (l : List (Fin N×ℝ)) :
    gridVariance (c::l)=fun i => gridVariance l i+if i=c.1 then c.2 else 0 := by
  funext i
  simp only [gridVariance,List.map_cons,List.sum_cons]
  split_ifs <;> simp_all
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianBackward_compress {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (l : List (Fin N×ℝ))
    (hl : l.Pairwise (fun a b => a.1 ≤ b.1)) (hv : ∀ c ∈ l, 0 ≤ c.2) :
    gaussianBackward (stdGaussian E) (l.map fun c => (p c.1,Real.sqrt c.2)) f=
      gaussianGrid N p (gridVariance l) f := by
  induction l with
  | nil =>
    simp only [List.map_nil,gaussianBackward]
    exact (gaussianGrid_zero hf N p hp).symm
  | cons c l ih =>
    have hpair := List.pairwise_cons.mp hl
    have hv' := fun d hd => hv d (List.mem_cons_of_mem c hd)
    simp only [List.map_cons,gaussianBackward,ih hpair.2 hv',gridVariance_cons]
    exact gaussianGrid_absorb hf N p (gridVariance l) hp (gridVariance_nonneg l hv')
      c.1 c.2 (hv c List.mem_cons_self) (fun i hi => gridVariance_below l hpair.1 hi)

end

lemma expectedCoordinateSphereLog_stationary_covariance {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hstat : ∀ i, 2*h i = weightedStepA w (fun j => (q j:ℝ)) (q i))
    (σ : ℕ → ℝ) (v : ℝ≥0) (hv : (v:ℝ)=2*h 0)
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=2*(h i.succ-h i.castSucc)) :
    Tendsto (fun n : ℕ => expectedCoordinateSphereLog n k σ (stepCumulative w) v-h (Fin.last k)) atTop
      (𝓝 ((entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-
        ∑ i, w i*h i*(q i:ℝ))) := by
  let Q : Fin (k+1) → ℝ := fun i => q i
  let D : Fin (k+1) → ℝ := fun i => weightedStepTail w Q (Q i)
  have hm : Monotone Q := fun i j hij => hq hij
  have h0 : 0 ≤ Q 0 := (q 0).2.1
  have hmax (i : Fin (k+1)) : Q i ≤ Q (Fin.last k) := hm (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D i :=
    weightedStepTail_pos w Q (fun i => (hw i).le) hw1 hq1 hmax (hmax i)
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hroot : 2*h 0=Q 0/(D 0)^2 :=
    (hstat 0).trans (weightedStepA_root w Q hm h0)
  have hinc (i : Fin k) : 2*(h i.succ-h i.castSucc)=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) := by
    calc
      _ = weightedStepA w Q (Q i.succ)-weightedStepA w Q (Q i.castSucc) := by
        linarith [hstat i.succ,hstat i.castSucc]
      _ = _ := weightedStepA_increment w Q (fun i => (hw i).le) hw1 hm h0 hq1 i (hz0 i)
  have hh : Monotone h := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hp := div_nonneg (sub_nonneg.mpr (hm (Fin.castSucc_le_succ i)))
      (mul_pos (hD i.castSucc) (hD i.succ)).le
    rw [← hinc i] at hp
    linarith
  have hr0 : 0 ≤ 2*h 0 := by rw [hroot]; positivity
  have hr : (v:ℝ)=Q 0/(D 0)^2 := hv.trans hroot
  have hend : D (Fin.last k) = 1-Q (Fin.last k) := weightedStepTail_of_le w Q hw1 hmax
  have hgap (i : Fin k) : D i.castSucc-D i.succ=stepCumulative w i*(Q i.succ-Q i.castSucc) := by
    have he := weightedStepTail_affine w Q hm i (t := Q i.succ) ⟨hm (Fin.castSucc_le_succ i),le_rfl⟩
    change D i.succ=D i.castSucc-stepCumulative w i*(Q i.succ-Q i.castSucc) at he
    linarith
  have hσ' (i : Fin k) : (σ (k-1-i.val))^2=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) := (hσ i).trans (hinc i)
  have ht := (expectedCoordinateSphereLog_stationary_data k σ
    Q D (stepCumulative w) hz hz0 hz1 hD hend hgap hσ' v hr).sub_const (h (Fin.last k))
  have he := entropy_weightedStepTrial_toReal_finite_formula w q (fun i => (hw i).le) hw1 hq hq1 hz0
  simp only [tailIntegral_weightedStepTrial] at he
  change (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal =
    Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0) at he
  have hs := stationary_field_shift_identity w Q h hw1 hm hD hroot hinc
  have hv : Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0)+
      ((D (Fin.last k))⁻¹-1)/2-h (Fin.last k) =
      (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-∑ i, w i*h i*Q i := by
    rw [he]
    change 2*(h (Fin.last k)-∑ i, w i*h i*Q i)=(D (Fin.last k))⁻¹-1 at hs
    linarith
  rw [hv] at ht
  exact ht

lemma amplitudeCovarianceLevels_root (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) :
    2*amplitudeCovarianceLevels k σ r 0=r^2 := by unfold amplitudeCovarianceLevels; ring

lemma amplitudeCovarianceLevels_increment (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) (i : Fin k) :
    2*(amplitudeCovarianceLevels k σ r i.succ-amplitudeCovarianceLevels k σ r i.castSucc)=
      (σ (k-1-i.val))^2 := by
  have he := stepTailSum_difference (fun j : Fin k => (σ (k-1-j.val))^2) i
  unfold amplitudeCovarianceLevels
  linarith

lemma amplitudeCovarianceLevels_monotone (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) :
    Monotone (amplitudeCovarianceLevels k σ r) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have h := amplitudeCovarianceLevels_increment k σ r i
  nlinarith [sq_nonneg (σ (k-1-i.val))]

lemma amplitudeCovarianceLevels_nonneg (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) :
    0 ≤ amplitudeCovarianceLevels k σ r 0 := by
  have h := amplitudeCovarianceLevels_root k σ r
  nlinarith [sq_nonneg r]

lemma amplitudeSphereValue_tendsto {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (σ : ℕ → ℝ) (r : ℝ) :
    Tendsto (fun n : ℕ => amplitudeSphereValue n k σ (stepCumulative w) r) atTop
      (𝓝 (amplitudeSphereDual w (fun i => (hw i).le) hw1 σ r)) := by
  let h := amplitudeCovarianceLevels k σ r
  obtain ⟨q,hq,hq1,hs⟩ := exists_finite_stationary_quantile w h hw hw1
    (amplitudeCovarianceLevels_monotone k σ r) (amplitudeCovarianceLevels_nonneg k σ r)
  have hleast : IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
      (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) := by
    refine ⟨⟨q,⟨hq,hq1⟩,rfl⟩,?_⟩
    rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
    exact stationary_finite_entropy_minimizes w h q p (fun i => (hw i).le) hw1 hq hp hq1 hp1 hs
  have ht := (expectedCoordinateSphereLog_stationary_covariance w h q hw hw1 hq hq1 hs σ
    ⟨r^2,sq_nonneg r⟩ (amplitudeCovarianceLevels_root k σ r).symm
    (fun i => (amplitudeCovarianceLevels_increment k σ r i).symm)).add_const (h (Fin.last k))
  simp only [sub_add_cancel,← amplitudeSphereValue_eq] at ht
  change Tendsto _ _ (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)+h (Fin.last k)))
  rw [hleast.csInf_eq]
  exact ht

lemma finiteAmplitudeSphereValue_convex {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (n : ℕ) :
    ConvexOn ℝ Set.univ (finiteAmplitudeSphereValue n k w) := by
  refine ⟨convex_univ,?_⟩
  intro a _ b _ c d hc hd hcd
  have he : finiteAmplitudeIncrement k (c • a+d • b)=
      c • finiteAmplitudeIncrement k a+d • finiteAmplitudeIncrement k b := by
    funext j
    unfold finiteAmplitudeIncrement
    by_cases hj : j < k
    · simp [hj,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    · simp [hj,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  simpa only [finiteAmplitudeSphereValue,he,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
    amplitudeSphereValue_convex n k (stepCumulative w) (stepCumulative_strictMono w hw)
      (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
      (finiteAmplitudeIncrement k a) (finiteAmplitudeIncrement k b) (a (Fin.last k))
      (b (Fin.last k)) hc hd hcd

lemma finiteAmplitudeSphereValue_nonneg {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (n : ℕ) (a : Fin (k+1) → ℝ) :
    0 ≤ finiteAmplitudeSphereValue n k w a :=
  integral_nonneg_of_ae (amplitudeSphereLog_nonneg n k _ _ (stepCumulative_strictMono w hw)
    (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1) _)

lemma finiteAmplitudeSphereValue_tendsto {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (a : Fin (k+1) → ℝ) :
    Tendsto (fun n : ℕ => finiteAmplitudeSphereValue n k w a) atTop
      (𝓝 (finiteAmplitudeSphereDual w (fun i => (hw i).le) hw1 a)) :=
  amplitudeSphereValue_tendsto w hw hw1 _ _

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ConvexUniform
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma equicontinuous_of_convex_nonneg_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℕ → E → ℝ) (f : E → ℝ)
    (hcv : ∀ n, ConvexOn ℝ Set.univ (F n)) (h0 : ∀ n x, 0 ≤ F n x)
    (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) : Equicontinuous F := by
  let G : E → ℝ := fun x => sSup (Set.range (fun n => F n x))
  have hb (x : E) : BddAbove (Set.range (fun n => F n x)) := (ht x).bddAbove_range
  have hle (n : ℕ) (x : E) : F n x ≤ G x := le_csSup (hb x) ⟨n,rfl⟩
  have hG : ConvexOn ℝ Set.univ G := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb' hab
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n,rfl⟩
    exact ((hcv n).2 trivial trivial ha hb' hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hle n x) ha)
        (mul_le_mul_of_nonneg_left (hle n y) hb'))
  have hGc : Continuous G := continuousOn_univ.mp (hG.continuousOn isOpen_univ)
  intro x
  have hn : {y : E | G y < G x+1} ∈ 𝓝 x :=
    (hGc.continuousAt).preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨r,hr,hrG⟩ := Metric.mem_nhds_iff.mp hn
  let K : ℝ≥0 := (2*(G x+1)/(r/2)).toNNReal
  have hLip (n : ℕ) : LipschitzOnWith K (F n) (ball x (r-r/2)) := by
    apply ((hcv n).subset (Set.subset_univ _) (convex_ball _ _)).lipschitzOnWith_of_abs_le
      (half_pos hr)
    intro y hy
    rw [abs_of_nonneg (h0 n y)]
    exact (hle n y).trans (hrG hy).le
  apply Metric.equicontinuousAt_of_continuity_modulus (fun y => (K:ℝ)*dist x y)
    (by
      have hc : Continuous (fun y : E => (K:ℝ)*dist x y) := by fun_prop
      simpa only [dist_self,mul_zero] using hc.tendsto x) F
  filter_upwards [ball_mem_nhds x (by linarith : 0 < r-r/2)] with y hy n
  have hx : x ∈ ball x (r-r/2) := by rw [mem_ball,dist_self]; linarith
  exact (hLip n).dist_le_mul x hx y hy

lemma tendstoUniformlyOn_of_convex_nonneg_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℕ → E → ℝ) (f : E → ℝ)
    (hcv : ∀ n, ConvexOn ℝ Set.univ (F n)) (h0 : ∀ n x, 0 ≤ F n x)
    (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {K : Set E} (hK : IsCompact K) : TendstoUniformlyOn F f atTop K := by
  have he := equicontinuous_of_convex_nonneg_tendsto F f hcv h0 ht
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he' : Equicontinuous (fun n (x : K) => F n x) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := Metric.equicontinuousAt_iff.mp (he (x:E)) ε hε
    exact ⟨δ,hδ,fun y hy n => hd (y:E) hy n⟩
  have hp : Tendsto (fun n (x : K) => F n x) atTop (𝓝 (fun x : K => f x)) :=
    tendsto_pi_nhds.mpr (fun x => ht x)
  have hu := (he'.tendsto_uniformFun_iff_pi atTop (fun x : K => f x)).mpr hp
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

lemma finiteAmplitudeSphereValue_uniform {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) {K : Set (Fin (k+1) → ℝ)}
    (hK : IsCompact K) : TendstoUniformlyOn (fun n => finiteAmplitudeSphereValue n k w)
      (finiteAmplitudeSphereDual w (fun i => (hw i).le) hw1) atTop K :=
  tendstoUniformlyOn_of_convex_nonneg_tendsto _ _ (finiteAmplitudeSphereValue_convex w hw hw1)
    (finiteAmplitudeSphereValue_nonneg w hw hw1) (finiteAmplitudeSphereValue_tendsto w hw hw1) hK

lemma fieldAmplitudes_last (k : ℕ) (h : Fin (k+1) → ℝ) :
    fieldAmplitudes k h (Fin.last k)=Real.sqrt (2*h 0) := by
  simp [fieldAmplitudes]

lemma fieldAmplitudes_increment (k : ℕ) (h : Fin (k+1) → ℝ) :
    finiteAmplitudeIncrement k (fieldAmplitudes k h)=stepFieldIncrement k h := by
  funext j
  by_cases hj : j < k
  · simp [finiteAmplitudeIncrement,fieldAmplitudes,hj]
  · simp [finiteAmplitudeIncrement,stepFieldIncrement,hj]

lemma fieldAmplitudes_continuous (k : ℕ) : Continuous (fieldAmplitudes k) := by
  apply continuous_pi
  intro i
  unfold fieldAmplitudes
  split_ifs
  · unfold stepFieldIncrement
    split_ifs
    fun_prop
  · fun_prop

lemma amplitudeCovarianceLevels_fieldAmplitudes (k : ℕ) (h : Fin (k+1) → ℝ)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    amplitudeCovarianceLevels k (finiteAmplitudeIncrement k (fieldAmplitudes k h))
      (fieldAmplitudes k h (Fin.last k))=h := by
  rw [fieldAmplitudes_increment,fieldAmplitudes_last]
  funext i
  induction i using Fin.induction with
  | zero =>
    have hr := amplitudeCovarianceLevels_root k (stepFieldIncrement k h) (Real.sqrt (2*h 0))
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hh0)] at hr
    linarith
  | succ i ih =>
    have hi := amplitudeCovarianceLevels_increment k (stepFieldIncrement k h) (Real.sqrt (2*h 0)) i
    rw [stepFieldIncrement_sq k h hh i,ih] at hi
    linarith

lemma finiteAmplitudeSphereDual_fieldAmplitudes {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    finiteAmplitudeSphereDual w hw hw1 (fieldAmplitudes k h)=
      sInf (finiteSphericalDualValues w h hw hw1)+h (Fin.last k) := by
  unfold finiteAmplitudeSphereDual amplitudeSphereDual
  rw [amplitudeCovarianceLevels_fieldAmplitudes k h hh hh0]

lemma finiteAmplitudeSphereValue_fieldAmplitudes (n k : ℕ) (w h : Fin (k+1) → ℝ)
    (hh0 : 0 ≤ h 0) :
    finiteAmplitudeSphereValue n k w (fieldAmplitudes k h)=finiteSphericalFieldValue n k w h+h (Fin.last k) := by
  unfold finiteAmplitudeSphereValue
  rw [fieldAmplitudes_increment,fieldAmplitudes_last,amplitudeSphereValue_eq]
  have hv : (⟨(Real.sqrt (2*h 0))^2,sq_nonneg _⟩ : ℝ≥0)=Real.toNNReal (2*h 0) := by
    apply NNReal.coe_injective
    change (Real.sqrt (2*h 0))^2=(Real.toNNReal (2*h 0) : ℝ)
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hh0),
      Real.coe_toNNReal _ (mul_nonneg (by norm_num) hh0)]
  rw [hv,finiteSphericalFieldValue,sub_add_cancel]

theorem finiteSphericalFieldValue_compact_uniform {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) {K : Set (Fin (k+1) → ℝ)}
    (hK : IsCompact K) (hfield : ∀ h ∈ K, Monotone h ∧ 0 ≤ h 0) :
    TendstoUniformlyOn (fun n h => finiteSphericalFieldValue n k w h)
      (fun h => sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)) atTop K := by
  have hu := finiteAmplitudeSphereValue_uniform w hw hw1 (hK.image (fieldAmplitudes_continuous k))
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn h hh
  have ht := hn (fieldAmplitudes k h) ⟨h,hh,rfl⟩
  rw [finiteAmplitudeSphereValue_fieldAmplitudes n k w h (hfield h hh).2,
    finiteAmplitudeSphereDual_fieldAmplitudes w h (fun i => (hw i).le) hw1
      (hfield h hh).1 (hfield h hh).2,dist_add_right] at ht
  exact ht

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldWord
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma cascadeHeatWord_eq_ofFn (σ : ℕ → ℝ) (k : ℕ) (z : Fin k → ℝ) :
    cascadeHeatWord σ k z=List.ofFn (fun i => (z i,σ (k-1-i.val))) := by
  induction k with
  | zero => simp [cascadeHeatWord]
  | succ k ih =>
    rw [cascadeHeatWord,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero]
    congr 1
    congr 1
    funext i
    have he : k-1-i.val=k+1-1-i.succ.val := by simp only [Fin.val_succ]; omega
    simp only [he,Nat.add_sub_cancel]

lemma fieldVariances_nonneg (k : ℕ) (h : Fin (k+1) → ℝ)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) (i : Fin (k+1)) : 0 ≤ fieldVariances k h i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact mul_nonneg (by norm_num) hh0
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hh (Fin.castSucc_le_succ i)))

lemma fieldVariances_sum (k : ℕ) (h : Fin (k+1) → ℝ) :
    (∑ i, fieldVariances k h i)=2*h (Fin.last k) := by
  rw [Fin.sum_univ_succ]
  simp only [fieldVariances,Fin.cases_zero,Fin.cases_succ]
  rw [← Finset.mul_sum,finite_sum_successive_differences]
  ring

lemma fieldExponents_nonneg {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i)
    (i : Fin (k+1)) : 0 ≤ fieldExponents w i := by
  refine Fin.cases (by rfl) (fun j => (stepCumulative_pos w hw j).le) i

lemma fieldExponents_lt_one {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i=1) (i : Fin (k+1)) : fieldExponents w i < 1 := by
  refine Fin.cases (by norm_num [fieldExponents]) (fun j => stepCumulative_lt_one w hw hw1 j) i

lemma fieldExponents_strictMono {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) :
    StrictMono (fieldExponents w) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases (by simp) (fun j _ => stepCumulative_pos w hw j) j
  · intro j
    refine Fin.cases (by simp) (fun j hij => stepCumulative_strictMono w hw (Fin.succ_lt_succ_iff.mp hij)) j

lemma stepFieldIncrement_reverse (k : ℕ) (h : Fin (k+1) → ℝ) (i : Fin k) :
    stepFieldIncrement k h (k-1-i.val)=Real.sqrt (2*(h i.succ-h i.castSucc)) := by
  have hi : k-1-i.val < k := by omega
  have he : Fin.rev (⟨k-1-i.val,hi⟩ : Fin k)=i := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [stepFieldIncrement,dite_eq_left hi,he]

lemma fieldWord_eq (k : ℕ) (w h : Fin (k+1) → ℝ) :
    List.ofFn (fun i => (fieldExponents w i,Real.sqrt (fieldVariances k h i)))=
      (0,Real.sqrt (2*h 0))::cascadeHeatWord (stepFieldIncrement k h) k (stepCumulative w) := by
  rw [List.ofFn_succ,cascadeHeatWord_eq_ofFn]
  simp only [fieldExponents,fieldVariances,Fin.cases_zero,Fin.cases_succ,stepFieldIncrement_reverse]

lemma finiteSphericalFieldValue_eq_heat {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) (n : ℕ) :
    finiteSphericalFieldValue n k w h=sphericalHeatValue n
      (List.ofFn fun i => (fieldExponents w i,Real.sqrt (fieldVariances k h i))) := by
  have hs : ((List.ofFn fun i => (fieldExponents w i,Real.sqrt (fieldVariances k h i))).map
      fun c => c.2^2).sum=2*h (Fin.last k) := by
    rw [List.map_ofFn,List.sum_ofFn]
    change (∑ i, (Real.sqrt (fieldVariances k h i))^2)=_
    simp only [Real.sq_sqrt (fieldVariances_nonneg k h hh hh0 _)]
    exact fieldVariances_sum k h
  have ha := finiteAmplitudeSphereValue_fieldAmplitudes n k w h hh0
  unfold finiteAmplitudeSphereValue at ha
  rw [fieldAmplitudes_increment,fieldAmplitudes_last,
    amplitudeSphereValue_eq_backward n k (stepFieldIncrement k h) (stepCumulative w)
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
      (stepCumulative_lt_one w hw hw1)] at ha
  rw [sphericalHeatValue,hs,fieldWord_eq]
  linarith

lemma varianceLevels_zero {k : ℕ} (v : Fin (k+1) → ℝ) : varianceLevels v 0=v 0/2 := by
  simp [varianceLevels]

lemma varianceLevels_increment {k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin k) :
    varianceLevels v i.succ-varianceLevels v i.castSucc=v i.succ/2 := by
  unfold varianceLevels
  rw [← sub_div,← Finset.sum_sub_distrib]
  congr 1
  have he : (fun j : Fin (k+1) => (if j ≤ i.succ then v j else 0)-
      (if j ≤ i.castSucc then v j else 0))=fun j => if j=i.succ then v j else 0 := by
    funext j
    by_cases h₁ : j ≤ i.castSucc
    · have h₂ : j ≤ i.succ := h₁.trans (Fin.castSucc_le_succ i)
      have h₃ : j ≠ i.succ := by intro e; subst j; simp [Fin.le_def,Fin.val_succ] at h₁
      simp [h₁,h₂,h₃]
    · by_cases h₂ : j ≤ i.succ
      · have hj : j=i.succ := by apply Fin.ext; simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ] at *; omega
        simp [hj]
      · have h₃ : j ≠ i.succ := by intro e; subst j; exact h₂ le_rfl
        simp [h₁,h₂,h₃]
  rw [he]
  simp

lemma fieldVariances_varianceLevels {k : ℕ} (v : Fin (k+1) → ℝ) :
    fieldVariances k (varianceLevels v)=v := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [fieldVariances,varianceLevels_zero]; ring
  · simp [fieldVariances,varianceLevels_increment]; ring

lemma varianceLevels_monotone {k : ℕ} (v : Fin (k+1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    Monotone (varianceLevels v) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have h := varianceLevels_increment v i
  linarith [hv i.succ]

lemma varianceLevels_nonneg {k : ℕ} (v : Fin (k+1) → ℝ) (hv : ∀ i, 0 ≤ v i)
    (i : Fin (k+1)) : 0 ≤ varianceLevels v i := by
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> first | exact hv j | rfl

lemma gaussianGrid_spherical_last (n k : ℕ) (p v : Fin (k+2) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hv : 0 ≤ v (Fin.last (k+1))) (hpl : p (Fin.last (k+1))=1) :
    gaussianGrid (k+2) p v (logSphericalExp n (Real.sqrt (n+1:ℕ)))=
      fun x => gaussianGrid (k+1) (fun i => p i.castSucc) (fun i => v i.castSucc)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) x+(n+1:ℕ)*v (Fin.last (k+1))/2 := by
  unfold gaussianGrid
  rw [List.ofFn_succ_last,gaussianBackward_append]
  simp only [gaussianBackward]
  have he : gaussianEntropic (stdGaussian (Spin (n+1))) (p (Fin.last (k+1)))
      (Real.sqrt (v (Fin.last (k+1)))) (logSphericalExp n (Real.sqrt (n+1:ℕ)))=
        fun x => logSphericalExp n (Real.sqrt (n+1:ℕ)) x+(n+1:ℕ)*v (Fin.last (k+1))/2 := by
    funext x
    rw [hpl,gaussianEntropic_logSphericalExp_one,Real.sq_sqrt (by positivity),Real.sq_sqrt hv]
  rw [he]
  apply gaussianBackward_add_const _ (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ)))
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  exact hp i.castSucc

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformGrid
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma uniformExponents_nonneg (k : ℕ) (i : Fin (k+2)) : 0 ≤ uniformExponents k i := by
  unfold uniformExponents
  positivity

lemma uniformExponents_last (k : ℕ) : uniformExponents k (Fin.last (k+1))=1 := by
  simp only [uniformExponents,Fin.val_last]
  exact div_self (by positivity)

lemma stepCumulative_uniformWeights (k : ℕ) (i : Fin k) :
    stepCumulative (uniformWeights k) i=(i.val+1:ℕ)/(k+1:ℕ) := by
  unfold stepCumulative uniformWeights
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun j : Fin (k+1) => j ≤ i.castSucc)=Finset.Iic i.castSucc := by
    ext j; simp
  rw [he,Finset.sum_const,Fin.card_Iic]
  simp only [Fin.val_castSucc,nsmul_eq_mul]
  push_cast
  ring

lemma uniformExponents_castSucc (k : ℕ) (i : Fin (k+1)) :
    uniformExponents k i.castSucc=fieldExponents (uniformWeights k) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [uniformExponents,fieldExponents]
  · simp [uniformExponents,fieldExponents,stepCumulative_uniformWeights]

lemma sphericalGridValue_eq (n k : ℕ) (v : Fin (k+2) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    sphericalGridValue n k v=finiteSphericalFieldValue n k (uniformWeights k)
      (varianceLevels (fun i => v i.castSucc)) := by
  rw [finiteSphericalFieldValue_eq_heat (uniformWeights k) _ (uniformWeights_pos k)
    (uniformWeights_sum k) (varianceLevels_monotone _ (fun i => hv i.castSucc))
    (varianceLevels_nonneg _ (fun i => hv i.castSucc) 0),fieldVariances_varianceLevels]
  unfold sphericalGridValue sphericalHeatValue
  have hs : ((List.ofFn fun i => (uniformExponents k i,Real.sqrt (v i))).map fun c => c.2^2).sum=
      (∑ i : Fin (k+1), v i.castSucc)+v (Fin.last (k+1)) := by
    rw [List.map_ofFn,List.sum_ofFn]
    change (∑ i, (Real.sqrt (v i))^2)=_
    simp only [Real.sq_sqrt (hv _)]
    exact Fin.sum_univ_castSucc v
  have hs' : ((List.ofFn fun i => (fieldExponents (uniformWeights k) i,
      Real.sqrt (v (i : Fin (k+1)).castSucc))).map fun c => c.2^2).sum=∑ i : Fin (k+1), v i.castSucc := by
    rw [List.map_ofFn,List.sum_ofFn]
    change (∑ i : Fin (k+1), (Real.sqrt (v i.castSucc))^2)=_
    simp only [Real.sq_sqrt (hv _)]
  rw [hs,hs']
  change gaussianGrid (k+2) (uniformExponents k) v _ 0/(n+1:ℕ)-_= _
  rw [gaussianGrid_spherical_last n k _ _ (uniformExponents_nonneg k)
    (hv _) (uniformExponents_last k)]
  simp only [uniformExponents_castSucc]
  unfold gaussianGrid
  have hn : (n+1:ℕ) ≠ (0:ℝ) := by positivity
  field_simp [hn]
  ring

lemma varianceLevels_continuous (k : ℕ) : Continuous (varianceLevels (k := k)) := by
  apply continuous_pi
  intro i
  unfold varianceLevels
  apply Continuous.div_const
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

lemma sphericalGridValue_compact_uniform (k : ℕ) (H : ℝ) :
    TendstoUniformlyOn (fun n => sphericalGridValue n k) (sphericalGridDual k) atTop
      (Icc (fun _ => 0) (fun _ => H)) := by
  let T : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ) := fun v => varianceLevels (fun i => v i.castSucc)
  have hT : Continuous T := (varianceLevels_continuous k).comp (by fun_prop)
  have hK : IsCompact (T '' Icc (fun _ => 0) (fun _ => H)) := isCompact_Icc.image hT
  have hfield : ∀ h ∈ T '' Icc (fun _ => 0) (fun _ => H), Monotone h ∧ 0 ≤ h 0 := by
    rintro h ⟨v,hv,rfl⟩
    exact ⟨varianceLevels_monotone _ (fun i => hv.1 i.castSucc),
      varianceLevels_nonneg _ (fun i => hv.1 i.castSucc) 0⟩
  have hu := finiteSphericalFieldValue_compact_uniform (uniformWeights k)
    (uniformWeights_pos k) (uniformWeights_sum k) hK hfield
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn v hv
  rw [sphericalGridValue_eq n k v (fun i => hv.1 i)]
  exact hn (T v) ⟨v,hv,rfl⟩

lemma gridVariance_weighted_sum {N : ℕ} (l : List (Fin N×ℝ)) (g : Fin N → ℝ) :
    (∑ i, g i*gridVariance l i)=(l.map fun c => g c.1*c.2).sum := by
  induction l with
  | nil => simp [gridVariance]
  | cons c l ih =>
    rw [gridVariance_cons]
    simp only [mul_add,Finset.sum_add_distrib,ih,List.map_cons,List.sum_cons]
    simp only [mul_ite,mul_zero]
    simp [add_comm]

lemma gridVariance_sum {N : ℕ} (l : List (Fin N×ℝ)) :
    (∑ i, gridVariance l i)=(l.map Prod.snd).sum := by
  simpa only [one_mul] using gridVariance_weighted_sum l (fun _ => 1)

lemma sphericalGridValue_compress (n k : ℕ) (l : List (Fin (k+2)×ℝ))
    (hl : l.Pairwise (fun a b => a.1 ≤ b.1)) (hv : ∀ c ∈ l, 0 ≤ c.2) :
    sphericalHeatValue n (l.map fun c => (uniformExponents k c.1,Real.sqrt c.2))=
      sphericalGridValue n k (gridVariance l) := by
  unfold sphericalHeatValue sphericalGridValue
  unfold sphericalHeatValue
  rw [gaussianBackward_compress (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ)))
    (k+2) (uniformExponents k) (uniformExponents_nonneg k) l hl hv]
  congr 1
  rw [List.map_ofFn,List.sum_ofFn,List.map_map]
  change (l.map fun c => (Real.sqrt c.2)^2).sum/2=(∑ i, (Real.sqrt (gridVariance l i))^2)/2
  simp only [Real.sq_sqrt (gridVariance_nonneg l hv _)]
  rw [gridVariance_sum]
  congr 2
  apply List.map_congr_left
  intro c hc
  exact Real.sq_sqrt (hv c hc)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GridGap
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

lemma varianceLevels_gridVariance {k : ℕ} (l : List (Fin (k+2)×ℝ)) (i : Fin (k+1)) :
    varianceLevels (fun j => gridVariance l j.castSucc) i =
      (l.map fun c => if c.1 ≤ i.castSucc then c.2 else 0).sum/2 := by
  unfold varianceLevels
  congr 1
  have H := gridVariance_weighted_sum l (fun j => if j ≤ i.castSucc then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul] at H
  rw [Fin.sum_univ_castSucc] at H
  simpa only [Fin.castSucc_le_castSucc_iff,ite_eq_right (not_le.mpr (Fin.castSucc_lt_last i)),add_zero] using H

lemma grid_prefix_step_gap {k N : ℕ} (A B : Fin N → Fin (k+2)) (v : Fin N → ℝ)
    (hv : ∀ r, 0 ≤ v r) (hAB : ∀ r, A r ≤ B r)
    (hBA : ∀ r, (B r).val ≤ (A r).val+1) (i : Fin (k+1)) :
    let hA := varianceLevels (fun j => gridVariance (List.ofFn fun r => (A r,v r)) j.castSucc)
    let hB := varianceLevels (fun j => gridVariance (List.ofFn fun r => (B r,v r)) j.castSucc)
    0 ≤ hA i-hB i ∧ hA i-hB i ≤
      gridVariance (List.ofFn fun r => (A r,v r)) i.castSucc/2 := by
  dsimp only
  rw [varianceLevels_gridVariance,varianceLevels_gridVariance]
  simp only [gridVariance,List.map_ofFn,List.sum_ofFn]
  rw [← sub_div,← Finset.sum_sub_distrib]
  have H (r : Fin N) :
      0 ≤ (if A r ≤ i.castSucc then v r else 0)-(if B r ≤ i.castSucc then v r else 0) ∧
      (if A r ≤ i.castSucc then v r else 0)-(if B r ≤ i.castSucc then v r else 0) ≤
        if A r=i.castSucc then v r else 0 := by
    by_cases ha : A r ≤ i.castSucc
    · by_cases hb : B r ≤ i.castSucc
      · simp only [ite_eq_left ha,ite_eq_left hb,sub_self]
        constructor
        · rfl
        · split_ifs <;> first | exact hv r | rfl
      · have he : A r=i.castSucc := by
          apply Fin.ext
          have h₁ := hBA r
          have h₂ : (A r).val ≤ i.val := ha
          have h₃ : i.val < (B r).val := lt_of_not_ge hb
          omega
        simp [hb,he,hv r]
    · have hb : ¬B r ≤ i.castSucc := fun hb => ha ((hAB r).trans hb)
      have he : A r ≠ i.castSucc := fun he => ha he.le
      simp [ha,hb,he]
  exact ⟨div_nonneg (Finset.sum_nonneg (fun r _ => (H r).1)) (by norm_num),
    div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => (H r).2)) (by norm_num)⟩

lemma grid_step_weighted_gap {k N : ℕ} (A B : Fin N → Fin (k+2)) (v : Fin N → ℝ)
    (hv : ∀ r, 0 ≤ v r) (hAB : ∀ r, A r ≤ B r)
    (hBA : ∀ r, (B r).val ≤ (A r).val+1) :
    (∑ i, uniformWeights k i *
      |varianceLevels (fun j => gridVariance (List.ofFn fun r => (A r,v r)) j.castSucc) i-
       varianceLevels (fun j => gridVariance (List.ofFn fun r => (B r,v r)) j.castSucc) i|) ≤
      (∑ r, v r)/(2*(k+1:ℕ)) := by
  have hV : ∀ c ∈ List.ofFn (fun r => (A r,v r)), 0 ≤ c.2 := by
    intro c hc; obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hc; exact hv r
  calc
    _ ≤ ∑ i : Fin (k+1), uniformWeights k i *
        (gridVariance (List.ofFn fun r => (A r,v r)) i.castSucc/2) := by
      apply Finset.sum_le_sum
      intro i _
      have H := grid_prefix_step_gap A B v hv hAB hBA i
      rw [abs_of_nonneg H.1]
      exact mul_le_mul_of_nonneg_left H.2 (uniformWeights_pos k i).le
    _ = (∑ i : Fin (k+1), gridVariance (List.ofFn fun r => (A r,v r)) i.castSucc)/(2*(k+1:ℕ)) := by
      simp only [uniformWeights]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (∑ i, gridVariance (List.ofFn fun r => (A r,v r)) i)/(2*(k+1:ℕ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [Fin.sum_univ_castSucc (gridVariance (List.ofFn fun r => (A r,v r)))]
      exact le_add_of_nonneg_right (gridVariance_nonneg _ hV _)
    _ = _ := by rw [gridVariance_sum,List.map_ofFn,List.sum_ofFn]; rfl

lemma sphericalGridDual_step_gap {k N : ℕ} (A B : Fin N → Fin (k+2)) (v : Fin N → ℝ)
    (hv : ∀ r, 0 ≤ v r) (hAB : ∀ r, A r ≤ B r)
    (hBA : ∀ r, (B r).val ≤ (A r).val+1) :
    |sphericalGridDual k (gridVariance (List.ofFn fun r => (A r,v r)))-
     sphericalGridDual k (gridVariance (List.ofFn fun r => (B r,v r)))| ≤
      (∑ r, v r)/(2*(k+1:ℕ)) := by
  have hVA : ∀ i, 0 ≤ gridVariance (List.ofFn fun r => (A r,v r)) i := by
    apply gridVariance_nonneg
    intro c hc; obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hc; exact hv r
  have hVB : ∀ i, 0 ≤ gridVariance (List.ofFn fun r => (B r,v r)) i := by
    apply gridVariance_nonneg
    intro c hc; obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hc; exact hv r
  exact (finiteSphericalDual_abs_sub_le (uniformWeights k) _ _ (uniformWeights_pos k)
    (uniformWeights_sum k)
    (varianceLevels_monotone _ (fun i => hVA i.castSucc))
    (varianceLevels_nonneg _ (fun i => hVA i.castSucc) 0)
    (varianceLevels_monotone _ (fun i => hVB i.castSucc))
    (varianceLevels_nonneg _ (fun i => hVB i.castSucc) 0)).trans
    (grid_step_weighted_gap A B v hv hAB hBA)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformQuantileCells
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma uniformQuantileGrid_last (n : ℕ) : uniformQuantileGrid n (Fin.last (n+1))=1 := by
  apply Subtype.ext
  change ((n+1:ℕ):ℝ)/(n+1)=1
  push_cast
  exact div_self (by positivity)

lemma uniformQuantileCell_mono (n : ℕ) : Monotone (uniformQuantileCell n) := by
  intro u v huv
  change min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n ≤ min ⌊(n+1:ℝ)*(v:ℝ)⌋₊ n
  exact min_le_min_right _ (Nat.floor_mono (mul_le_mul_of_nonneg_left (show (u:ℝ)≤v from huv) (by positivity)))

lemma uniformQuantileCell_floor {n : ℕ} {u : Time} (hu : (u:ℝ)<1) :
    (uniformQuantileCell n u).val=⌊(n+1:ℝ)*(u:ℝ)⌋₊ := by
  change min _ n=_
  apply min_eq_left
  have hf : ⌊(n+1:ℝ)*(u:ℝ)⌋₊<n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) u.2.1)]
    push_cast
    nlinarith
  omega

lemma uniformQuantileCell_bounds (n : ℕ) (u : Time) :
    uniformQuantileGrid n (uniformQuantileCell n u).castSucc≤u ∧
      u≤uniformQuantileGrid n (uniformQuantileCell n u).succ := by
  by_cases hu : (u:ℝ)<1
  · have he := uniformQuantileCell_floor (n:=n) hu
    constructor
    · change ((uniformQuantileCell n u).val:ℝ)/(n+1)≤u
      rw [he,div_le_iff₀ (by positivity)]
      simpa only [mul_comm] using Nat.floor_le (mul_nonneg (show (0:ℝ)≤(n:ℝ)+1 by positivity) u.2.1)
    · change (u:ℝ)≤((_ : ℕ):ℝ)/(n+1)
      rw [Fin.val_succ,he,le_div_iff₀ (by positivity)]
      push_cast
      simpa only [mul_comm] using (Nat.lt_floor_add_one ((n+1:ℝ)*(u:ℝ))).le
  · have he : u=1 := Subtype.ext (le_antisymm u.2.2 (le_of_not_gt hu))
    subst u
    have hcell : uniformQuantileCell n 1=Fin.last n := by
      apply Fin.ext
      change min ⌊(n+1:ℝ)*1⌋₊ n=n
      rw [mul_one,show (n:ℝ)+1=((n+1:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast]
      omega
    rw [hcell,Fin.succ_last,uniformQuantileGrid_last]
    exact ⟨le_top,le_rfl⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavitySphericalGrid
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]
lemma gaussianBackward_label_mono_parameters {I : Type*} {f : E→ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (l : List (I×ℝ)) (a b : I→ℝ)
    (ha : ∀ c∈l,0≤a c.1) (hab : ∀ c∈l,a c.1≤b c.1) :
    ∀ x,gaussianBackward μ (l.map fun c=>(a c.1,c.2)) f x≤
      gaussianBackward μ (l.map fun c=>(b c.1,c.2)) f x := by
  have hb : ∀ c∈l,0≤b c.1:=fun c hc=>(ha c hc).trans (hab c hc)
  induction l with
  | nil => intro x; rfl
  | cons c l ih =>
    have ha':=fun d hd=>ha d (List.mem_cons_of_mem c hd)
    have hb':=fun d hd=>hb d (List.mem_cons_of_mem c hd)
    have hab':=fun d hd=>hab d (List.mem_cons_of_mem c hd)
    have hla : LipschitzWith L (gaussianBackward μ (l.map fun d=>(a d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩:=List.mem_map.mp hd
      exact ha' e he
    have hlb : LipschitzWith L (gaussianBackward μ (l.map fun d=>(b d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩:=List.mem_map.mp hd
      exact hb' e he
    intro x
    simp only [List.map_cons,gaussianBackward]
    exact (gaussianEntropic_mono_parameter μ hla c.2 x (hab c List.mem_cons_self)).trans
      (gaussianEntropic_mono μ hla hlb (hb c List.mem_cons_self) c.2 (ih ha' hab' hb') x)
end

lemma sphericalHeatValue_ofFn_mono_parameters (n N : ℕ) (a b σ : Fin N→ℝ)
    (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i) :
    sphericalHeatValue n (List.ofFn fun i=>(a i,σ i))≤
      sphericalHeatValue n (List.ofFn fun i=>(b i,σ i)) := by
  have hm:=gaussianBackward_label_mono_parameters (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ)))
    (List.ofFn fun i=>(i,σ i)) a b
    (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact ha i)
    (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact hab i) 0
  simp only [List.map_ofFn,Function.comp_def] at hm
  unfold sphericalHeatValue
  simp only [List.map_ofFn,Function.comp_def]
  exact sub_le_sub_right (div_le_div_of_nonneg_right hm (by positivity)) _

theorem finiteSphericalFieldValue_grid_bracket {d : ℕ} (w h : Fin (d+1)→ℝ)
    (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1) (hh : Monotone h) (hh0 : 0≤h 0)
    (H : ℝ) (hhH : h (Fin.last d)≤H) (k : ℕ) :
    ∃ v u : Fin (k+2)→ℝ,
      v∈Icc (fun _=>0) (fun _=>2*H) ∧ u∈Icc (fun _=>0) (fun _=>2*H) ∧
      (∀ n,sphericalGridValue n k v≤finiteSphericalFieldValue n d w h ∧
        finiteSphericalFieldValue n d w h≤ sphericalGridValue n k u) ∧
      |sphericalGridDual k v-sphericalGridDual k u|≤H/(k+1:ℕ) := by
  let e : Fin (d+1)→Time:=fun i=>⟨fieldExponents w i,fieldExponents_nonneg w hw i,
    (fieldExponents_lt_one w hw hw1 i).le⟩
  let A : Fin (d+1)→Fin (k+2):=fun i=>(uniformQuantileCell k (e i)).castSucc
  let B : Fin (d+1)→Fin (k+2):=fun i=>(uniformQuantileCell k (e i)).succ
  let V:=fieldVariances d h
  let v:=gridVariance (List.ofFn fun i=>(A i,V i))
  let u:=gridVariance (List.ofFn fun i=>(B i,V i))
  have hV : ∀ i,0≤V i:=fieldVariances_nonneg d h hh hh0
  have he : Monotone e:=(fieldExponents_strictMono w hw).monotone
  have hA : Monotone A:=fun i j hij=>Fin.castSucc_le_castSucc_iff.mpr (uniformQuantileCell_mono k (he hij))
  have hB : Monotone B:=fun i j hij=>Fin.succ_le_succ_iff.mpr (uniformQuantileCell_mono k (he hij))
  have hvn : ∀ i,0≤v i:=fun i=>gridVariance_nonneg _ (by
    intro c hc; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hc; exact hV j) i
  have hun : ∀ i,0≤u i:=fun i=>gridVariance_nonneg _ (by
    intro c hc; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hc; exact hV j) i
  have hvsum : (∑ i,v i)=2*h (Fin.last d) := by
    rw [gridVariance_sum,List.map_ofFn,List.sum_ofFn]; exact fieldVariances_sum d h
  have husum : (∑ i,u i)=2*h (Fin.last d) := by
    rw [gridVariance_sum,List.map_ofFn,List.sum_ofFn]; exact fieldVariances_sum d h
  refine ⟨v,u,⟨hvn,?_⟩,⟨hun,?_⟩,?_,?_⟩
  · intro i
    calc
      v i≤∑ j,v j:=Finset.single_le_sum (fun j _=>hvn j) (Finset.mem_univ i)
      _≤2*H:=by rw [hvsum]; linarith
  · intro i
    calc
      u i≤∑ j,u j:=Finset.single_le_sum (fun j _=>hun j) (Finset.mem_univ i)
      _≤2*H:=by rw [husum]; linarith
  · intro n
    have hlo:=sphericalGridValue_compress n k (List.ofFn fun i=>(A i,V i))
      (List.pairwise_ofFn.mpr (fun i j hij=>hA hij.le))
      (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact hV i)
    have hup:=sphericalGridValue_compress n k (List.ofFn fun i=>(B i,V i))
      (List.pairwise_ofFn.mpr (fun i j hij=>hB hij.le))
      (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact hV i)
    simp only [List.map_ofFn,Function.comp_def] at hlo hup
    rw [←hlo,←hup,finiteSphericalFieldValue_eq_heat w h hw hw1 hh hh0]
    constructor
    · apply sphericalHeatValue_ofFn_mono_parameters
      · intro i; exact uniformExponents_nonneg k (A i)
      · intro i
        have hi:=(uniformQuantileCell_bounds k (e i)).1
        change (uniformExponents k (A i))≤fieldExponents w i
        simpa only [uniformExponents,uniformQuantileGrid,Nat.cast_add,Nat.cast_one] using (show (uniformQuantileGrid k (uniformQuantileCell k (e i)).castSucc : ℝ) ≤ (e i : ℝ) from hi)
    · apply sphericalHeatValue_ofFn_mono_parameters
      · exact fieldExponents_nonneg w hw
      · intro i
        have hi:=(uniformQuantileCell_bounds k (e i)).2
        change fieldExponents w i≤uniformExponents k (B i)
        simpa only [uniformExponents,uniformQuantileGrid,Nat.cast_add,Nat.cast_one] using (show (e i : ℝ) ≤ (uniformQuantileGrid k (uniformQuantileCell k (e i)).succ : ℝ) from hi)
  · have hg:=sphericalGridDual_step_gap A B V hV (fun i=>Fin.castSucc_le_succ _)
      (fun i=>by dsimp [A,B]; simp)
    refine hg.trans ?_
    rw [fieldVariances_sum]
    have hk : (0:ℝ)<(k+1:ℕ):=by positivity
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(k+1:ℕ))).mpr
    field_simp
    nlinarith


theorem finiteSphericalFieldValue_depth_uniform_oai (H : ℝ) (hH : 0≤H)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d (w h : Fin (d+1)→ℝ)
      (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1),
      Monotone h → 0≤h 0 → h (Fin.last d)≤H →
      |finiteSphericalFieldValue n d w h-
        sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε := by
  obtain ⟨k,hk⟩:=exists_nat_gt (2*H/ε)
  have hk0 : (0:ℝ)<(k+1:ℕ):=by
    exact lt_of_le_of_lt (div_nonneg (mul_nonneg (by norm_num) hH) hε.le)
      (hk.trans (by push_cast; linarith))
  have hgap : H/(k+1:ℕ)<ε/2 := by
    apply (div_lt_iff₀ hk0).mpr
    have hek : 2*H<ε*(k+1:ℕ):=by
      have h:= (div_lt_iff₀ hε).mp hk
      push_cast
      nlinarith
    linarith
  have hu:=sphericalGridValue_compact_uniform k (2*H)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu (ε/2) (by positivity)] with n hn
  intro d w h hw hw1 hh hh0 hhH
  obtain ⟨v,u,hv,hu,hbr,hgap'⟩:=finiteSphericalFieldValue_grid_bracket w h hw hw1 hh hh0 H hhH k
  have hf:=(finiteSphericalFieldValue_pointwise_dual w h hw hw1 hh hh0).choose_spec.2.2.2
  have hvl:=(sphericalGridValue_compact_uniform k (2*H)).tendsto_at hv
  have hul:=(sphericalGridValue_compact_uniform k (2*H)).tendsto_at hu
  have hBD : sphericalGridDual k v≤ sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1) :=
    le_of_tendsto_of_tendsto hvl hf (Eventually.of_forall fun m=>(hbr m).1)
  have hDU : sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)≤ sphericalGridDual k u :=
    le_of_tendsto_of_tendsto hf hul (Eventually.of_forall fun m=>(hbr m).2)
  have hnv:=hn v hv
  have hnu:=hn u hu
  rw [Real.dist_eq] at hnv hnu
  have hGU : sphericalGridDual k u-sphericalGridDual k v≤H/(k+1:ℕ) := by
    linarith [(abs_le.mp hgap').1]
  exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hnv).2,(hbr n).1],
    by linarith [(abs_lt.mp hnu).1,(hbr n).2]⟩
end SphericalPerceptronFreeEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform_oai := @OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform_oai
