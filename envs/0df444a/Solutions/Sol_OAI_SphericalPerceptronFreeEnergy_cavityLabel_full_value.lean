-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:20:00.031066+00:00
-- url     : https://prove2.me/submissions/2c5e4431-cdd7-4510-9344-59a31632fa75

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavityLabel_full_evaluation

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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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

lemma gaussianEntropic_zero {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (σ : ℝ) (x : E) :
    gaussianEntropic μ 0 σ f x=∫ y, f (x+σ • y) ∂μ :=
  entropicMean_zero μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)

lemma gaussianEntropic_pos {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p : ℝ} (hp : p ≠ 0) (σ : ℝ) (x : E) :
    gaussianEntropic μ p σ f x=Real.log (∫ y, Real.exp (p*f (x+σ • y)) ∂μ)/p :=
  entropicMean_eq_div μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) hp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
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
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem progressive_zero (P : Measure BrownianPath) :
    Progressive P (fun _ _ => 0) := by
  intro t
  exact measurable_const

theorem abs_integral_reward_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (X : BrownianPath → ℝ) :
    |∫ ω, f (X ω) ∂P| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun ω => f (X ω)) (C := ‖f‖)
    (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X ω))
  simpa using h

theorem controlPayoff_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (v : Time → BrownianPath → ℝ) :
    controlPayoff P f m v ≤ ‖f‖ := by
  unfold controlPayoff
  have h := (abs_integral_reward_le P f
    (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))
  have h := (le_abs_self _).trans h
  exact (sub_le_self _ (div_nonneg ENNReal.toReal_nonneg (by norm_num))).trans h

theorem controlPayoffs_nonempty (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}.Nonempty := by
  exact ⟨_, fun _ _ => 0, progressive_zero P, by simp, rfl⟩

theorem controlPayoffs_bddAbove (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    BddAbove {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v} := by
  refine ⟨‖f‖, ?_⟩
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlDrift
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
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma brownianEval_measurable (t : ℝ≥0) : Measurable (brownianEval t) :=
  (continuous_eval_const t).measurable

lemma usualBrownianSigma_le_completion (P : Measure BrownianPath) (t : Time) :
    usualBrownianSigma P t ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) := by
  unfold usualBrownianSigma
  refine (iInf_le _ (⟨2, lt_of_le_of_lt t.property.2 (by norm_num)⟩ :
    {s : ℝ≥0 // (t : ℝ) < s})).trans ?_
  apply sup_le
  · apply iSup_le
    intro r
    exact (brownianEval_measurable r.val).comap_le.trans
      (fun _ hs => hs.nullMeasurableSet)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact NullMeasurableSet.of_null hs

lemma progressive_joint_complete (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    Measurable (fun p : Time × NullMeasurableSpace BrownianPath P => v p.1 p.2) := by
  have h := (hv 1).mono (show MeasurableSpace.prod inferInstance (usualBrownianSigma P 1) ≤
      MeasurableSpace.prod inferInstance
        (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) from
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (usualBrownianSigma_le_completion P 1))) le_rfl
  have hf : Measurable (fun p : Time × NullMeasurableSpace BrownianPath P =>
      (⟨p.1, p.1.property.2⟩ : Set.Iic (1 : Time))) := measurable_fst.subtype_mk
  exact h.comp (hf.prodMk measurable_snd)

lemma progressive_time_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (ω : BrownianPath) :
    Measurable (fun t : Time => v t ω) :=
  (progressive_joint_complete P hv).comp (measurable_id.prodMk measurable_const)

lemma controlDrift_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (controlDrift m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => controlDrift m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      (progressive_joint_complete P hv)).stronglyMeasurable.integral_prod_left'.measurable
  exact (show NullMeasurable (controlDrift m v) P from h).aemeasurable

lemma pathControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (pathControlCost m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => pathControlCost m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      ((progressive_joint_complete P hv).pow_const 2)).ennreal_ofReal.lintegral_prod_left'
  exact (show NullMeasurable (pathControlCost m v) P from h).aemeasurable

lemma controlledTerminal_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (fun ω => brownianEval 1 ω + controlDrift m v ω) P :=
  (brownianEval_measurable 1).aemeasurable.add (controlDrift_aemeasurable P m hv)

lemma controlReward_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) :
    Integrable (fun ω => f (brownianEval 1 ω + controlDrift m v ω)) P := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.measurable.comp_aemeasurable
      (controlledTerminal_aemeasurable P m hv)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalVariational
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
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma indep_eventuallyMeasurable_left {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) {m n : MeasurableSpace Ω} (h : Indep m n μ) :
    Indep (eventuallyMeasurableSpace m (ae μ)) n μ := by
  rw [Indep_iff] at h ⊢
  rintro A B ⟨A', hA', hAA'⟩ hB
  rw [measure_congr (hAA'.inter (Filter.EventuallyEq.refl (ae μ) B)), measure_congr hAA']
  exact h A' B hA' hB

lemma nullSigma_le_eventuallyMeasurable (P : Measure BrownianPath)
    (m : MeasurableSpace BrownianPath) :
    nullSigma P ≤ eventuallyMeasurableSpace m (ae P) := by
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact ⟨∅, MeasurableSet.empty, ae_eq_empty.mpr hA⟩

lemma rawBrownianSigma_le_past_comap (s : ℝ≥0) :
    rawBrownianSigma s ≤
      MeasurableSpace.comap (fun ω (r : Set.Iic s) => brownianEval r.val ω) inferInstance := by
  apply iSup_le
  intro r
  rintro A ⟨B, hB, rfl⟩
  exact ⟨(fun f : Set.Iic s → ℝ => f r) ⁻¹' B, (measurable_pi_apply r) hB, rfl⟩

lemma usualBrownianSigma_le_ae_raw (P : Measure BrownianPath) (t : Time)
    (s : ℝ≥0) (hts : (t : ℝ) < s) :
    usualBrownianSigma P t ≤ eventuallyMeasurableSpace (rawBrownianSigma s) (ae P) := by
  apply (iInf_le _ (⟨s, hts⟩ : {s : ℝ≥0 // (t : ℝ) < s})).trans
  exact sup_le le_eventuallyMeasurableSpace (nullSigma_le_eventuallyMeasurable P _)

lemma brownian_future_indep_raw (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (s u : ℝ≥0) :
    Indep (rawBrownianSigma s)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P := by
  have h := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply u)
  exact indep_of_indep_of_le_left h (rawBrownianSigma_le_past_comap s)

lemma brownian_future_indep_usual_earlier (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (t : Time) (s u : ℝ≥0)
    (hts : (t : ℝ) < s) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P :=
  indep_of_indep_of_le_left
    (indep_eventuallyMeasurable_left P (brownian_future_indep_raw P hB s u))
    (usualBrownianSigma_le_ae_raw P t s hts)

lemma indep_setIntegral_eq_mul_null {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ} {A : Set Ω}
    (hI : Indep m (MeasurableSpace.comap X (borel ℝ)) P)
    (hX : AEMeasurable X P) (hA : MeasurableSet[m] A) (hAn : NullMeasurableSet A P)
    (f : ℝ →ᵇ ℝ) :
    (∫ ω in A, f (X ω) ∂P) = P.real A * ∫ ω, f (X ω) ∂P := by
  calc
    _ = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) * f (X ω) ∂P := by
      rw [← integral_indicator₀ hAn]
      congr with ω
      by_cases hω : ω ∈ A <;> simp [hω]
    _ = _ := by
      simp only [Pi.one_def]
      rw [IndepFun.integral_fun_comp_mul_comp
        (hI.indicator_indepFun 1 hA)
        ((aemeasurable_indicator_const_iff 1).2 hAn) hX
        measurable_id.aestronglyMeasurable f.continuous.measurable.aestronglyMeasurable]
      simp only [id_eq, integral_indicator₀ hAn, integral_const, smul_eq_mul, mul_one,
        measureReal_def, Measure.restrict_apply_univ]

lemma indep_comap_of_ae_tendsto {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : ∀ A, MeasurableSet[m] A → NullMeasurableSet A P)
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hI : ∀ n, Indep m (MeasurableSpace.comap (X n) (borel ℝ)) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y (borel ℝ)) P := by
  apply (Indep_iff_IndepSets _ _ P).2
  apply indepSets_comap_of_bcf (fun A hA => hm A hA) hY
  intro A hA f
  have hall := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    (hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  have hres := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable.restrict)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    ((ae_restrict_of_ae hlim).mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  apply tendsto_nhds_unique hres
  convert hall.const_mul (P.real A) using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact indep_setIntegral_eq_mul_null P (hI n) (hX n) hA (hm A hA) f

lemma brownian_increment_indep_usual (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval r ω -
        brownianEval ⟨t.val, t.property.1⟩ ω) (borel ℝ)) P := by
  let t₀ : ℝ≥0 := ⟨t.val, t.property.1⟩
  have ht₀r : t₀ < r := htr
  obtain ⟨s, -, hs, hlim⟩ := exists_seq_strictAnti_tendsto' ht₀r
  apply indep_comap_of_ae_tendsto P (fun A hA =>
    (usualBrownianSigma_le_completion P t A hA))
    (X := fun n ω => brownianEval r ω - brownianEval (s n) ω)
    (fun n => ((brownianEval_measurable r).sub (brownianEval_measurable (s n))).aemeasurable)
    (((brownianEval_measurable r).sub (brownianEval_measurable t₀)).aemeasurable)
  · intro n
    have hI := brownian_future_indep_usual_earlier P hB t (s n) (r-s n) (hs n).1
    rwa [add_tsub_cancel_of_le (hs n).2.le] at hI
  · exact Filter.Eventually.of_forall fun ω => tendsto_const_nhds.sub
      (ω.continuous.continuousAt.tendsto.comp hlim)

lemma progressive_clipControl (P : Measure BrownianPath) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) (L : ℝ) : Progressive P (clipControl L v) := by
  intro t
  exact measurable_const.max (measurable_const.min (hv t))

lemma abs_clip_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : |max (-L) (min L x)| ≤ L := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clip_cost_gain {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    L * |x - max (-L) (min L x)| ≤ (x^2 - (max (-L) (min L x))^2)/2 := by
  by_cases hx : x ≤ -L
  · have hxL : x ≤ L := hx.trans (by linarith)
    rw [min_eq_right hxL, max_eq_left hx, abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (x+L)]
  · by_cases hLx : L ≤ x
    · rw [min_eq_left hLx, max_eq_right (by linarith : -L ≤ L),
        abs_of_nonneg (by linarith : 0 ≤ x-L)]
      nlinarith [sq_nonneg (x-L)]
    · rw [min_eq_right (le_of_not_ge hLx), max_eq_right (le_of_not_ge hx)]
      simp

lemma clip_sq_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    (max (-L) (min L x))^2 ≤ x^2 := by
  have h := clip_cost_gain hL x
  nlinarith [mul_nonneg hL (abs_nonneg (x - max (-L) (min L x)))]

lemma pathControlCost_clip_le (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    pathControlCost m (clipControl L v) ω ≤ pathControlCost m v ω := by
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (clip_sq_le hL _) (m.nonneg t))

lemma controlCost_clip_le (P : Measure BrownianPath) (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) : controlCost P m (clipControl L v) ≤ controlCost P m v :=
  lintegral_mono fun ω => pathControlCost_clip_le m hL v ω

lemma weightedTime_integrable (m : Trial) {v : Time → ℝ} (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    Integrable (fun t => m t * v t ^ 2) timeLaw ∧
      Integrable (fun t => m t * v t) timeLaw := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  refine ⟨hq, (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  change |m t * v t| ≤ m t * v t ^ 2 + m t
  rw [abs_mul, abs_of_nonneg (m.nonneg t)]
  have h : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_nonneg (|v t| - 1), sq_abs (v t)]
  nlinarith [mul_le_mul_of_nonneg_left h (m.nonneg t)]

lemma integral_pathControlCost (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, (pathControlCost m v ω).toReal ∂P) = (controlCost P m v).toReal :=
  integral_toReal (pathControlCost_aemeasurable P m hv)
    (ae_lt_top' (pathControlCost_aemeasurable P m hv) hc.ne)

lemma clipping_drift_gain (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    {v : Time → BrownianPath → ℝ} (ω : BrownianPath)
    (hv : Measurable (fun t => v t ω)) (hc : pathControlCost m v ω < ∞) :
    L * |controlDrift m v ω - controlDrift m (clipControl L v) ω| ≤
      ((pathControlCost m v ω).toReal - (pathControlCost m (clipControl L v) ω).toReal)/2 := by
  have hw : Measurable (fun t => clipControl L v t ω) := measurable_const.max (measurable_const.min hv)
  have hcv := weightedTime_integrable m hv hc
  have hcw := weightedTime_integrable m hw ((pathControlCost_clip_le m hL v ω).trans_lt hc)
  have hev : (∫ t, m t * v t ω ^ 2 ∂timeLaw) = (pathControlCost m v ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcv.1.aestronglyMeasurable
  have hew : (∫ t, m t * clipControl L v t ω ^ 2 ∂timeLaw) =
      (pathControlCost m (clipControl L v) ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcw.1.aestronglyMeasurable
  unfold controlDrift
  rw [← integral_sub hcv.2 hcw.2]
  calc
    _ ≤ L * ∫ t, |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hL
    _ = ∫ t, L * |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ t, (m t * v t ω ^ 2 - m t * clipControl L v t ω ^ 2)/2 ∂timeLaw := by
      apply integral_mono ((hcv.2.sub hcw.2).abs.const_mul L) ((hcv.1.sub hcw.1).div_const 2)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg (m.nonneg t)]
      have h := mul_le_mul_of_nonneg_left (clip_cost_gain hL (v t ω)) (m.nonneg t)
      dsimp [clipControl]
      nlinarith
    _ = _ := by rw [integral_div, integral_sub hcv.1 hcw.1, hev, hew]

lemma controlPayoff_le_clipControl (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    controlPayoff P f m v ≤ controlPayoff P f m (clipControl L v) := by
  let w := clipControl L v
  have hw : Progressive P w := progressive_clipControl P hv L
  have hcw : controlCost P m w < ∞ := (controlCost_clip_le P m L.coe_nonneg v).trans_lt hc
  have hpv := pathControlCost_aemeasurable P m hv
  have hpw := pathControlCost_aemeasurable P m hw
  have hcvI := integrable_toReal_of_lintegral_ne_top hpv hc.ne
  have hcwI := integrable_toReal_of_lintegral_ne_top hpw hcw.ne
  have hineq : (∫ ω, (f (brownianEval 1 ω + controlDrift m v ω) -
        f (brownianEval 1 ω + controlDrift m w ω)) ∂P) ≤
      (∫ ω, ((pathControlCost m v ω).toReal - (pathControlCost m w ω).toReal)/2 ∂P) := by
    apply integral_mono_ae ((controlReward_integrable P f m hv).sub (controlReward_integrable P f m hw))
      ((hcvI.sub hcwI).div_const 2)
    filter_upwards [ae_lt_top' hpv hc.ne] with ω hω
    have hLip := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
      (brownianEval 1 ω + controlDrift m w ω)
    rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hLip
    exact (le_abs_self _).trans (hLip.trans
      (clipping_drift_gain m L.coe_nonneg ω (progressive_time_measurable P hv ω) hω))
  rw [integral_sub (controlReward_integrable P f m hv) (controlReward_integrable P f m hw),
    integral_div, integral_sub hcvI hcwI, integral_pathControlCost P m hv hc,
    integral_pathControlCost P m hw hcw] at hineq
  unfold controlPayoff
  change _ ≤ _
  dsimp only [controlDrift, w] at hineq
  linarith

lemma controlValue_le_of_bounded_controls (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) (b : ℝ)
    (hb : ∀ v : Time → BrownianPath → ℝ, Progressive P v → controlCost P m v < ∞ →
      (∀ t ω, |v t ω| ≤ L) → controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  exact (controlPayoff_le_clipControl P f m L hf hv hc).trans
    (hb (clipControl L v) (progressive_clipControl P hv L)
      ((controlCost_clip_le P m L.coe_nonneg v).trans_lt hc)
      (fun t ω => abs_clip_le L.coe_nonneg (v t ω)))

lemma pathControlCost_le_bound (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    pathControlCost m v ω ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _t : Time, ENNReal.ofReal ((L : ℝ)^2) ∂timeLaw := by
      apply lintegral_mono
      intro t
      apply ENNReal.ofReal_le_ofReal
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      exact (mul_le_mul_of_nonneg_right (m.le_one t) (sq_nonneg _)).trans (by simpa using hx)
    _ = _ := by simp

lemma controlCost_le_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) :
    controlCost P m v ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _ω : BrownianPath, ENNReal.ofReal ((L : ℝ)^2) ∂P :=
      lintegral_mono fun ω => pathControlCost_le_bound m L hv ω
    _ = _ := by simp

lemma trial_abs_sub_integrable (m n : Trial) :
    Integrable (fun t => |m t - n t|) timeLaw := by
  apply (integrable_const (2 : ℝ)).mono'
    ((m.measurable.sub n.measurable).abs.aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (m.nonneg t), abs_of_nonneg (n.nonneg t)]; linarith [m.le_one t,n.le_one t])

lemma bounded_drift_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |controlDrift m v ω - controlDrift n v ω| ≤ (L : ℝ) * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  rw [controlDrift, controlDrift, ← integral_sub hm.2 hn.2]
  calc
    _ ≤ ∫ t, |m t * v t ω - n t * v t ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ) * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.2.sub hn.2).abs ((trial_abs_sub_integrable m n).const_mul L)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv t ω) (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma bounded_pathCost_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ≤
      (L : ℝ)^2 * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  have hem : (pathControlCost m v ω).toReal = ∫ t, m t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hm.1.aestronglyMeasurable).symm
  have hen : (pathControlCost n v ω).toReal = ∫ t, n t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (n.nonneg t) (sq_nonneg _))
      hn.1.aestronglyMeasurable).symm
  rw [hem, hen, ← integral_sub hm.1 hn.1]
  calc
    _ ≤ ∫ t, |m t * v t ω ^ 2 - n t * v t ω ^ 2| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ)^2 * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.1.sub hn.1).abs ((trial_abs_sub_integrable m n).const_mul ((L : ℝ)^2))
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (v t ω))]
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma controlPayoff_trial_diff_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hbound : ∀ t ω, |v t ω| ≤ L) :
    |controlPayoff P f m v - controlPayoff P f n v| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  let D := ∫ t, |m t-n t| ∂timeLaw
  have hcm : controlCost P m v < ∞ := (controlCost_le_bound P m L hbound).trans_lt (by finiteness)
  have hcn : controlCost P n v < ∞ := (controlCost_le_bound P n L hbound).trans_lt (by finiteness)
  have hm := controlReward_integrable P f m hv
  have hn := controlReward_integrable P f n hv
  have hrew : |(∫ ω, f (brownianEval 1 ω + controlDrift m v ω) ∂P) -
      (∫ ω, f (brownianEval 1 ω + controlDrift n v ω) ∂P)| ≤ (L : ℝ)^2 * D := by
    rw [← integral_sub hm hn]
    calc
      _ ≤ ∫ ω, |f (brownianEval 1 ω + controlDrift m v ω) -
          f (brownianEval 1 ω + controlDrift n v ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono (hm.sub hn).abs (integrable_const _)
        intro ω
        have hh := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
          (brownianEval 1 ω + controlDrift n v ω)
        rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hh
        have hb := mul_le_mul_of_nonneg_left
          (bounded_drift_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)) L.coe_nonneg
        exact hh.trans (by dsimp only [D]; nlinarith [hb])
      _ = _ := by simp
  have hcost : |(controlCost P m v).toReal - (controlCost P n v).toReal| ≤ (L : ℝ)^2 * D := by
    rw [← integral_pathControlCost P m hv hcm, ← integral_pathControlCost P n hv hcn,
      ← integral_sub (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne)
        (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)]
    calc
      _ ≤ ∫ ω, |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono
          ((integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne).sub
            (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)).abs
          (integrable_const _)
        intro ω
        exact bounded_pathCost_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)
      _ = _ := by simp
  apply abs_le.mpr
  obtain ⟨hrewlo,hrewhi⟩ := abs_le.mp hrew
  obtain ⟨hcostlo,hcosthi⟩ := abs_le.mp hcost
  dsimp only [controlPayoff, controlDrift] at *
  constructor <;> linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianAverage
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
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma controlValue_trial_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    controlValue P f m - controlValue P f n ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  suffices controlValue P f m ≤ controlValue P f n +
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw by linarith
  apply controlValue_le_of_bounded_controls P f m L hf
  intro v hv _ hbound
  have hpay : controlPayoff P f n v ≤ controlValue P f n :=
    le_csSup (controlPayoffs_bddAbove P f n) ⟨v, hv,
      (controlCost_le_bound P n L hbound).trans_lt (by finiteness), rfl⟩
  have hd := (abs_le.mp (controlPayoff_trial_diff_bound P f m n L hf hv hbound)).2
  linarith

lemma controlValue_trial_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    |controlValue P f m - controlValue P f n| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  have hmn := controlValue_trial_sub_le P f m n L hf
  have hnm := controlValue_trial_sub_le P f n m L hf
  simp_rw [abs_sub_comm (n _) (m _)] at hnm
  exact abs_le.mpr ⟨by linarith, hmn⟩

lemma usual_measurable_aemeasurable (P : Measure BrownianPath) (t : Time)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    AEMeasurable Y P := by
  have h : NullMeasurable Y P := hY.mono (usualBrownianSigma_le_completion P t) le_rfl
  exact h.aemeasurable

lemma brownian_increment_indep_adapted (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    IndepFun Y (fun ω => brownianEval r ω - brownianEval ⟨t.val, (show 0 ≤ (t : ℝ) from t.property.1)⟩ ω) P :=
  indep_of_indep_of_le_left (brownian_increment_indep_usual P hB t r htr) hY.comap_le

lemma second_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2| ≤
      C * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd₁ : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hd₂ : iteratedDerivWithin 2 f (uIcc x y) x = iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc
  have hp : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + iteratedDeriv 2 f x * (y-x)^2/2 := by
    rw [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval, hd₁, hd₂]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2 =
      iteratedDeriv 3 f z * (y-x)^3/6 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (by positivity)) (by norm_num)

lemma first_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x)| ≤ C * (y-x)^2 / 2 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hp : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) = iteratedDeriv 2 f z * (y-x)^2/2 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x))]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (sq_nonneg _)) (by norm_num)

lemma smooth_deriv_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) : LipschitzWith C (deriv f) := by
  apply lipschitzWith_of_nnnorm_deriv_le hf.differentiable_deriv_two
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, coe_nnnorm, Real.norm_eq_abs] using hC x

lemma drift_shift_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x z a : ℝ) :
    |f (x+z+a) - f (x+z) - deriv f x * a| ≤ (C : ℝ) * (|z| * |a| + a^2/2) := by
  have ht := first_order_taylor_bound hf C hC (x+z) (x+z+a)
  simp only [add_sub_cancel_left] at ht
  have hd := (smooth_deriv_lipschitz hf C hC).dist_le_mul (x+z) x
  simp only [Real.dist_eq, add_sub_cancel_left] at hd
  calc
    _ = |(f (x+z+a) - f (x+z) - deriv f (x+z) * a) + (deriv f (x+z) - deriv f x) * a| := by congr 1; ring
    _ ≤ |f (x+z+a) - f (x+z) - deriv f (x+z) * a| + |(deriv f (x+z) - deriv f x) * a| := abs_add_le _ _
    _ ≤ (C : ℝ) * a^2/2 + (C : ℝ) * |z| * |a| := by
      rw [abs_mul]
      exact add_le_add ht (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    _ = _ := by ring

lemma gaussian_abs_moment (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
      (Real.sqrt v)^n * ∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt v)^2, sq_nonneg _⟩ : ℝ≥0) = v := by
    ext; exact Real.sq_sqrt v.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  simp only [mul_zero, NNReal.mk] at hL
  rw [hv, mul_one] at hL
  rw [← hL.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^n) (gaussianReal 0 v))]
  simp only [Function.comp_apply, id_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

lemma gaussian_law_integrable_abs_pow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) (n : ℕ) :
    Integrable (fun ω => |Z ω|^n) P := by
  have hm : MemLp id (n : ℝ≥0∞) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) (n : ℝ≥0))
  have hi : Integrable (fun x : ℝ => |x|^n) (Measure.map Z P) := by
    rw [hZ.map_eq]
    simpa only [Real.norm_eq_abs, id_eq] using hm.integrable_norm_pow'
  exact (integrable_map_measure hi.aestronglyMeasurable hZ.aemeasurable).mp hi

lemma gaussian_law_sq_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) :
    (∫ ω, (Z ω)^2 ∂P) = v := by
  have hi := hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2)
    (gaussianReal 0 v))
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  simp only [variance_id_gaussianReal, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    zero_pow (by decide : 2 ≠ 0), sub_zero] at hv
  exact hi.trans hv.symm

lemma gaussian_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₂ C₃ : ℝ) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) :
    |(∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  let d₁ := deriv (f : ℝ → ℝ)
  let d₂ := iteratedDeriv 2 (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hm₂ : Measurable d₂ := (hf.continuous_iteratedDeriv 2 (by norm_num)).measurable
  have hi₁ : Integrable (fun ω => d₁ (X ω) * Z ω) P := by
    have hz : Integrable Z P := by
      have hi := gaussian_law_integrable_abs_pow hZ 1
      exact (integrable_norm_iff hZ.aemeasurable.aestronglyMeasurable).mp (by
        simpa only [pow_one, Real.norm_eq_abs] using hi)
    apply hz.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have hi₂ : Integrable (fun ω => d₂ (X ω) * (Z ω)^2) P := by
    have hz : Integrable (fun ω => (Z ω)^2) P := by
      simpa only [sq_abs] using gaussian_law_integrable_abs_pow hZ 2
    apply hz.bdd_mul (hm₂.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₂] using h₂ (X ω)
  have hv₁ : (∫ ω, d₁ (X ω) * Z ω ∂P) = 0 := by
    have hh := (hI.comp hm₁ measurable_id).integral_fun_mul_eq_mul_integral
      (hm₁.comp_aemeasurable hX).aestronglyMeasurable hZ.aemeasurable.aestronglyMeasurable
    have hz : (∫ ω, Z ω ∂P) = 0 := hZ.integral_eq.trans (integral_id_gaussianReal)
    simpa only [Function.comp_apply, id_eq, hz, mul_zero] using hh
  have hv₂ : (∫ ω, d₂ (X ω) * (Z ω)^2 ∂P) = (v : ℝ) * (∫ ω, d₂ (X ω) ∂P) := by
    have hh := (hI.comp hm₂ (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      (hm₂.comp_aemeasurable hX).aestronglyMeasurable (hZ.aemeasurable.pow_const 2).aestronglyMeasurable
    simp only [Function.comp_apply, id_eq] at hh
    exact hh.trans (by rw [gaussian_law_sq_mean hZ, mul_comm])
  let R := fun ω => f (X ω + Z ω) - f (X ω) - d₁ (X ω) * Z ω - d₂ (X ω) * (Z ω)^2/2
  have hiR : Integrable R P :=
    (((boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)).sub
      (boundedContinuousFunction_integrable_comp f hX)).sub hi₁).sub (hi₂.div_const 2)
  have hR : ∀ ω, |R ω| ≤ C₃/6 * |Z ω|^3 := by
    intro ω
    have hh := second_order_taylor_bound hf C₃ h₃ (X ω) (X ω + Z ω)
    simpa only [add_sub_cancel_left, R, d₁, d₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hbound : |∫ ω, R ω ∂P| ≤ C₃/6 * ∫ ω, |Z ω|^3 ∂P := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C₃/6 * |Z ω|^3 ∂P := integral_mono hiR.abs
        ((gaussian_law_integrable_abs_pow hZ 3).const_mul _) hR
      _ = _ := integral_const_mul _ _
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, d₂ (X ω) ∂P := by
    have ha := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
    have hb := boundedContinuousFunction_integrable_comp f hX
    have he₁ := integral_sub ((ha.sub hb).sub hi₁) (hi₂.div_const 2)
    have he₂ := integral_sub (ha.sub hb) hi₁
    have he₃ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂ he₃
    dsimp only [R]
    rw [he₁, he₂, he₃, integral_div, hv₁, hv₂]
    ring
  have hg : (∫ ω, |Z ω|^3 ∂P) = (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 :=
    (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^3) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 3)
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma drift_shift_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (C₁ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P)| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) := by
  let d₁ := deriv (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hiA := bounded_real_integrable hA K (Filter.Eventually.of_forall hAK)
  have hi₁ : Integrable (fun ω => d₁ (X ω) * A ω) P := by
    apply hiA.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have ha := boundedContinuousFunction_integrable_comp f ((hX.add hZ.aemeasurable).add hA)
  have hb := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
  let R := fun ω => f (X ω + Z ω + A ω) - f (X ω + Z ω) - d₁ (X ω) * A ω
  have hiR : Integrable R P := (ha.sub hb).sub hi₁
  have hR : ∀ ω, |R ω| ≤ (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) := by
    intro ω
    apply (drift_shift_taylor_bound hf C₂ h₂ (X ω) (Z ω) (A ω)).trans
    apply mul_le_mul_of_nonneg_left _ C₂.coe_nonneg
    have hsq : A ω ^2 ≤ (K : ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (A ω)) K.coe_nonneg).mpr (hAK ω)
    exact add_le_add (mul_le_mul_of_nonneg_left (hAK ω) (abs_nonneg _)) (by linarith)
  have hiz : Integrable (fun ω => |Z ω|) P := by
    simpa only [pow_one] using gaussian_law_integrable_abs_pow hZ 1
  have hbound : |∫ ω, R ω ∂P| ≤
      (C₂ : ℝ) * ((∫ ω, |Z ω| ∂P) * (K : ℝ) + (K : ℝ)^2/2) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) ∂P :=
        integral_mono hiR.abs (((hiz.mul_const K).add (integrable_const _)).const_mul C₂) hR
      _ = _ := by rw [integral_const_mul, integral_add (hiz.mul_const K) (integrable_const _), integral_mul_const]; simp
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω + A ω) ∂P) -
      (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, d₁ (X ω) * A ω ∂P) := by
    have he₁ := integral_sub (ha.sub hb) hi₁
    have he₂ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂
    exact he₁.trans (by rw [he₂])
  have hg : (∫ ω, |Z ω| ∂P) = Real.sqrt v * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
    have hh := (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^1) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 1)
    simpa only [pow_one, Function.comp_apply] using hh
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma gaussian_drift_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₃ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) +
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  have hG := gaussian_taylor_mean_bound f hf C₁ C₂ C₃ h₁ h₂ h₃ hX hZ hI
  have hD := drift_shift_mean_bound f (hf.of_le (by norm_num)) C₁ C₂ K h₁ h₂ hX hZ hA hAK
  have hh := abs_add_le
    ((∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P))
    ((∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P)
  convert hh.trans (add_le_add hD hG) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma gaussianAverage_semigroup (s t : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (gaussianAverageBCF t f) x = gaussianAverage (s+t) f x := by
  have hi : Integrable (fun z => f (x+z)) ((gaussianReal 0 s) ∗ (gaussianReal 0 t)) := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
    exact gaussianAverage_integrable (s+t) f x
  have hh := integral_conv hi
  simp only [gaussianReal_conv_gaussianReal, zero_add] at hh
  simpa only [gaussianAverage, gaussianAverageBCF_coe, add_assoc] using hh.symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatLogBCF
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

lemma exp_heatLog (s d : ℝ≥0) (hd : d ≠ 0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (d * heatLog s d f x) = gaussianAverage s (expBCF d f) x := by
  simp only [heatLog, hd, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hd), one_mul,
    Real.exp_log (gaussianAverage_exp_pos s d f x)]

lemma heatLog_zero (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : heatLog 0 d f x = f x := by
  by_cases hd : d = 0
  · simp [heatLog, hd]
  · simp [heatLog, hd]

lemma heatLog_semigroup (s t d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    heatLog s d (heatLogBCF t d f) x = heatLog (s+t) d f x := by
  by_cases hd : d = 0
  · subst d
    have he : heatLogBCF t 0 f = gaussianAverageBCF t f := by ext z; simp [heatLog]
    simp only [heatLog, ↓reduceIte, he]
    exact gaussianAverage_semigroup s t f x
  · have he : expBCF d (heatLogBCF t d f) = gaussianAverageBCF t (expBCF d f) := by
      ext z
      exact exp_heatLog t d hd f z
    simp only [heatLog, hd, ↓reduceIte, he, gaussianAverage_semigroup]

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv
lemma Jet3.deriv2_eq (g : Jet3) : iteratedDeriv 2 (g.f : ℝ → ℝ) = g.d2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, g.deriv_eq]
  exact funext fun x => (g.has2 x).deriv
lemma Jet3.deriv3_eq (g : Jet3) : iteratedDeriv 3 (g.f : ℝ → ℝ) = g.d3 := by
  rw [iteratedDeriv_succ, g.deriv2_eq]
  exact funext fun x => (g.has3 x).deriv

lemma Jet3.contDiff (g : Jet3) : ContDiff ℝ 3 (g.f : ℝ → ℝ) := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has1 x).differentiableAt, by norm_num, ?_⟩
  rw [g.deriv_eq, show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has2 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d1 : ℝ → ℝ) = g.d2 from funext fun x => (g.has2 x).deriv,
    show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has3 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d2 : ℝ → ℝ) = g.d3 from funext fun x => (g.has3 x).deriv]
  exact contDiff_zero.mpr g.d3.continuous

lemma Jet3.gaussianAverage_norms (s : ℝ≥0) (g : Jet3) :
    ‖(g.gaussianAverage s).f‖ ≤ ‖g.f‖ ∧ ‖(g.gaussianAverage s).d1‖ ≤ ‖g.d1‖ ∧
    ‖(g.gaussianAverage s).d2‖ ≤ ‖g.d2‖ ∧ ‖(g.gaussianAverage s).d3‖ ≤ ‖g.d3‖ := by
  have hh (f : ℝ →ᵇ ℝ) : ‖gaussianAverageBCF s f‖ ≤ ‖f‖ := by
    rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
    intro x; exact gaussianAverage_abs_le s f x
  exact ⟨hh _,hh _,hh _,hh _⟩

lemma invBCF_norm_le (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) :
    ‖invBCF g c hc hg‖ ≤ c⁻¹ := by
  rw [BoundedContinuousFunction.norm_le (inv_nonneg.mpr hc.le)]
  intro x; exact inv_bcf_bound hc hg x

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptronFreeEnergy.heatLog]
  · rfl

lemma gaussianAverage_jet_error (s : ℝ≥0) (g : Jet3) (x : ℝ) :
    |gaussianAverage s g.f x - g.f x - (s : ℝ)/2 * g.d2 x| ≤
      ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by
  have hh := gaussian_taylor_mean_bound (P := gaussianReal 0 s) g.f g.contDiff
    ‖g.d1‖ ‖g.d2‖ ‖g.d3‖
    (fun y => by rw [g.deriv_eq]; exact g.d1.norm_coe_le_norm y)
    (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y)
    (fun y => by rw [g.deriv3_eq]; exact g.d3.norm_coe_le_norm y)
    (X := fun _ : ℝ => x) aemeasurable_const (Z := id) HasLaw.id (indepFun_const_left _ _)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, g.deriv2_eq, gaussianAverage, id_eq] using hh

lemma log_linear_error_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b - Real.log a - (b-a)/a| ≤ (b-a)^2 / c^2 := by
  have ha0 := hc.trans_le ha
  have hb0 := hc.trans_le hb
  have hu := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hu
  rw [Real.log_div ha0.ne' hb0.ne'] at hl
  have heq : b/a-1 = (b-a)/a := by field_simp
  rw [heq] at hu
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  have hlin : -(Real.log b - Real.log a - (b-a)/a) ≤ (b-a)^2/(a*b) := by
    have he : (b-a)/a + (a/b-1) = (b-a)^2/(a*b) := by field_simp; ring
    linarith
  exact hlin.trans (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hc)
    (by nlinarith [mul_le_mul ha hb hc.le ha0.le]))

lemma gaussianAverage_ge_const (s : ℝ≥0) (f : ℝ →ᵇ ℝ) {c : ℝ}
    (hc : ∀ x, c ≤ f x) (x : ℝ) : c ≤ gaussianAverage s f x := by
  have hh := integral_mono (integrable_const c) (gaussianAverage_integrable s f x) (fun z => hc (x+z))
  simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma log_gaussian_generator_error (g : Jet3) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x, c ≤ g.f x) (C₂ C₃ : ℝ≥0) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃)
    (s : ℝ≥0) (hs : s ≤ 1) (x : ℝ) :
    |Real.log (gaussianAverage s g.f x) - Real.log (g.f x) -
      (s : ℝ)/2 * g.d2 x / g.f x| ≤
      (((C₂ : ℝ)/2 + (C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))^2/c^2 +
        ((C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))/c) * (s : ℝ) * Real.sqrt s := by
  let A := gaussianAverage s g.f x
  let a := g.f x
  let K := (C₃ : ℝ)/6 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  let D := (C₂ : ℝ)/2 + K
  have ha := hg x
  have hA := gaussianAverage_ge_const s g.f hg x
  have hM : 0 ≤ ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := integral_nonneg (fun z => by positivity)
  have hK : 0 ≤ K := by positivity
  have hD : 0 ≤ D := by positivity
  have hs0 : 0 ≤ (s : ℝ) := s.coe_nonneg
  have hs1 : (s : ℝ) ≤ 1 := hs
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := (Real.sqrt_le_one).mpr hs1
  have hrsq := Real.sq_sqrt hs0
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ) * Real.sqrt (s : ℝ) := by nlinarith
  have herr : |A-a-(s : ℝ)/2*g.d2 x| ≤ K * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by gcongr
      _ = _ := by rw [hrcube]; unfold K; ring
  have hdx : |g.d2 x| ≤ C₂ := (g.d2.norm_coe_le_norm x).trans h₂
  have hdelta : |A-a| ≤ D * (s : ℝ) := by
    have habs := abs_add_le (A-a-(s : ℝ)/2*g.d2 x) ((s : ℝ)/2*g.d2 x)
    rw [sub_add_cancel] at habs
    have hterm : |(s : ℝ)/2*g.d2 x| ≤ (s : ℝ)/2*C₂ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s/2)]
      exact mul_le_mul_of_nonneg_left hdx (by positivity)
    have hkr := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hK hs0)
    dsimp [D]; nlinarith
  have hquad : (A-a)^2/c^2 ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s := by
    have hdsq : (A-a)^2 ≤ (D*(s : ℝ))^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (A-a)) (mul_nonneg hD hs0)).mpr hdelta
      simpa only [sq_abs] using hh
    calc
      _ ≤ (D*(s : ℝ))^2/c^2 := div_le_div_of_nonneg_right hdsq (sq_nonneg c)
      _ = D^2/c^2 * (s : ℝ)^2 := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsr hs0)
          (show 0 ≤ D^2/c^2 by positivity)
        nlinarith only [hh]
  have hrem : |A-a-(s : ℝ)/2*g.d2 x|/a ≤ (K/c) * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ (K*(s : ℝ)*Real.sqrt s)/c := div_le_div₀ (by positivity) herr hc ha
      _ = _ := by ring
  have hlog := log_linear_error_le hc ha hA
  change |Real.log A - Real.log a - (s : ℝ)/2*g.d2 x/a| ≤ _
  calc
    _ = |(Real.log A-Real.log a-(A-a)/a) + (A-a-(s : ℝ)/2*g.d2 x)/a| := by congr 1; ring
    _ ≤ |Real.log A-Real.log a-(A-a)/a| + |(A-a-(s : ℝ)/2*g.d2 x)/a| := abs_add_le _ _
    _ = |Real.log A-Real.log a-(A-a)/a| + |A-a-(s : ℝ)/2*g.d2 x|/a := by
      rw [abs_div, abs_of_pos (hc.trans_le ha)]
    _ ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s + (K/c)*(s : ℝ)*Real.sqrt s :=
      add_le_add (hlog.trans hquad) hrem
    _ = _ := by dsimp [D,K]; ring

lemma expBCF_norm_le (d : ℝ) (f : ℝ →ᵇ ℝ) :
    ‖expBCF d f‖ ≤ Real.exp (|d| * ‖f‖) := by
  rw [BoundedContinuousFunction.norm_le (Real.exp_pos _).le]
  exact exp_bcf_bound d f

lemma Jet3.exp_norms (g : Jet3) (d C₀ C₁ C₂ C₃ : ℝ≥0)
    (h₀ : ‖g.f‖ ≤ C₀) (h₁ : ‖g.d1‖ ≤ C₁) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃) :
    let E := Real.exp ((d : ℝ)*C₀)
    ‖(g.exp d).f‖ ≤ E ∧ ‖(g.exp d).d1‖ ≤ (d : ℝ)*E*C₁ ∧
    ‖(g.exp d).d2‖ ≤ E*((d : ℝ)^2*C₁^2 + d*C₂) ∧
    ‖(g.exp d).d3‖ ≤ E*((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*C₁*C₂ + d*C₃) := by
  dsimp only
  have hf : ‖expBCF d g.f‖ ≤ Real.exp ((d : ℝ)*C₀) := by
    refine (expBCF_norm_le d g.f).trans ?_
    rw [abs_of_nonneg d.coe_nonneg]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h₀ d.coe_nonneg)
  refine ⟨hf, ?_, ?_, ?_⟩
  · change ‖(d : ℝ) • (expBCF d g.f * g.d1)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ) * (‖expBCF d g.f‖ * ‖g.d1‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ (d : ℝ) * (Real.exp ((d : ℝ)*C₀) * C₁) := by gcongr
      _ = _ := by ring
  · change ‖expBCF d g.f * ((d : ℝ)^2 • (g.d1^2) + (d : ℝ) • g.d2)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * (‖(d : ℝ)^2 • (g.d1^2)‖ + ‖(d : ℝ) • g.d2‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^2 * ‖g.d1^2‖ + (d : ℝ) * ‖g.d2‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg, abs_pow]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^2 * C₁^2 + (d : ℝ) * C₂) := by
        gcongr
        exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖expBCF d g.f * ((d : ℝ)^3 • (g.d1^3) + (3*(d : ℝ)^2) • (g.d1*g.d2) + (d : ℝ) • g.d3)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * ((‖(d : ℝ)^3 • (g.d1^3)‖ + ‖(3*(d : ℝ)^2) • (g.d1*g.d2)‖) + ‖(d : ℝ) • g.d3‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^3 * ‖g.d1^3‖ + 3*(d : ℝ)^2*‖g.d1*g.d2‖ + (d : ℝ)*‖g.d3‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)^3),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3*(d : ℝ)^2), abs_of_nonneg d.coe_nonneg]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*(C₁*C₂) + (d : ℝ)*C₃) := by
        gcongr
        · exact (norm_pow_le _ _).trans (by gcongr)
        · exact (norm_mul_le _ _).trans (by gcongr)
      _ = _ := by ring

lemma Jet3.heatLog_uniform_bounds (d : ℝ≥0) (g : Jet3) :
    ∃ C₀ C₁ C₂ C₃ : ℝ≥0, ∀ s : ℝ≥0,
      ‖(g.heatLog s d).f‖ ≤ C₀ ∧ ‖(g.heatLog s d).d1‖ ≤ C₁ ∧
      ‖(g.heatLog s d).d2‖ ≤ C₂ ∧ ‖(g.heatLog s d).d3‖ ≤ C₃ := by
  by_cases hd : d = 0
  · subst d
    refine ⟨‖g.f‖₊, ‖g.d1‖₊, ‖g.d2‖₊, ‖g.d3‖₊, ?_⟩
    intro s; simpa only [Jet3.heatLog, ↓reduceDIte, coe_nnnorm] using g.gaussianAverage_norms s
  let e := g.exp d
  let B := (Real.exp (-(d : ℝ)*‖g.f‖))⁻¹
  let r := (d : ℝ)⁻¹
  have hB : 0 ≤ B := by positivity
  have hr : 0 ≤ r := by positivity
  refine ⟨‖g.f‖₊,
    ⟨r*(‖e.d1‖*B), by positivity⟩,
    ⟨r*(‖e.d2‖*B+‖e.d1‖^2*B^2), by positivity⟩,
    ⟨r*(‖e.d3‖*B+3*(‖e.d1‖*‖e.d2‖*B^2)+2*(‖e.d1‖^3*B^3)), by positivity⟩, ?_⟩
  intro s
  let A := e.gaussianAverage s
  let c := Real.exp (-(d : ℝ)*‖g.f‖)
  let hc := Real.exp_pos (-(d : ℝ)*‖g.f‖)
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  have hj : ‖J‖ ≤ B := invBCF_norm_le A.f c hc hA
  obtain ⟨_, h₁,h₂,h₃⟩ := e.gaussianAverage_norms s
  have hf : ‖(g.heatLog s d).f‖ ≤ ‖g.f‖ := by
    rw [g.heatLog_f, BoundedContinuousFunction.norm_le (norm_nonneg _)]
    exact heatLog_abs_le s d g.f
  rw [Jet3.heatLog, dite_eq_right hd]
  refine ⟨by simpa only [Jet3.heatLog, dite_eq_right hd, coe_nnnorm] using hf, ?_, ?_, ?_⟩
  · change ‖r • (A.d1*J)‖ ≤ r * (‖e.d1‖*B)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (by gcongr)) hr
  · change ‖r • (A.d2*J - A.d1^2*J^2)‖ ≤ r*(‖e.d2‖*B+‖e.d1‖^2*B^2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖r • (A.d3*J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_mul_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)

lemma heatLog_generator_uniform (d C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ →
      ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ → ∀ (s : ℝ≥0), s ≤ 1 → ∀ x : ℝ,
        |heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)| ≤
          (C : ℝ) * (s : ℝ) * Real.sqrt s := by
  let M := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg (fun z => by positivity)
  by_cases hd : d = 0
  · subst d
    refine ⟨⟨(C₃ : ℝ)/6*M, by positivity⟩, ?_⟩
    intro g _ _ _ h₃ s _ x
    simp only [heatLog, ↓reduceIte, NNReal.coe_zero, zero_mul, add_zero]
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * M := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * M := by gcongr
      _ = (C₃ : ℝ)/6*M * (s : ℝ) * Real.sqrt s := by
        have hh := Real.sq_sqrt s.coe_nonneg
        calc
          _ = (C₃ : ℝ)/6*M * (Real.sqrt s)^2 * Real.sqrt s := by ring
          _ = _ := by rw [hh]
  let c := Real.exp (-(d : ℝ)*C₀)
  let E := Real.exp ((d : ℝ)*C₀)
  let E₂ : ℝ≥0 := ⟨E*((d : ℝ)^2*C₁^2+(d : ℝ)*C₂), by positivity⟩
  let E₃ : ℝ≥0 := ⟨E*((d : ℝ)^3*C₁^3+3*(d : ℝ)^2*C₁*C₂+(d : ℝ)*C₃), by positivity⟩
  let K := ((E₂ : ℝ)/2+(E₃ : ℝ)/6*M)^2/c^2 + ((E₃ : ℝ)/6*M)/c
  have hc : 0 < c := Real.exp_pos _
  have hK : 0 ≤ K := by positivity
  have hdpos : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  refine ⟨⟨(d : ℝ)⁻¹*K, by positivity⟩, ?_⟩
  intro g h₀ h₁ h₂ h₃ s hs x
  have hh := g.exp_norms d C₀ C₁ C₂ C₃ h₀ h₁ h₂ h₃
  have hlo (x : ℝ) : c ≤ (g.exp d).f x := by
    change Real.exp (-(d : ℝ)*C₀) ≤ Real.exp ((d : ℝ)*g.f x)
    apply Real.exp_le_exp.mpr
    have hb : |g.f x| ≤ C₀ := (g.f.norm_coe_le_norm x).trans h₀
    nlinarith [(abs_le.mp hb).1]
  have herr := log_gaussian_generator_error (g.exp d) c hc hlo E₂ E₃ hh.2.2.1 hh.2.2.2 s hs x
  have he : (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x =
      (d : ℝ) * ((s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)) := by
    change (s : ℝ)/2 * (Real.exp ((d : ℝ)*g.f x) * ((d : ℝ)^2*g.d1 x^2 + (d : ℝ)*g.d2 x)) /
      Real.exp ((d : ℝ)*g.f x) = _
    field_simp
    ring
  have hid : heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x+(d : ℝ)*g.d1 x^2) =
      (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (g.exp d).f x) - Real.log ((g.exp d).f x) -
        (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x) := by
    rw [he]
    change _ = (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (expBCF d g.f) x) -
      Real.log (Real.exp ((d : ℝ)*g.f x)) - _)
    rw [Real.log_exp]
    simp only [heatLog, hd, ↓reduceIte]
    field_simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hdpos)]
  calc
    _ ≤ (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hdpos.le)
    _ = _ := by change (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) = (d : ℝ)⁻¹*K*(s : ℝ)*Real.sqrt s; ring

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BcfEvalRingHom
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

lemma gaussianAverage_scaling (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s f x = ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt s)^2, sq_nonneg _⟩ : ℝ≥0) = s := by
    ext; exact Real.sq_sqrt s.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt s)
  simp only [mul_zero,NNReal.mk] at hL
  rw [hv,mul_one] at hL
  exact (hL.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun z => f (x+z)) (gaussianReal 0 s))).symm

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

lemma fractional_log_moment_prod_add {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (b : ℝ) {f : S → ℝ} {g : T → ℝ}
    (hIf : Integrable (fun s => Real.exp (b*f s)) ν)
    (hIg : Integrable (fun t => Real.exp (b*g t)) ρ) :
    Real.log (∫ p, Real.exp (b*(f p.1+g p.2)) ∂ν.prod ρ)/b =
      Real.log (∫ s, Real.exp (b*f s) ∂ν)/b + Real.log (∫ t, Real.exp (b*g t) ∂ρ)/b := by
  simp_rw [mul_add,Real.exp_add]
  rw [integral_prod_mul (fun s => Real.exp (b*f s)) (fun t => Real.exp (b*g t)),Real.log_mul (integral_exp_pos hIf).ne' (integral_exp_pos hIg).ne',add_div]

theorem finiteCascadeLogRecursion_add_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    {H : X → ℝ} {G : Y → ℝ}
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) :
    finiteCascadeLogRecursion (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
        (fun q => H q.1+G q.2) (x,y) =
      finiteCascadeLogRecursion ν step₁ n z H x + finiteCascadeLogRecursion ρ step₂ n z G y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    rcases hIH with ⟨hHroot,hHtail⟩
    rcases hIG with ⟨hGroot,hGtail⟩
    conv_lhs => rw [finiteCascadeLogRecursion]
    change Real.log (∫ p : S×T, Real.exp (z 0 *
      finiteCascadeLogRecursion (productMarkLaw ν ρ)
        (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n (fun i => z i.succ)
          (fun q => H q.1+G q.2) (step₁ (x,p.1),step₂ (y,p.2))) ∂(ν : Measure S).prod (ρ : Measure T))/(z 0) = _
    simp_rw [ih (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail]
    exact fractional_log_moment_prod_add (ν : Measure S) (ρ : Measure T) (z 0) (hHroot x) (hGroot y)

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

lemma decoratedAngularFactor_mass_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) (r : ℝ) :
    decoratedTerminalTotalE step (fun _ => 0) k p ≤ decoratedAngularFactor n step field k p r := by
  rw [decoratedAngularFactor_eq n step hs field hf, ← decoratedLeafIntegral_exp]
  apply decoratedLeafIntegral_mono
  intro y
  simpa using ENNReal.ofReal_le_ofReal (one_le_sphericalExp n (field y) r)

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

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AmplitudeConvex
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
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CascadeIndependentTilt
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

lemma decoratedTerminalLogRatio_integrable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i)
    (hz1 : ∀ i, z i < 1) {H : X → ℝ} (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    Integrable (fun η => Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η)))
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact (decoratedCascade_log_second_moment_bound ν step hs n z hz hz0 hz1
    (finiteCascadeShifts ν step n z H)
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z
      (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z
      (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x)).1.integrable (by norm_num)

lemma finiteCascadeFractionalIntegrable_add_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} {G : Y → ℝ}
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) :
    finiteCascadeFractionalIntegrable (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2)))
      (fun q => H q.1+G q.2) n z := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rcases hIH with ⟨hHroot,hHtail⟩
    rcases hIG with ⟨hGroot,hGtail⟩
    constructor
    · intro x
      simp_rw [finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n
        (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail,mul_add,Real.exp_add]
      exact (hHroot x.1).mul_prod (hGroot x.2)
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CavityFiniteRPC
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityRPCStep_measurable (n d : ℕ) (σ τ : ℕ→ℝ) : Measurable (cavityRPCStep n d σ τ) :=
  ((canonicalCoordinateStep_measurable (n+1) σ).comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
    ((canonicalCoordinateStep_measurable d τ).comp (measurable_fst.snd.prodMk measurable_snd.snd))
lemma cavityRPCTerminal_measurable (n d : ℕ) (F : ℝ→ᵇℝ) : Measurable (cavityRPCTerminal n d F) := by
  have hv : Measurable (fun x : CavityRPCState n d=>logSphericalExp n (Real.sqrt (n+1:ℕ))
      (coordinateLeafField (n+1) x.1)) := (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))).continuous.measurable.comp
    ((coordinateLeafField_measurable (n+1)).comp measurable_fst)
  apply hv.add
  exact Finset.measurable_sum _ fun i _=>F.measurable.comp ((measurable_pi_apply 0).comp
    ((measurable_pi_apply i).comp measurable_snd))

theorem cavity_finiteRPC_conditional (n d k : ℕ) (σ τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (x : CavityRPCState n d) :
    Integrable (fun η=>Real.log (decoratedTerminalTotal (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k (x,η)/
        decoratedTerminalTotal (cavityRPCStep n d σ τ) (fun _=>0) k (x,η)))
      (decoratedCascadeLaw (cavityRPCMarkLaw n d) k z) ∧
    (∫ η,Real.log (decoratedTerminalTotal (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k (x,η)/
        decoratedTerminalTotal (cavityRPCStep n d σ τ) (fun _=>0) k (x,η))
      ∂decoratedCascadeLaw (cavityRPCMarkLaw n d) k z)=
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) (coordinateDepthField (n+1) k x.1)+
      ∑ i,finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun a=>F (a 0)) (x.2 i) := by
  have hF : Measurable (fun a : ℕ→ℝ=>F (a 0)) := F.measurable.comp (measurable_pi_apply 0)
  have hFI := finiteCascadeFractionalIntegrable_of_bounded standardGaussianMark
    (gaussianShiftStep τ) (gaussianShiftStep_measurable τ) k z hz0 hF
    (fun a=>F.norm_coe_le_norm (a 0))
  have hs := finiteCascade_sum_pi (fun _ : Fin d=>standardGaussianMark)
    (fun _=>gaussianShiftStep τ) k z (fun _ a=>F (a 0)) (fun _=>hFI)
  have hv := coordinateRecursion_eq_backward (n+1) σ
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) k z hz0
  have hi := finiteCascadeFractionalIntegrable_add_product
    (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
    (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep d τ) k z hz0 hv.2 hs.2
  constructor
  · exact decoratedTerminalLogRatio_integrable (cavityRPCMarkLaw n d) (cavityRPCStep n d σ τ)
      (cavityRPCStep_measurable n d σ τ) k z hz hz0 hz1
      (cavityRPCTerminal_measurable n d F) hi x
  · rw [finiteCascade_terminal_log_recursion_of_fractional (cavityRPCMarkLaw n d)
      (cavityRPCStep n d σ τ) (cavityRPCStep_measurable n d σ τ) k z hz hz0 hz1
      (cavityRPCTerminal_measurable n d F) hi x]
    exact (finiteCascadeLogRecursion_add_product
      (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
      (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
      (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep d τ) k z hz0 hv.2 hs.2 x.1 x.2).trans
      (congrArg₂ (fun a b : ℝ=>a+b) (hv.1 x.1) (hs.1 x.2))


lemma cavity_scalar_recursion_bound (k : ℕ) (τ : ℕ→ℝ) (z : Fin k→ℝ)
    (hz0 : ∀ i,0<z i) (F : ℝ→ᵇℝ) (x : ℕ→ℝ) :
    |finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
      (fun x=>F (x 0)) x|≤‖F‖ :=
  finiteCascadeLogRecursion_abs_le standardGaussianMark (gaussianShiftStep τ)
    (gaussianShiftStep_measurable τ) k z hz0
    (F.measurable.comp (measurable_pi_apply 0)) (fun a=>F.norm_coe_le_norm (a 0)) x

lemma cavity_scalar_root_pi_mean (d k : ℕ) (τ : ℕ→ℝ) (z : Fin k→ℝ)
    (hz0 : ∀ i,0<z i) (t : ℝ) (F : ℝ→ᵇℝ) :
    (∫ b : Fin d→ℝ, (∑ i,finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i))
      ∂(piMarkLaw (fun _ : Fin d=>standardGaussianMark) : Measure (Fin d→ℝ)))=
      d*cavityScalarRootValue k τ z t F := by
  have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
    (gaussianShiftStep_measurable τ) k z (F.measurable.comp (measurable_pi_apply 0))
  have hi (i : Fin d) : Integrable (fun b : Fin d→ℝ=>finiteCascadeLogRecursion
      standardGaussianMark (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i))
      (piMarkLaw (fun _ : Fin d=>standardGaussianMark)) := by
    apply Integrable.of_bound (hm.comp (Measurable.of_eval (fun _=>measurable_const.mul
      (measurable_pi_apply i)))).aestronglyMeasurable ‖F‖
    exact ae_of_all _ fun b=>by
      change |finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun x=>F (x 0)) (fun _=>t*b i)|≤‖F‖
      exact cavity_scalar_recursion_bound k τ z hz0 F _
  rw [integral_finsetSum _ (fun index _=>hi index)]
  have he (i : Fin d) : (∫ b : Fin d→ℝ,finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i)
      ∂(piMarkLaw (fun _ : Fin d=>standardGaussianMark) : Measure (Fin d→ℝ)))=
        cavityScalarRootValue k τ z t F := by
    have hmp := measurePreserving_eval (fun _ : Fin d=>(standardGaussianMark : Measure ℝ)) i
    unfold cavityScalarRootValue
    rw [←hmp.map_eq]
    exact (integral_map hmp.measurable.aemeasurable
      ((hm.comp (Measurable.of_eval (fun _=>measurable_const.mul measurable_id))).aestronglyMeasurable)).symm
  simp_rw [he]
  simp

theorem cavity_finiteRPC_roots (n d k : ℕ) (σ τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (r t : ℝ) :
    (∫ b, (∫ η,Real.log (decoratedTerminalTotal (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k (cavityRPCRootState n d r t b,η)/
        decoratedTerminalTotal (cavityRPCStep n d σ τ) (fun _=>0) k
          (cavityRPCRootState n d r t b,η))
      ∂decoratedCascadeLaw (cavityRPCMarkLaw n d) k z)
      ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)))=
      (n+1:ℕ)*amplitudeSphereValue n k σ z r+d*cavityScalarRootValue k τ z t F := by
  have hl := gaussianBackward_lipschitz (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) (cascadeHeatWord σ k z)
    (cascadeHeatWord_nonneg σ k z (fun i=>(hz0 i).le))
  let V := fun b : Fin (n+1)→ℝ=>gaussianBackward (stdGaussian (Spin (n+1)))
    (cascadeHeatWord σ k z) (logSphericalExp n (Real.sqrt (n+1:ℕ)))
      (r • WithLp.toLp 2 b)
  let W := fun b : Fin d→ℝ=>∑ i,finiteCascadeLogRecursion standardGaussianMark
    (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i)
  have hV : Integrable V (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark)) :=
    integrable_pi_standardGaussian (n+1) (hl.continuous.comp (continuous_id.const_smul r))
      (by simpa only [zero_add,Function.comp_def,Pi.smul_apply,id_eq] using (gaussian_integrable_lipschitz
        (stdGaussian (Spin (n+1))) hl r (0 : Spin (n+1))))
  have hW : Integrable W (piMarkLaw (fun _ : Fin d=>standardGaussianMark)) := by
    apply integrable_finsetSum
    intro i _
    have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
      (gaussianShiftStep_measurable τ) k z (F.measurable.comp (measurable_pi_apply 0))
    apply Integrable.of_bound (hm.comp (Measurable.of_eval (fun _=>measurable_const.mul
      (measurable_pi_apply i)))).aestronglyMeasurable ‖F‖
    exact ae_of_all _ fun b=>by
      change |finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun x=>F (x 0)) (fun _=>t*b i)|≤‖F‖
      exact cavity_scalar_recursion_bound k τ z hz0 F _
  simp_rw [(cavity_finiteRPC_conditional n d k σ τ F z hz hz0 hz1 _).2]
  change (∫ b,V b.1+W b.2 ∂(piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark) : Measure _).prod
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark)))=_
  rw [integral_add (hV.comp_fst _) (hW.comp_snd _),integral_fun_fst,integral_fun_snd]
  simp only [probReal_univ,one_smul]
  rw [show (∫ b,W b ∂(piMarkLaw (fun _ : Fin d=>standardGaussianMark) : Measure _))=
    d*cavityScalarRootValue k τ z t F from cavity_scalar_root_pi_mean d k τ z hz0 t F]
  congr 1
  have he := amplitudeSphereValue_eq_backward n k σ z hz hz0 hz1 r
  rw [gaussianBackward,gaussianEntropic_zero _ hl] at he
  simp only [zero_add] at he
  have hpi : (∫ b,V b ∂(piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark) : Measure _))=
      ∫ y,gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) (r • y) ∂stdGaussian (Spin (n+1)) :=
    integral_pi_standardGaussian (n+1) (show Continuous (fun y : Spin (n+1)=>
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) (r • y)) from
          hl.continuous.comp (continuous_id.const_smul r))
  rw [hpi,he]
  field_simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlledPrefix
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
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma heatLog_control_step_error (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      ∀ (s : ℝ≥0), s ≤ 1 → ∀ (X Z A : Ω → ℝ), AEMeasurable X P →
        HasLaw Z (gaussianReal 0 s) P → IndepFun X Z P → AEMeasurable A P →
        (∀ ω, |A ω| ≤ (L : ℝ)*s) →
        |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, heatLog s d g.f (X ω) ∂P) -
          (∫ ω, g.d1 (X ω)*A ω ∂P) + (d : ℝ)*(s : ℝ)/2 * (∫ ω, (g.d1 (X ω))^2 ∂P)| ≤
          (C : ℝ)*(s : ℝ)*Real.sqrt s := by
  obtain ⟨C,hC⟩ := heatLog_generator_uniform d C₀ C₁ C₂ C₃
  let M₁ := ∫ z : ℝ, |z| ∂gaussianReal 0 1
  let M₃ := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM₁ : 0 ≤ M₁ := integral_nonneg (fun z => abs_nonneg z)
  have hM₃ : 0 ≤ M₃ := integral_nonneg (fun z => by positivity)
  let K := (C₂ : ℝ)*((L : ℝ)*M₁+(L : ℝ)^2/2) + (C₃ : ℝ)/6*M₃
  have hK : 0 ≤ K := by positivity
  refine ⟨⟨K+C, by positivity⟩, ?_⟩
  intro Ω _ P _ g h₀ h₁ h₂ h₃ s hs X Z A hX hZ hI hA hAK
  have hG := gaussian_drift_taylor_mean_bound g.f g.contDiff C₁ C₃ C₂ (L*s)
    (fun y => by rw [g.deriv_eq]; exact (g.d1.norm_coe_le_norm y).trans h₁)
    (fun y => by rw [g.deriv2_eq]; exact (g.d2.norm_coe_le_norm y).trans h₂)
    (fun y => by rw [g.deriv3_eq]; exact (g.d3.norm_coe_le_norm y).trans h₃)
    hX hZ hI hA (by simpa only [NNReal.coe_mul] using hAK)
  rw [g.deriv_eq, g.deriv2_eq] at hG
  have hs0 := s.coe_nonneg
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := Real.sqrt_le_one.mpr hs
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith [Real.sq_sqrt hs0]
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ)*Real.sqrt s := by nlinarith [Real.sq_sqrt hs0]
  have hG' : |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P)| ≤
      K*(s : ℝ)*Real.sqrt s := by
    refine hG.trans ?_
    simp only [NNReal.coe_mul, hrcube]
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsr hs0)
      (show 0 ≤ (C₂ : ℝ)*(L : ℝ)^2/2 by positivity)
    dsimp [K,M₁,M₃] at *
    nlinarith only [ht]
  have hiF := boundedContinuousFunction_integrable_comp g.f hX
  have hiH := boundedContinuousFunction_integrable_comp (heatLogBCF s d g.f) hX
  change Integrable (fun ω => heatLog s d g.f (X ω)) P at hiH
  have hi₂ := boundedContinuousFunction_integrable_comp g.d2 hX
  have hi₁₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hX
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₁₂
  let R := fun ω => heatLog s d g.f (X ω) - g.f (X ω) -
    (s : ℝ)/2*(g.d2 (X ω)+(d : ℝ)*(g.d1 (X ω))^2)
  have hiR : Integrable R P := (hiH.sub hiF).sub ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
  have hR : |∫ ω, R ω ∂P| ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (f := R) (μ := P) (Filter.Eventually.of_forall fun ω =>
        show ‖R ω‖ ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s by
          simpa only [Real.norm_eq_abs, R] using hC g h₀ h₁ h₂ h₃ s hs (X ω))
  have hRe : (∫ ω, R ω ∂P) = (∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)) := by
    have he := integral_sub (hiH.sub hiF) ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
    simp only [Pi.sub_apply, Pi.add_apply] at he
    dsimp only [R]
    rw [he, integral_sub hiH hiF, integral_const_mul, integral_add hi₂ (hi₁₂.const_mul d), integral_const_mul]
  rw [hRe] at hR
  have hh := abs_sub
    ((∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P))
    ((∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)))
  have hh' := hh.trans (add_le_add hG' hR)
  convert! hh' using 1
  · congr 1; ring
  · change (K+(C : ℝ))*(s : ℝ)*Real.sqrt s = K*(s : ℝ)*Real.sqrt s + (C : ℝ)*(s : ℝ)*Real.sqrt s
    ring

lemma usualBrownianSigma_mono (P : Measure BrownianPath) {s t : Time} (hst : s ≤ t) :
    usualBrownianSigma P s ≤ usualBrownianSigma P t := by
  apply le_iInf
  intro r
  exact iInf_le_of_le (⟨r.val, lt_of_le_of_lt hst r.property⟩ : {r : ℝ≥0 // (s : ℝ) < r}) le_rfl

lemma brownianEval_usual_measurable (P : Measure BrownianPath) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (brownianEval ⟨t.val,t.property.1⟩) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro r
  apply le_sup_of_le_left
  exact le_iSup_of_le (⟨⟨t.val,t.property.1⟩, r.property.le⟩ : {s : ℝ≥0 // s ≤ r.val}) le_rfl

lemma progressive_prefix_integral_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
  let : MeasurableSpace BrownianPath := usualBrownianSigma P t
  have hm : Measurable (fun p : Set.Iic t × BrownianPath => a p.1.val * v p.1.val p.2) :=
    (ha.comp (measurable_subtype_coe.comp measurable_fst)).mul (hv t)
  have hi := hm.stronglyMeasurable.integral_prod_left (f := fun r ω => a r.val * v r.val ω) (μ := Measure.comap Subtype.val timeLaw)
  have he : (fun ω => ∫ r : Set.Iic t, a r.val * v r.val ω ∂Measure.comap Subtype.val timeLaw) =
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
    funext ω
    exact integral_subtype_comap (μ := timeLaw) (s := Set.Iic t) measurableSet_Iic (fun r => a r * v r ω)
  rw [he] at hi
  exact hi.measurable

lemma progressive_interval_integral_aemeasurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (s t : Time) :
    AEMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P := by
  have hm := (ha.comp measurable_fst).mul (progressive_joint_complete P hv)
  have hi := hm.stronglyMeasurable.integral_prod_left (β := NullMeasurableSpace BrownianPath P)
    (f := fun r ω => a r * v r ω) (μ := timeLaw.restrict (Set.Ioc s t))
  exact (show NullMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P from hi.measurable).aemeasurable

lemma controlledPrefix_usual_measurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) (controlledPrefix m v t) :=
  (brownianEval_usual_measurable P t).add (progressive_prefix_integral_measurable P hv m m.measurable t)

lemma timeSpan_coe {s t : Time} (hst : s ≤ t) :
    (timeSpan s t : ℝ) = (t : ℝ)-(s : ℝ) := Real.coe_toNNReal _ (sub_nonneg.mpr hst)

lemma timeSpan_le_one (s t : Time) : timeSpan s t ≤ 1 := by
  apply Real.toNNReal_le_one.mpr
  linarith [t.property.2,s.property.1]

lemma timeLaw_real_Ioc {s t : Time} (hst : s ≤ t) :
    timeLaw.real (Set.Ioc s t) = (t : ℝ)-(s : ℝ) := by
  simp only [timeLaw_eq_volume, Measure.real, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]

lemma timeLaw_integral_const_Ioc {s t : Time} (hst : s ≤ t) (a : ℝ) :
    (∫ _r in Set.Ioc s t, a ∂timeLaw) = ((t : ℝ)-(s : ℝ))*a := by
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, ← Measure.real,
    timeLaw_real_Ioc hst, smul_eq_mul]

lemma bounded_control_integrable (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    Integrable (fun r => m r * v r ω^2) timeLaw ∧ Integrable (fun r => m r * v r ω) timeLaw :=
  weightedTime_integrable m (progressive_time_measurable P hv ω)
    ((pathControlCost_le_bound m L hL ω).trans_lt (by finiteness))

lemma controlledPrefix_increment (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    controlledPrefix m v t ω = controlledPrefix m v s ω +
      (brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω) +
      ∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw := by
  have hi := (bounded_control_integrable P m L hv hL ω).2
  have he := setIntegral_union (s := Set.Iic s) (t := Set.Ioc s t)
    (Set.Iic_disjoint_Ioc (a := s) (c := t) le_rfl) measurableSet_Ioc
    hi.integrableOn hi.integrableOn
  rw [Set.Iic_union_Ioc_eq_Iic hst] at he
  unfold controlledPrefix
  rw [he]
  ring

lemma bounded_interval_drift (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    |∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw| ≤ (L : ℝ) * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm (L : ℝ)]
  calc
    _ ≤ ∫ r in Set.Ioc s t, |m r*v r ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ) ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).2.integrableOn.abs (integrable_const _)
      intro r
      change |m r * v r ω| ≤ (L : ℝ)
      rw [abs_mul, abs_of_nonneg (m.nonneg r)]
      exact (mul_le_mul_of_nonneg_left (hL r ω) (m.nonneg r)).trans
        (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst L

lemma intervalControlCost_nonneg (m : Trial) (v : Time → BrownianPath → ℝ) (s t : Time) (ω : BrownianPath) :
    0 ≤ intervalControlCost m v s t ω := integral_nonneg (fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))

lemma intervalControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time) :
    AEMeasurable (intervalControlCost m v s t) P :=
  progressive_interval_integral_aemeasurable P (fun r => (hv r).pow_const 2) m m.measurable s t

lemma intervalControlCost_le_bound (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    intervalControlCost m v s t ω ≤ (L : ℝ)^2 * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm ((L : ℝ)^2)]
  calc
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ)^2 ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).1.integrableOn (integrable_const _)
      intro r
      have hh : (v r ω)^2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) L.coe_nonneg).mpr (hL r ω)
      exact (mul_le_mul_of_nonneg_left hh (m.nonneg r)).trans (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst _

lemma intervalControlCost_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ t ω, |v t ω| ≤ L) {s t : Time} (hst : s ≤ t) :
    Integrable (intervalControlCost m v s t) P :=
  bounded_real_integrable (intervalControlCost_aemeasurable P m hv s t) ((L : ℝ)^2*timeSpan s t)
    (Filter.Eventually.of_forall fun ω => by
      rw [abs_of_nonneg (intervalControlCost_nonneg m v s t ω)]
      exact intervalControlCost_le_bound P m L hv hL hst ω)

lemma interval_square_completion (P : Measure BrownianPath) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (hm : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ))
    (a : ℝ) (ω : BrownianPath) :
    2*a*(∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw) -
      (d : ℝ)*(timeSpan s t : ℝ)*a^2 ≤ intervalControlCost m v s t ω := by
  have hi := bounded_control_integrable P m L hv hL ω
  have him : Integrable (fun r => m r) timeLaw := by
    apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (m.nonneg r)]; exact m.le_one r
  have hmono := setIntegral_mono_on (s := Set.Ioc s t) ((hi.2.const_mul (2*a)).sub (him.const_mul (a^2))).integrableOn
    hi.1.integrableOn measurableSet_Ioc (fun r _ => by
      change 2*a*(m r*v r ω) - a^2*m r ≤ m r*(v r ω)^2
      nlinarith [mul_nonneg (m.nonneg r) (sq_nonneg (v r ω-a))])
  have he : (∫ r in Set.Ioc s t, m r ∂timeLaw) = (d : ℝ)*timeSpan s t := by
    rw [setIntegral_congr_fun measurableSet_Ioc hm, timeLaw_integral_const_Ioc hst, timeSpan_coe hst, mul_comm]
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hi.2.const_mul (2*a)).integrableOn (him.const_mul (a^2)).integrableOn,
    integral_const_mul, integral_const_mul, he] at hmono
  convert! hmono using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma brownian_increment_timeSpan (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {s t : Time} (hst : s ≤ t) :
    HasLaw (fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω)
      (gaussianReal 0 (timeSpan s t)) P := by
  have he : timeSpan s t = nndist (t : ℝ) (s : ℝ) := by
    apply NNReal.coe_injective
    rw [timeSpan_coe hst, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
  rw [he]
  exact (hB.toIsPreBrownianReal.hasLaw_sub ⟨t.val,t.property.1⟩ ⟨s.val,s.property.1⟩).congr
    (Filter.Eventually.of_forall fun ω => rfl)

lemma brownian_control_cell_upper (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) ≤
        (∫ ω, intervalControlCost m v s t ω ∂P)/2 +
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃
  let X := controlledPrefix m v s
  let Z := fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω
  let A := fun ω => ∫ r in Set.Ioc s t, m r*v r ω ∂timeLaw
  have hX := controlledPrefix_usual_measurable P m hv s
  have hXm : AEMeasurable X P := usual_measurable_aemeasurable P s hX
  have hAm : AEMeasurable A P := progressive_interval_integral_aemeasurable P hv m m.measurable s t
  have hAb : ∀ ω, |A ω| ≤ (L : ℝ)*timeSpan s t := bounded_interval_drift P m L hv hL hst.le
  have he := hC P g h₀ h₁ h₂ h₃ (timeSpan s t) (timeSpan_le_one s t) X Z A hXm
    (brownian_increment_timeSpan P hB hst.le)
    (brownian_increment_indep_adapted P hB s ⟨t.val,t.property.1⟩ hst hX) hAm hAb
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := by
    intro ω
    exact (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hi₁ := boundedContinuousFunction_integrable_comp g.d1 hXm
  have hi₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hXm
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₂
  have hiA := bounded_real_integrable hAm ((L : ℝ)*timeSpan s t) (Filter.Eventually.of_forall hAb)
  have hiJ : Integrable (fun ω => g.d1 (X ω)*A ω) P :=
    hiA.bdd_mul ((g.d1.continuous.measurable.comp_aemeasurable hXm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => g.d1.norm_coe_le_norm (X ω))
  have hq := integral_mono ((hiJ.const_mul 2).sub (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))))
    (intervalControlCost_integrable P m L hv hL hst.le)
    (fun ω => by
      change 2*(g.d1 (X ω)*A ω) - (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 ≤ _
      nlinarith only [interval_square_completion P m L d hv hL hst.le hm (g.d1 (X ω)) ω])
  simp only [Pi.sub_apply] at hq
  rw [integral_sub (hiJ.const_mul 2) (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))),
    integral_const_mul, integral_const_mul] at hq
  exact le_trans (by linarith only [(abs_le.mp he).2,hq]) le_rfl

lemma antitoneOn_of_superlinear_increment (F : Time → ℝ) (C : ℝ)
    {a b : Time} (hab : a ≤ b)
    (h : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt ((t : ℝ)-(s : ℝ))) : F b ≤ F a := by
  have hbnd : ∀ n : ℕ, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt (((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro s hs t ht hst
      have hstreal : (s : ℝ) < (t : ℝ) := hst
      let u : Time := ⟨((s : ℝ)+(t : ℝ))/2, by
        constructor <;> linarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
      have hsu : s < u := by change (s : ℝ) < ((s : ℝ)+(t : ℝ))/2; linarith only [hstreal]
      have hut : u < t := by change ((s : ℝ)+(t : ℝ))/2 < (t : ℝ); linarith only [hstreal]
      have hu : u ∈ Set.Icc a b := ⟨hs.1.trans hsu.le,hut.le.trans ht.2⟩
      have h₁ := ih s hs u hu hsu
      have h₂ := ih u hu t ht hut
      have e₁ : (u : ℝ)-(s : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      have e₂ : (t : ℝ)-(u : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      rw [e₁] at h₁
      rw [e₂] at h₂
      have e₃ : ((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^(n+1) = (((t : ℝ)-(s : ℝ))/2)*(1/2 : ℝ)^n := by rw [pow_succ]; ring
      rw [e₃]
      linarith only [h₁,h₂]
  rcases hab.eq_or_lt with heq | hlt
  · simp [heq]
  have hlim : Tendsto (fun n : ℕ => C*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))*(1/2 : ℝ)^n)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    simpa using (hp.const_mul ((b : ℝ)-(a : ℝ))).sqrt.const_mul (C*((b : ℝ)-(a : ℝ)))
  have he := ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hbnd n a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hlt)
  linarith only [he]

lemma timeSpan_add {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    timeSpan a b + timeSpan b c = timeSpan a c := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add,timeSpan_coe hab,timeSpan_coe hbc,timeSpan_coe (hab.trans hbc)]
  ring

lemma intervalControlCost_add (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) (ω : BrownianPath) :
    intervalControlCost m v a c ω = intervalControlCost m v a b ω + intervalControlCost m v b c ω := by
  have hi := (bounded_control_integrable P m L hv hL ω).1
  have he := setIntegral_union (s := Set.Ioc a b) (t := Set.Ioc b c)
    (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi.integrableOn hi.integrableOn
  rwa [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at he

lemma expected_intervalControlCost_add (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ r ω, |v r ω| ≤ L) {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ ω, intervalControlCost m v a c ω ∂P) =
      (∫ ω, intervalControlCost m v a b ω ∂P) + (∫ ω, intervalControlCost m v b c ω ∂P) := by
  simp only [intervalControlCost_add P m L hv hL hab hbc]
  exact integral_add (intervalControlCost_integrable P m L hv hL hab)
    (intervalControlCost_integrable P m L hv hL hbc)

lemma brownian_control_interval_upper (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b : Time} (hab : a ≤ b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) (g : Jet3) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) ≤
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  obtain ⟨C,hC⟩ := brownian_control_cell_upper d L C₀ C₁ C₂ C₃
  let F : Time → ℝ := fun t =>
    (∫ ω, heatLog (timeSpan t b) d g.f (controlledPrefix m v t ω) ∂P) -
      (∫ ω, intervalControlCost m v a t ω ∂P)/2
  have hF := antitoneOn_of_superlinear_increment F (C : ℝ) hab (by
    intro s hs t ht hst
    have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
    obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
    have hh := hC P hB m v hv hL s t hst hmst (g.heatLog (timeSpan t b) d) h₀ h₁ h₂ h₃
    rw [g.heatLog_f] at hh
    simp only [heatLogBCF_coe, heatLog_semigroup, timeSpan_add hst.le ht.2] at hh
    have hcost := expected_intervalControlCost_add P m L hv hL hs.1 hst.le
    rw [timeSpan_coe hst.le] at hh
    dsimp [F]
    linarith only [hh,hcost])
  have he₁ : timeSpan b b = 0 := by simp [timeSpan]
  have he₂ : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  dsimp [F] at hF
  simp only [he₁,heatLog_zero,he₂,integral_zero,zero_div,sub_zero] at hF
  linarith only [hF]

lemma progressive_patchControl (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time)
    {a : BrownianPath → ℝ} (ha : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) a) :
    Progressive P (patchControl v s t a) := by
  intro T
  by_cases hs : s ≤ T
  · have haT := ha.mono (usualBrownianSigma_mono P hs) le_rfl
    apply Measurable.ite _ (haT.comp measurable_snd) (hv T)
    exact (measurableSet_Ioc : MeasurableSet (Set.Ioc s t)).preimage
      (measurable_subtype_coe.comp measurable_fst)
  · have he : (fun p : Set.Iic T × BrownianPath => patchControl v s t a p.1.val p.2) =
        (fun p : Set.Iic T × BrownianPath => v p.1.val p.2) := by
      funext p
      apply ite_eq_right
      intro h
      exact hs (h.1.le.trans p.1.property)
    rw [he]
    exact hv T

lemma patchControl_bound {v : Time → BrownianPath → ℝ} {L : ℝ≥0}
    (hv : ∀ r ω, |v r ω| ≤ L) (s t : Time) {a : BrownianPath → ℝ}
    (ha : ∀ ω, |a ω| ≤ L) : ∀ r ω, |patchControl v s t a r ω| ≤ L := by
  intro r ω
  simp only [patchControl]
  split <;> first | exact ha ω | exact hv r ω

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BackwardScore
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
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma patchControl_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    controlledPrefix m (patchControl v s t a) r ω = controlledPrefix m v r ω := by
  unfold controlledPrefix
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma patchControl_cost_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) (q : Time) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    intervalControlCost m (patchControl v s t a) q r ω = intervalControlCost m v q r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.2.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma brownian_control_feedback_cell (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∀ r ∈ Set.Ioc s t, ∀ ω, v r ω = g.d1 (controlledPrefix m v s ω)) →
      |(∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) -
        (∫ ω, intervalControlCost m v s t ω ∂P)/2| ≤
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃ hV
  let X := controlledPrefix m v s
  let Z := fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω
  let A := fun ω => ∫ r in Set.Ioc s t, m r*v r ω ∂timeLaw
  have hX := controlledPrefix_usual_measurable P m hv s
  have hXm : AEMeasurable X P := usual_measurable_aemeasurable P s hX
  have hAm : AEMeasurable A P := progressive_interval_integral_aemeasurable P hv m m.measurable s t
  have hAb : ∀ ω, |A ω| ≤ (L : ℝ)*timeSpan s t := bounded_interval_drift P m L hv hL hst.le
  have he := hC P g h₀ h₁ h₂ h₃ (timeSpan s t) (timeSpan_le_one s t) X Z A hXm
    (brownian_increment_timeSpan P hB hst.le)
    (brownian_increment_indep_adapted P hB s ⟨t.val,t.property.1⟩ hst hX) hAm hAb
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := fun ω =>
    (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hA : ∀ ω, A ω = (d : ℝ)*(timeSpan s t : ℝ)*g.d1 (X ω) := by
    intro ω
    dsimp only [A]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hQ : ∀ ω, intervalControlCost m v s t ω =
      (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 := by
    intro ω
    rw [intervalControlCost,setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hJ : (∫ ω, g.d1 (X ω)*A ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hA]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by ring
  have hQi : (∫ ω, intervalControlCost m v s t ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hQ,integral_const_mul]
  rw [hJ] at he
  rw [hQi]
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma brownian_control_patch_gain (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ (v : Time → BrownianPath → ℝ), Progressive P v →
      (∀ r ω, |v r ω| ≤ L) → ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc s t, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g s - (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) ≤
          backwardScore P m w a b d g t := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  let L := max L₀ C₁
  obtain ⟨C,hC⟩ := brownian_control_feedback_cell d L C₀ C₁ C₂ C₃
  refine ⟨L,C,le_max_left _ _,?_⟩
  intro v hv hL s hs t ht hst
  let j := g.heatLog (timeSpan t b) d
  let A := fun ω => j.d1 (controlledPrefix m v s ω)
  have hAm : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) A :=
    j.d1.continuous.measurable.comp (controlledPrefix_usual_measurable P m hv s)
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
  have hAL : ∀ ω, |A ω| ≤ L := fun ω =>
    ((j.d1.norm_coe_le_norm _).trans h₁).trans (show (C₁ : ℝ) ≤ L from le_max_right _ _)
  let w := patchControl v s t A
  have hw : Progressive P w := progressive_patchControl P hv s t hAm
  have hwL : ∀ r ω, |w r ω| ≤ L := patchControl_bound hL s t hAL
  have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
  have hXe : ∀ ω, controlledPrefix m w s ω = controlledPrefix m v s ω :=
    patchControl_prefix m v s t A le_rfl
  have hQe : ∀ ω, intervalControlCost m w a s ω = intervalControlCost m v a s ω :=
    patchControl_cost_prefix m v s t A a le_rfl
  have hfeedback : ∀ r ∈ Set.Ioc s t, ∀ ω, w r ω = j.d1 (controlledPrefix m w s ω) := by
    intro r hr ω
    rw [hXe]
    exact ite_eq_left hr
  have hh := hC P hB m w hw hwL s t hst hmst j h₀ h₁ h₂ h₃ hfeedback
  change |(∫ ω, (g.heatLog (timeSpan t b) d).f (controlledPrefix m w t ω) ∂P) - _ - _| ≤ _ at hh
  rw [g.heatLog_f] at hh
  simp only [heatLogBCF_coe,heatLog_semigroup,timeSpan_add hst.le ht.2,hXe] at hh
  have hcost := expected_intervalControlCost_add P m L hw hwL hs.1 hst.le
  simp only [hQe] at hcost
  refine ⟨w,hw,hwL,?_,?_⟩
  · intro r hr ω
    exact ite_eq_right hr
  · dsimp [backwardScore]
    linarith only [(abs_le.mp hh).1,hcost]

lemma timeMesh_coe (a b : Time) (n k : ℕ) (hk : k ≤ n+1) :
    (timeMesh a b n k : ℝ) = (a : ℝ)+((b : ℝ)-(a : ℝ))*((k : ℝ)/(n+1)) := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hh : (k : ℝ)/(n+1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hp).mpr
      exact_mod_cast hk
  simp only [timeMesh, Set.projIcc_of_mem zero_le_one hh, Set.Icc.coe_convexComb]
  ring

lemma timeMesh_zero (a b : Time) (n : ℕ) : timeMesh a b n 0 = a := by
  apply Subtype.ext
  rw [timeMesh_coe a b n 0 (Nat.zero_le _)]
  simp

lemma timeMesh_last (a b : Time) (n : ℕ) : timeMesh a b n (n+1) = b := by
  apply Subtype.ext
  rw [timeMesh_coe a b n (n+1) le_rfl]
  push_cast
  rw [div_self (by positivity : (n : ℝ)+1 ≠ 0)]
  ring

lemma timeMesh_between {a b : Time} (hab : a ≤ b) (n k : ℕ) (hk : k ≤ n+1) :
    timeMesh a b n k ∈ Set.Icc a b := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hq : 0 ≤ (k : ℝ)/(n+1) := by positivity
  have hr : (k : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr (by exact_mod_cast hk)
  have habr : (a : ℝ) ≤ (b : ℝ) := hab
  constructor <;> change _ ≤ (show ℝ from ↑_)
  · rw [timeMesh_coe a b n k hk]
    nlinarith
  · rw [timeMesh_coe a b n k hk]
    nlinarith

lemma timeMesh_step {a b : Time} (hab : a < b) (n k : ℕ) (hk : k < n+1) :
    timeMesh a b n k < timeMesh a b n (k+1) := by
  change (timeMesh a b n k : ℝ) < (timeMesh a b n (k+1) : ℝ)
  rw [timeMesh_coe a b n k hk.le, timeMesh_coe a b n (k+1) hk]
  have hh : (a : ℝ) < (b : ℝ) := hab
  have hp : (0 : ℝ) < n+1 := by positivity
  apply add_lt_add_of_le_of_lt le_rfl
  apply mul_lt_mul_of_pos_left _ (sub_pos.mpr hh)
  apply div_lt_div_of_pos_right _ hp
  exact_mod_cast Nat.lt_succ_self k

lemma timeMesh_step_size (a b : Time) (n k : ℕ) (hk : k < n+1) :
    (timeMesh a b n (k+1) : ℝ) - (timeMesh a b n k : ℝ) = ((b : ℝ)-(a : ℝ))/(n+1) := by
  rw [timeMesh_coe a b n k hk.le,timeMesh_coe a b n (k+1) hk]
  push_cast
  ring

lemma brownian_control_interval_lower_mesh (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ n : ℕ,
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) -
          (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,hLL,hgain⟩ := brownian_control_patch_gain P hB m d L₀ g hm
  refine ⟨L,C,hLL,?_⟩
  intro n
  let τ := timeMesh a b n
  let δ : ℝ := ((b : ℝ)-(a : ℝ))/(n+1)
  let E : ℝ := (C : ℝ)*δ*Real.sqrt δ
  have hind : ∀ k : ℕ, k ≤ n+1 →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g a - (k : ℝ)*E ≤ backwardScore P m w a b d g (τ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨v,hv,fun r ω => (hvL r ω).trans (show (L₀ : ℝ) ≤ L from hLL),?_,?_⟩
      · intro _ _ _; rfl
      · simp only [τ,timeMesh_zero,Nat.cast_zero,zero_mul,sub_zero,le_refl]
    | succ k ih =>
      intro hk
      obtain ⟨u,hu,huL,huout,huScore⟩ := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hk' : k < n+1 := hk
      have hs := timeMesh_between hab.le n k hk'.le
      have ht := timeMesh_between hab.le n (k+1) hk
      have hst := timeMesh_step hab n k hk'
      obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hgain u hu huL (τ k) hs (τ (k+1)) ht hst
      have heδ : (timeSpan (τ k) (τ (k+1)) : ℝ) = δ := by
        rw [timeSpan_coe hst.le]
        exact timeMesh_step_size a b n k hk'
      rw [heδ] at hwScore
      refine ⟨w,hw,hwL,?_,?_⟩
      · intro r hr ω
        have hr' : r ∉ Set.Ioc (τ k) (τ (k+1)) := fun hh =>
          hr ⟨hs.1.trans_lt hh.1,hh.2.trans ht.2⟩
        rw [hwout r hr' ω]
        exact huout r hr ω
      · change backwardScore P m u a b d g (τ k) - E ≤ _ at hwScore
        rw [Nat.cast_succ]
        linarith only [huScore,hwScore]
  obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hind (n+1) le_rfl
  have he : ((n+1 : ℕ) : ℝ)*E =
      (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) := by
    dsimp [E,δ]
    push_cast
    field_simp
  have hz : timeSpan b b = 0 := by simp [timeSpan]
  have hq : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  simp only [τ,timeMesh_last,he,backwardScore,hz,heatLog_zero,hq,integral_zero,zero_div,sub_zero] at hwScore
  exact ⟨w,hw,hwL,hwout,hwScore⟩

lemma brownian_control_interval_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,_,hmesh⟩ := brownian_control_interval_lower_mesh P hB m d L₀ g hab hm v hv hvL
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => ((b : ℝ)-(a : ℝ))/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have he : Tendsto (fun n : ℕ => (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)))
      atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hd).const_mul ((C : ℝ)*((b : ℝ)-(a : ℝ)))
  obtain ⟨n,hn⟩ := (he.eventually (gt_mem_nhds hε)).exists
  obtain ⟨w,hw,hwL,hwout,hwval⟩ := hmesh n
  exact ⟨L,w,hw,hwL,hwout,by linarith⟩

lemma HeatChain.left_le_right {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) : a ≤ b := by
  cases H with
  | nil => exact le_rfl
  | cons _ hat htb _ _ => exact hat.le.trans htb

lemma controls_equal_cost_prefix {m : Trial} {v w : Time → BrownianPath → ℝ} {a b r s : Time}
    (h : ∀ t ∉ Set.Ioc a b, ∀ ω, w t ω = v t ω) (hr : r ≤ a) (ω : BrownianPath) :
    intervalControlCost m w s r ω = intervalControlCost m v s r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [h t (fun hh => not_lt_of_ge (ht.2.trans hr) hh.1) ω]

lemma HeatChain.upper {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 ≤
        (∫ ω, h.f (controlledPrefix m v a ω) ∂P) := by
  induction H with
  | nil a => simp [intervalControlCost]
  | @cons a t b h d hat htb hm tail ih =>
    have hi := brownian_control_interval_upper P hB m L d hv hL hat.le hm h
    have hc := expected_intervalControlCost_add P m L hv hL hat.le htb
    rw [Jet3.heatLog_f]
    simp only [heatLogBCF_coe]
    linarith only [ih,hi,hc]

lemma HeatChain.lower {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ K) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, h.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  induction H generalizing v L ε with
  | nil a =>
    refine ⟨L,v,hv,hL,fun _ _ _ => rfl,?_⟩
    simp only [intervalControlCost,Set.Ioc_self,Measure.restrict_empty,integral_zero_measure,
      integral_zero,zero_div,sub_zero]
    linarith
  | @cons a t b h d hat htb hm tail ih =>
    obtain ⟨K,u,hu,huK,huout,huval⟩ :=
      brownian_control_interval_lower P hB m d L h hat hm v hv hL (by positivity : 0 < ε/2)
    obtain ⟨K',w,hw,hwK,hwout,hwval⟩ := ih K u hu huK (by positivity : 0 < ε/2)
    have hc := expected_intervalControlCost_add P m K' hw hwK hat.le htb
    have he : ∀ ω, intervalControlCost m w a t ω = intervalControlCost m u a t ω :=
      controls_equal_cost_prefix hwout le_rfl
    simp only [he] at hc
    refine ⟨K',w,hw,hwK,?_,?_⟩
    · intro r hr ω
      rw [hwout r (fun hh => hr ⟨hat.trans hh.1,hh.2⟩) ω]
      exact huout r (fun hh => hr ⟨hh.1,hh.2.trans htb⟩) ω
    · rw [Jet3.heatLog_f]
      simp only [heatLogBCF_coe]
      linarith only [huval,hwval,hc]

lemma controlledPrefix_one (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    controlledPrefix m v 1 ω = brownianEval 1 ω + controlDrift m v ω := by
  simp only [controlledPrefix,controlDrift,show Set.Iic (1 : Time) = Set.univ from Set.Iic_top,
    Measure.restrict_univ]
  rfl

lemma controlledPrefix_zero (P : Measure BrownianPath) (hB : IsBrownianReal brownianEval P)
    (m : Trial) (v : Time → BrownianPath → ℝ) : controlledPrefix m v 0 =ᵐ[P] fun _ => 0 := by
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  simp only [controlledPrefix,show Set.Iic (0 : Time) = {0} from Set.Iic_bot,
    Measure.restrict_singleton,measure_singleton,zero_smul,integral_zero_measure,add_zero]
  exact hω

lemma intervalControlCost_full (m : Trial) (v : Time → BrownianPath → ℝ)
    (ω : BrownianPath) (hm : Measurable (v · ω)) :
    intervalControlCost m v 0 1 ω = (pathControlCost m v ω).toReal := by
  unfold intervalControlCost
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := timeLaw)), show Set.Icc (0 : Time) 1 = Set.univ from Set.Icc_bot_top,
    Measure.restrict_univ]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))
    ((m.measurable.mul (hm.pow_const 2)).aestronglyMeasurable)

lemma expected_intervalControlCost_full (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, intervalControlCost m v 0 1 ω ∂P) = (controlCost P m v).toReal := by
  simp only [intervalControlCost_full m v _ (progressive_time_measurable P hv _)]
  exact integral_pathControlCost P m hv hc

lemma Jet3.lipschitz (g : Jet3) : LipschitzWith ‖g.d1‖₊ g.f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (g.has1 x).differentiableAt)
  intro x
  rw [g.deriv_eq]
  exact_mod_cast g.d1.norm_coe_le_norm x

lemma HeatChain.controlValue_eq {m : Trial} {g h : Jet3}
    (H : HeatChain m g 0 1 h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) : controlValue P g.f m = h.f 0 := by
  apply le_antisymm
  · apply controlValue_le_of_bounded_controls P g.f m ‖g.d1‖₊ g.lipschitz
    intro v hv hc hL
    have hh := H.upper P hB ‖g.d1‖₊ hv hL
    have he : (∫ ω, h.f (controlledPrefix m v 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m v] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hv hc] at hh
    simp only [controlledPrefix_one] at hh
    exact hh
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨K,w,hw,hwK,_,hwval⟩ := H.lower P hB 0 (fun _ _ => 0) (progressive_zero P)
      (by simp) hε
    have hc : controlCost P m w < ∞ := (controlCost_le_bound P m K hwK).trans_lt (by finiteness)
    have he : (∫ ω, h.f (controlledPrefix m (fun _ _ => 0) 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m (fun _ _ => 0)] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hw hc] at hwval
    simp only [controlledPrefix_one] at hwval
    have hsup : controlPayoff P g.f m w ≤ controlValue P g.f m :=
      le_csSup (controlPayoffs_bddAbove P g.f m) ⟨w,hw,hc,rfl⟩
    change h.f 0 - ε ≤ controlPayoff P g.f m w at hwval
    linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
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
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma Jet3.eq_of_f_eq {g h : Jet3} (he : g.f=h.f) : g=h := by
  have h1 : g.d1=h.d1 := by
    ext x
    rw [← g.deriv_eq,← h.deriv_eq,he]
  have h2 : g.d2=h.d2 := by
    ext x
    rw [← g.deriv2_eq,← h.deriv2_eq,he]
  have h3 : g.d3=h.d3 := by
    ext x
    rw [← g.deriv3_eq,← h.deriv3_eq,he]
  cases g
  cases h
  simp_all

lemma Jet3.heatLog_zero_time (g : Jet3) (d : ℝ≥0) : g.heatLog 0 d=g := by
  apply Jet3.eq_of_f_eq
  ext x
  simp only [Jet3.heatLog_f,heatLogBCF_coe,heatLog_zero]

lemma finiteStepControlJet_chain (g : Jet3) (m : Trial) (n : ℕ)
    (q : Fin (n+1)→Time) (d : Fin n→ℝ≥0) (hq : Monotone q)
    (hm : ∀ i : Fin n, ∀ r∈Ioc (q i.castSucc) (q i.succ), m r=(d i:ℝ)) :
    HeatChain m g (q 0) (q (Fin.last n)) (finiteStepControlJet g n q d) := by
  induction n with
  | zero => exact HeatChain.nil (q 0)
  | succ n ih =>
    have ih' := ih (fun i => q i.succ) (fun i => d i.succ)
      (hq.comp (Fin.strictMono_succ.monotone)) (fun i => hm i.succ)
    change HeatChain m g (q 1) (q (Fin.last (n+1))) _ at ih'
    have h01 : q 0≤q 1 := hq (Fin.zero_le _)
    rcases lt_or_eq_of_le h01 with hlt | he
    · exact HeatChain.cons (d 0) hlt (hq (Fin.le_last _)) (hm 0) ih'
    · simpa only [finiteStepControlJet,he,timeSpan,sub_self,Real.toNNReal_zero,
        Jet3.heatLog_zero_time] using ih'

lemma leftWeightedStepTrial_ae {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    (leftWeightedStepTrial w q hw hw1 : Time→ℝ)=ᵐ[timeLaw] weightedStepTrial w q hw hw1 := by
  have he : ∀ᵐ t ∂timeLaw, ∀ i, t≠q i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_iff.mpr
    simp
  filter_upwards [he] with t ht
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i≤t
  · rw [ite_eq_left hi,ite_eq_left (lt_of_le_of_ne hi (Ne.symm (ht i)))]
  · rw [ite_eq_right hi,ite_eq_right (not_lt_of_ge (le_of_not_ge hi))]

lemma leftWeightedStepTrial_interval (n : ℕ) (w : Fin (n+1)→ℝ) (q : Fin (n+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (i : Fin n) {r : Time} (hr : r∈Ioc (q i.castSucc) (q i.succ)) :
    leftWeightedStepTrial w q hw hw1 r=(weightedControlCoefficient n w hw i:ℝ) := by
  change (∑ j, if q j < r then w j else 0) = ∑ j, if j ≤ i.castSucc then w j else 0
  apply Finset.sum_congr rfl
  intro j _
  have he : q j < r ↔ j ≤ i.castSucc := by
    constructor
    · intro hj
      by_contra hn
      have hij : i.succ ≤ j := by
        simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hn ⊢
        omega
      exact not_lt_of_ge ((hq hij).trans' hr.2) hj
    · intro hj
      exact (hq hj).trans_lt hr.1
  simp only [he]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianAffineCoordinate
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

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma stdGaussian_coordinate_law (i : I) :
    (stdGaussian (EuclideanSpace ℝ I)).map (fun x => x i)=gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ => gaussianReal 0 1) i).map_eq

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReferenceValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileTerminal_lipschitz (g : Jet3) (s : ℝ≥0) :
    LipschitzWith (‖(g.heatLog s 1).d1‖₊*
      ‖innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))‖₊)
      (labelProfileTerminal g s) := by
  have he : labelProfileTerminal g s =
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog s 1).f
        ((innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))) v) := by
    funext v
    rw [Jet3.heatLog_f]
    rfl
  rw [he]
  have heatLipschitz : LipschitzWith ‖(g.heatLog s 1).d1‖₊ (g.heatLog s 1).f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun point => ((g.heatLog s 1).has1 point).differentiableAt)
    intro point
    rw [(g.heatLog s 1).deriv_eq]
    exact_mod_cast (g.heatLog s 1).d1.norm_coe_le_norm point
  exact heatLipschitz.comp
    (innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))).lipschitz

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_LabelProfileControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma oneDim_inner (v : EuclideanSpace ℝ (Fin 1)) :
    inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v=v 0 := by
  simp [PiLp.inner_apply]

lemma oneDim_gaussian_average (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (a : ℝ) :
    (∫ v : EuclideanSpace ℝ (Fin 1), f (a+Real.sqrt s*v 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))=gaussianAverage s f a := by
  rw [gaussianAverage_scaling]
  have h : (∫ z, f (a+Real.sqrt s*z) ∂((stdGaussian (EuclideanSpace ℝ (Fin 1))).map
      (fun v => v 0)))=∫ v : EuclideanSpace ℝ (Fin 1), f (a+Real.sqrt s*v 0)
        ∂stdGaussian (EuclideanSpace ℝ (Fin 1)) :=
    integral_map (show Measurable (fun v : EuclideanSpace ℝ (Fin 1) => v 0) from by fun_prop).aemeasurable
      (show Measurable (fun z : ℝ => f (a+Real.sqrt s*z)) from by fun_prop).aestronglyMeasurable
  rw [stdGaussian_coordinate_law] at h
  exact h.symm

lemma oneDim_gaussian_entropic (s b : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ (Fin 1))) b
      (diagonalMark (fun _ => Real.sqrt s)) (fun v => f (v 0)) x=heatLog s b f (x 0) := by
  have hX : ∀ a : ℝ, Integrable
      (fun v : EuclideanSpace ℝ (Fin 1) => Real.exp (a*f (x 0+Real.sqrt s*v 0)))
      (stdGaussian (EuclideanSpace ℝ (Fin 1))) := fun a =>
    boundedContinuousFunction_integrable_comp (expBCF a f) (by fun_prop)
  change entropicMean (stdGaussian (EuclideanSpace ℝ (Fin 1))) b
    (fun v => f (x 0+Real.sqrt s*v 0))=heatLog s b f (x 0)
  by_cases hb : b=0
  · subst b
    rw [NNReal.coe_zero,entropicMean_zero _ hX,heatLog,ite_eq_left rfl,oneDim_gaussian_average]
  · rw [entropicMean_eq_div _ hX (by exact_mod_cast hb),heatLog,ite_eq_right hb]
    unfold cgf mgf
    change Real.log (∫ v : EuclideanSpace ℝ (Fin 1), expBCF b f (x 0+Real.sqrt s*v 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))/(b:ℝ)=_
    rw [oneDim_gaussian_average]
    ring

lemma linearCascadeWord_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : ℕ→E→L[ℝ] E) (k : ℕ) (z : Fin k→ℝ) (h : ∀ j<k,A j=B j) :
    linearCascadeWord A k z=linearCascadeWord B k z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [linearCascadeWord]
    rw [h k (Nat.lt_succ_self k),ih (fun i => z i.succ) (fun j hj => h j (Nat.lt_succ_of_lt hj))]

lemma profileGaussianStep_first {k : ℕ} (q : Fin (k+2)→Time) :
    profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) k=
      fun _ => Real.sqrt (timeSpan (q 0) (q 1)) := by
  funext i
  simp only [profileGaussianStep,dite_eq_left (Nat.lt_succ_self k)]
  have h0 : (⟨k+1-k-1,by omega⟩ : Fin (k+2))=0 := by ext; simp
  have h1 : (⟨k+1-k,by omega⟩ : Fin (k+2))=1 := by ext; simp
  rw [h0,h1]
  simp only [timeSpan,Real.coe_toNNReal']
  by_cases h : 0≤(q 1:ℝ)-q 0
  · rw [max_eq_left h]
  · have hn : (q 1:ℝ)-q 0≤0 := by linarith
    rw [max_eq_right hn,Real.sqrt_eq_zero_of_nonpos hn,Real.sqrt_zero]

lemma profileGaussianStep_tail {k : ℕ} (q : Fin (k+2)→Time) {j : ℕ} (hj : j<k) :
    profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j=
      profileGaussianStep (fun l (_ : Fin 1) => (q l.succ:ℝ)) j := by
  funext i
  simp only [profileGaussianStep,dite_eq_left hj,dite_eq_left (Nat.lt_succ_of_lt hj)]
  have ha : (⟨k+1-j,by omega⟩ : Fin (k+2))=(⟨k-j,by omega⟩ : Fin (k+1)).succ := by
    ext; simp only [Fin.val_succ]; omega
  have hb : (⟨k+1-j-1,by omega⟩ : Fin (k+2))=(⟨k-j-1,by omega⟩ : Fin (k+1)).succ := by
    ext; simp only [Fin.val_succ]; omega
  rw [ha,hb]

lemma oneDim_profile_backward (g : Jet3) (k : ℕ) (q : Fin (k+1)→Time)
    (z : Fin k→ℝ≥0) (x : EuclideanSpace ℝ (Fin 1)) :
    gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
      (linearCascadeWord (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j))
        k (fun i => z i)) (fun v => g.f (v 0)) x=(finiteStepControlJet g k q z).f (x 0) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [linearCascadeWord,gaussianLinearBackward,finiteStepControlJet]
    rw [profileGaussianStep_first]
    have hw := linearCascadeWord_congr
      (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j))
      (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l.succ:ℝ)) j))
      k (fun i => (z i.succ:ℝ)) (fun j hj => congrArg diagonalMark (profileGaussianStep_tail q hj))
    rw [hw]
    have hf := funext (ih (fun i => q i.succ) (fun i => z i.succ))
    rw [hf,oneDim_gaussian_entropic,Jet3.heatLog_f]
    change _=heatLog _ _ _ _
    rfl

lemma HeatChain.prepend {m : Trial} {g h j : Jet3} {a b c : Time}
    (H : HeatChain m g b c h) (J : HeatChain m h a b j) : HeatChain m g a c j := by
  induction J with
  | nil => exact H
  | cons d hat htb hm tail ih =>
    exact HeatChain.cons d hat (htb.trans H.left_le_right) hm (ih H)

lemma weightedStepTrial_controlValue_core (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w q hw hw1)=
      ((finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
        (weightedControlCoefficient k w hw)).heatLog (timeSpan 0 (q 0)) 0).f 0 := by
  let m := leftWeightedStepTrial w q hw hw1
  have ht : HeatChain m g (q (Fin.last k)) 1 (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) := by
    rcases lt_or_eq_of_le (show q (Fin.last k)≤1 from le_top) with hl|he
    · apply HeatChain.cons 1 hl le_rfl _ (HeatChain.nil 1)
      intro r hr
      change (∑ i, if q i < r then w i else 0)=(1:ℝ)
      have hqr i : q i < r := (hq (Fin.le_last i)).trans_lt hr.1
      simp only [hqr,ite_true,hw1]
    · rw [he]
      simp only [timeSpan,sub_self,Real.toNNReal_zero,Jet3.heatLog_zero_time]
      exact HeatChain.nil 1
  have hm := finiteStepControlJet_chain (g.heatLog (timeSpan (q (Fin.last k)) 1) 1)
    m k q (weightedControlCoefficient k w hw) hq
    (fun i r hr => leftWeightedStepTrial_interval k w q hw hw1 hq i hr)
  have hm' := ht.prepend hm
  have H : HeatChain m g 0 1 ((finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1)
      k q (weightedControlCoefficient k w hw)).heatLog (timeSpan 0 (q 0)) 0) := by
    rcases lt_or_eq_of_le (show (0:Time)≤q 0 from bot_le) with hl|he
    · apply HeatChain.cons 0 hl (show q 0≤1 from le_top) _ hm'
      intro r hr
      change (∑ i, if q i < r then w i else 0)=(0:ℝ)
      have hqr i : ¬ q i < r := not_lt_of_ge (hr.2.trans (hq (Fin.zero_le i)))
      simp only [hqr,ite_false,Finset.sum_const_zero]
    · rw [←he] at hm' ⊢
      simpa only [timeSpan,sub_self,Real.toNNReal_zero,Jet3.heatLog_zero_time] using hm'
  have he := leftWeightedStepTrial_ae w q hw hw1
  have hv := controlValue_trial_abs_sub_le P g.f (weightedStepTrial w q hw hw1) m ‖g.d1‖₊ g.lipschitz
  have hz : (∫ t, |weightedStepTrial w q hw hw1 t-m t| ∂timeLaw)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with t ht
    simp only [m,ht,sub_self,abs_zero,Pi.zero_apply]
  rw [hz,mul_zero] at hv
  rw [sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))]
  exact H.controlValue_eq P hB

theorem labelProfileValue_control (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    labelProfileValue k (stepCumulative w) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g=
      controlValue P g.f (weightedStepTrial w q hw hw1) := by
  rw [weightedStepTrial_controlValue_core k w q hw hw1 hq g P hB]
  have hend : (⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0)=
      timeSpan (q (Fin.last k)) 1 := by
    apply Subtype.ext
    change 1-(q (Fin.last k):ℝ)=(timeSpan (q (Fin.last k)) 1:ℝ)
    exact (timeSpan_coe (show q (Fin.last k)≤1 from le_top)).symm
  have hstart : (timeSpan 0 (q 0):ℝ)=(q 0:ℝ) := by
    rw [timeSpan_coe (show (0:Time)≤q 0 from bot_le)]; simp
  have hterm : labelProfileTerminal g (timeSpan (q (Fin.last k)) 1)=
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog (timeSpan (q (Fin.last k)) 1) 1).f (v 0) := by
    funext v
    rw [labelProfileTerminal,oneDim_inner,Jet3.heatLog_f]
    rfl
  have hc : stepCumulative w=fun i => (weightedControlCoefficient k w hw i:ℝ) := rfl
  unfold labelProfileValue
  rw [hend,hterm,hc]
  simp_rw [oneDim_profile_backward]
  simp only [diagonalMark_apply,profileGaussianRoot]
  rw [Jet3.heatLog_f]
  change (∫ x : EuclideanSpace ℝ (Fin 1),
    (finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
      (weightedControlCoefficient k w hw)).f (Real.sqrt (q 0:ℝ)*x 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))=heatLog (timeSpan 0 (q 0)) 0 _ 0
  rw [heatLog,ite_eq_left rfl]
  simpa only [hstart,zero_add] using oneDim_gaussian_average (timeSpan 0 (q 0))
    (finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
      (weightedControlCoefficient k w hw)).f 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CavityRPCControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_scalar_vector_recursion (τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (k : ℕ) (z : Fin k→ℝ) (x : ℕ→Spin 1) :
    finiteCascadeLogRecursion (gaussianMarkLaw : ProbabilityMeasure (Spin 1))
      (gaussianLinearMarkStep (fun j=>diagonalMark (fun _ : Fin 1=>τ j))) k z
      (fun x=>F (x 0 0)) x=
    finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
      (fun x=>F (x 0)) (fun j=>x j 0) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [finiteCascadeLogRecursion,fractionalLogMoment,ih]
    congr 2
    let G := fun b : ℝ=>Real.exp (z 0*finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k (fun i=>z i.succ) (fun x=>F (x 0))
        (gaussianShiftStep τ ((fun j=>x j 0),b)))
    have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
      (gaussianShiftStep_measurable τ) k (fun i=>z i.succ)
      (F.measurable.comp (measurable_pi_apply 0))
    have hG : Measurable G := Real.measurable_exp.comp (measurable_const.mul
      (hm.comp ((gaussianShiftStep_measurable τ).comp (measurable_const.prodMk measurable_id))))
    have he := integral_map (μ:=stdGaussian (Spin 1)) (show Measurable (fun v : Spin 1=>v 0) from by fun_prop).aemeasurable
      hG.aestronglyMeasurable
    rw [stdGaussian_coordinate_law] at he
    exact he.symm

lemma cavityScalarRootValue_eq_label (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (g : Jet3) :
    cavityScalarRootValue k (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>q l) j 0)
      z (Real.sqrt (q 0)) (g.heatLog ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ 1).f=
      labelProfileValue k z q hq1 g := by
  let s : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩
  let τ := fun j=>profileGaussianStep (fun l (_ : Fin 1)=>q l) j 0
  let A := fun j=>diagonalMark (profileGaussianStep (fun l (_ : Fin 1)=>q l) j)
  have hA : (fun j=>diagonalMark (fun _ : Fin 1=>τ j))=A := by
    rfl
  have hF : (fun v : Spin 1=>(g.heatLog s 1).f (v 0))=labelProfileTerminal g s := by
    funext v
    rw [labelProfileTerminal,oneDim_inner,Jet3.heatLog_f]
    rfl
  let : IsGaussian (gaussianMarkLaw (E:=Spin 1) : Measure (Spin 1)) :=
    (inferInstance : IsGaussian (stdGaussian (Spin 1)))
  have hr := (gaussianLinearRecursion_realization (gaussianMarkLaw (E:=Spin 1)) A
    (labelProfileTerminal_lipschitz g s) k z hz0).1
  have hs (v : Spin 1) :
      finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun x=>(g.heatLog s 1).f (x 0)) (fun _=>Real.sqrt (q 0)*v 0)=
      gaussianLinearBackward (stdGaussian (Spin 1)) (linearCascadeWord A k z)
        (labelProfileTerminal g s) (diagonalMark (profileGaussianRoot (fun l (_ : Fin 1)=>q l)) v) := by
    have H := cavity_scalar_vector_recursion τ (g.heatLog s 1).f k z
      (fun _=>diagonalMark (profileGaussianRoot (fun l (_ : Fin 1)=>q l)) v)
    rw [hA] at H
    have ht : (fun x : ℕ→Spin 1=>(g.heatLog s 1).f (x 0 0))=
        fun x=>labelProfileTerminal g s (x 0) := funext (fun x=>congrFun hF (x 0))
    rw [ht,hr] at H
    exact H.symm
  unfold cavityScalarRootValue labelProfileValue
  change (∫ b,finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
    (fun x=>(g.heatLog s 1).f (x 0)) (fun _=>Real.sqrt (q 0)*b)
      ∂(standardGaussianMark : Measure ℝ))=_
  have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
    (gaussianShiftStep_measurable τ) k z ((g.heatLog s 1).f.measurable.comp (measurable_pi_apply 0))
  have hroot : Measurable (fun b : ℝ=>finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k z (fun x=>(g.heatLog s 1).f (x 0))
        (fun _=>Real.sqrt (q 0)*b)) :=
    hm.comp (Measurable.of_eval (fun _=>measurable_const.mul measurable_id))
  have he := integral_map (μ:=stdGaussian (Spin 1)) (show Measurable (fun v : Spin 1=>v 0) from by fun_prop).aemeasurable
    hroot.aestronglyMeasurable
  rw [stdGaussian_coordinate_law] at he
  exact he.trans (integral_congr_ae (ae_of_all _ hs))

theorem cavityScalarRootValue_control (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i,0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q)
    (hz0 : ∀ i,0 < stepCumulative w i) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    cavityScalarRootValue k (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0)
      (stepCumulative w) (Real.sqrt (q 0 : ℝ))
      (g.heatLog ⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ 1).f=
      controlValue P g.f (weightedStepTrial w q hw hw1) := by
  rw [cavityScalarRootValue_eq_label k (stepCumulative w) hz0]
  exact labelProfileValue_control k w q hw hw1 hq g P hB

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

lemma fieldAmplitudes_last (k : ℕ) (h : Fin (k+1) → ℝ) :
    fieldAmplitudes k h (Fin.last k)=Real.sqrt (2*h 0) := by
  simp [fieldAmplitudes]

lemma fieldAmplitudes_increment (k : ℕ) (h : Fin (k+1) → ℝ) :
    finiteAmplitudeIncrement k (fieldAmplitudes k h)=stepFieldIncrement k h := by
  funext j
  by_cases hj : j < k
  · simp [finiteAmplitudeIncrement,fieldAmplitudes,hj]
  · simp [finiteAmplitudeIncrement,stepFieldIncrement,hj]

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

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFiniteEvaluation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem cavity_finiteRPC_value (n d k : ℕ) (w h : Fin (k+1)→ℝ)
    (q : Fin (k+1)→Time) (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1)
    (hh0 : 0≤h 0) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (c a : ℝ) :
    (n+1:ℕ)*(c+a-2*h (Fin.last k))/2+
    (∫ b, (∫ η,Real.log (decoratedTerminalTotal
      (cavityRPCStep n d (stepFieldIncrement k h)
        (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0))
      (cavityRPCTerminal n d
        (g.heatLog ⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ 1).f) k
      (cavityRPCRootState n d (Real.sqrt (2*h 0)) (Real.sqrt (q 0:ℝ)) b,η)/
      decoratedTerminalTotal
        (cavityRPCStep n d (stepFieldIncrement k h)
          (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0))
        (fun _=>0) k
      (cavityRPCRootState n d (Real.sqrt (2*h 0)) (Real.sqrt (q 0:ℝ)) b,η))
      ∂decoratedCascadeLaw (cavityRPCMarkLaw n d) k (stepCumulative w))
      ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)))=
    (n+1:ℕ)*((c+a)/2+finiteSphericalFieldValue n k w h)+
      d*controlValue P g.f (weightedStepTrial w q (fun i=>(hw i).le) hw1) := by
  rw [cavity_finiteRPC_roots n d k _ _ _ _ (stepCumulative_strictMono w hw)
    (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)]
  rw [cavityScalarRootValue_control k w q (fun i=>(hw i).le) hw1 hq
    (stepCumulative_pos w hw) g P hB]
  have he:=finiteAmplitudeSphereValue_fieldAmplitudes n k w h hh0
  unfold finiteAmplitudeSphereValue at he
  rw [fieldAmplitudes_increment,fieldAmplitudes_last] at he
  rw [he]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGaussianTransport
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal

lemma cavityRPC_fractional (n d k : ℕ) (σ τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (z : Fin k→ℝ) (hz0 : ∀ i,0<z i) :
    finiteCascadeFractionalIntegrable (cavityRPCMarkLaw n d) (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k z := by
  have hF : Measurable (fun a : ℕ→ℝ=>F (a 0)) := F.measurable.comp (measurable_pi_apply 0)
  have hFI := finiteCascadeFractionalIntegrable_of_bounded standardGaussianMark
    (gaussianShiftStep τ) (gaussianShiftStep_measurable τ) k z hz0 hF
    (fun a=>F.norm_coe_le_norm (a 0))
  have hs := finiteCascade_sum_pi (fun _ : Fin d=>standardGaussianMark)
    (fun _=>gaussianShiftStep τ) k z (fun _ a=>F (a 0)) (fun _=>hFI)
  have hv := coordinateRecursion_eq_backward (n+1) σ
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) k z hz0
  exact finiteCascadeFractionalIntegrable_add_product
    (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
    (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep d τ) k z hz0 hv.2 hs.2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFullEvaluation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

theorem cavityLabel_full_value_oai (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0 ≤ cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i ≤ cavityPairDiagonal n d D i)
    (q : Fin (k+1)→Time) (hpR : ∀ l,(p l).1.val=(q l:ℝ)) (hDR : D.1.val=1)
    (w : Fin (k+1)→ℝ) (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (hq : Monotone q)
    (g : Jet3) (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    let Q:=cavityPairProfile n d p
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-Q (Fin.last k) i)
    (∫ t,Real.log (cavityLabelFullPartition n d k g.f σ Q t)
      ∂(indexedCascadeBaseLaw k (stepCumulative w) : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
      (n+1:ℕ)*(D.2.val/2+finiteSphericalFieldValue n k w (fun l=>(p l).2.val/2))+
        d*controlValue P g.f (weightedStepTrial w q (fun l=>(hw l).le) hw1) := by
  have hpB : (p (Fin.last k)).2.val≤D.2.val := hpD (Sum.inl 0)
  let a : ℝ≥0:=⟨D.2.val-(p (Fin.last k)).2.val,sub_nonneg.mpr hpB⟩
  let s : ℝ≥0:=⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩
  have hs : (s:ℝ)=D.1.val-(p (Fin.last k)).1.val := by dsimp [s]; rw [hDR,hpR]; rfl
  have hr:=cavityLabel_full_evaluation n d p D hp0 hpm hpD g.f (stepCumulative w)
    (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
    a s rfl hs
  have hh0 : 0≤(p 0).2.val/2:=div_nonneg (hp0 (Sum.inl 0)) (by norm_num)
  have hv:=cavity_finiteRPC_value n d k w (fun l=>(p l).2.val/2) q hw hw1 hh0 hq g P hB 0 D.2.val
  have hb l : 2*((p l).2.val/2)=(p l).2.val := by ring
  have hqf : (fun l (_ : Fin 1)=>(p l).1.val)=(fun l (_ : Fin 1)=>(q l:ℝ)) := by
    funext l i; exact hpR l
  have hval : (n+1:ℕ)*a/2+
      (∫ b,finiteCascadeLogRecursion (cavityRPCMarkLaw n d)
        (cavityRPCStep n d (stepFieldIncrement k (fun l=>(p l).2.val/2))
          (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(p l).1.val) j 0)) k (stepCumulative w)
        (cavityRPCTerminal n d (heatLogBCF s 1 g.f))
        (cavityRPCRootState n d (Real.sqrt (p 0).2.val) (Real.sqrt (p 0).1.val) b)
        ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)))=
      (n+1:ℕ)*(D.2.val/2+finiteSphericalFieldValue n k w (fun l=>(p l).2.val/2))+
        d*controlValue P g.f (weightedStepTrial w q (fun l=>(hw l).le) hw1) := by
    simp only [zero_add,hb] at hv
    simp_rw [finiteCascade_terminal_log_recursion_of_fractional (cavityRPCMarkLaw n d)
      (cavityRPCStep n d (stepFieldIncrement k (fun l=>(p l).2.val/2))
        (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0))
      (cavityRPCStep_measurable n d _ _) k (stepCumulative w)
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
      (cavityRPCTerminal_measurable n d _) (cavityRPC_fractional n d k _ _ _ _ (stepCumulative_pos w hw))] at hv
    erw [Jet3.heatLog_f] at hv
    have ha : (a:ℝ)=D.2.val-(p (Fin.last k)).2.val := rfl
    rw [ha,hqf,hpR]
    exact hv
  exact hr.trans hval

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value_oai := @OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value_oai
