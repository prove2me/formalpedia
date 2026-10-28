-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:28:12.924998+00:00
-- url     : https://prove2.me/submissions/16684e2c-d938-4674-b795-a1d57877f06f

import Mathlib
import Definitions.Def_OAIQ61Pf002

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

lemma stablePoisson_mark_shift {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [SFinite ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (Measure.map (logMarkShift F)) =
      poissonRandomMeasureLaw ((stableLogIntensity b).prod
        (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b * F s))))) := by
  rw [poissonRandomMeasureLaw_map _ (logMarkShift_measurable hF)]
  congr 1
  exact stableLogIntensity_mark_shift ν hb hF

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

lemma aemeasurable_measure_lintegral_of_finite {S : Type*} [MeasurableSpace S]
    {P : Measure (Measure S)} (hP : ∀ᵐ η ∂P, η univ < ⊤)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    AEMeasurable (fun η => ∫⁻ x, H (η,x) ∂η) P := by
  have hm : Measurable (fun η => ⨆ n : ℕ, ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel n η) :=
    Measurable.iSup fun n => hH.lintegral_kernel_prod_right' (κ := finiteMeasureCutKernel n)
  apply hm.aemeasurable.congr
  filter_upwards [hP] with η hη
  apply le_antisymm
  · apply iSup_le
    intro n
    change (∫⁻ x, H (η,x) ∂(if η univ ≤ n then η else 0)) ≤ _
    split_ifs <;> simp
  · obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hη.ne
    calc
      (∫⁻ x, H (η,x) ∂η) = ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel n η := by
        change _ = ∫⁻ x, H (η,x) ∂(if η univ ≤ n then η else 0)
        rw [ite_eq_left hn.le]
      _ ≤ _ := le_iSup (fun m : ℕ => ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel m η) n

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

lemma finitePointMeasure_insertNth {S : Type*} [MeasurableSpace S]
    (n : ℕ) (i : Fin (n+1)) (x : S) (y : Fin n → S) :
    finitePointMeasure (n+1) (i.insertNth x y) = Measure.dirac x + finitePointMeasure n y := by
  classical
  rw [finitePointMeasure,Fin.sum_univ_succAbove _ i]
  simp [finitePointMeasure]

lemma finite_point_mecke {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y : Fin (n+1) → S, ∑ i, H (finitePointMeasure (n+1) y,y i)
      ∂Measure.pi (fun _ => ν)) = (n+1 : ℝ≥0∞) *
      ∫⁻ x, ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x)
        ∂Measure.pi (fun _ => ν) ∂ν := by
  classical
  rw [lintegral_finsetSum (f := fun (i : Fin (n+1)) (y : Fin (n+1) → S) => H (finitePointMeasure (n+1) y,y i)) _ (fun i _ => hH.comp
    ((finitePointMeasure_measurable _).prodMk (measurable_pi_apply i)))]
  have he (i : Fin (n+1)) :
      (∫⁻ y : Fin (n+1) → S, H (finitePointMeasure (n+1) y,y i)
        ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x)
        ∂Measure.pi (fun _ => ν) ∂ν := by
    have hm : Measurable (fun y : Fin (n+1) → S => H (finitePointMeasure (n+1) y,y i)) :=
      hH.comp ((finitePointMeasure_measurable _).prodMk (measurable_pi_apply i))
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) i).symm).lintegral_comp hm]
    change (∫⁻ p : S × (Fin n → S), H (finitePointMeasure (n+1) (i.insertNth p.1 p.2),
      ((i.insertNth p.1 p.2 : Fin (n+1) → S) i)) ∂ν.prod (Measure.pi fun _ => ν)) = _
    simp only [finitePointMeasure_insertNth,Fin.insertNth_apply_same]
    exact lintegral_prod _ (hH.comp
      (((by fun_prop : Measurable (fun p : S × (Fin n → S) =>
        Measure.dirac p.1 + finitePointMeasure n p.2))).prodMk measurable_fst)).aemeasurable
  simp_rw [he]
  simp

lemma poissonMeasure_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n+1} * (n+1 : ℝ≥0∞) = (r : ℝ≥0∞) * poissonMeasure r {n} := by
  rw [poissonMeasure_singleton,poissonMeasure_singleton]
  have he : Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-(r : ℝ)) *
    (r : ℝ)^(n+1) / (n+1).factorial), ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
    ENNReal.ofReal_natCast,ENNReal.ofReal_one] using hh

lemma finitePoissonLaw_mecke {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂finitePoissonLaw r ν) =
      (r : ℝ≥0∞) * ∫⁻ x, ∫⁻ η, H (Measure.dirac x + η,x) ∂finitePoissonLaw r ν ∂ν := by
  rw [finitePoissonLaw,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure]
  have hmap (n : ℕ) :
      (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂(Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) =
      ∫⁻ y : Fin n → S, ∫⁻ x, H (finitePointMeasure n y,x) ∂finitePointMeasure n y
        ∂Measure.pi (fun _ => ν) := by
    apply lintegral_map'
    · exact aemeasurable_measure_lintegral_of_finite
        ((ae_map_iff (finitePointMeasure_measurable n).aemeasurable
          (measurableSet_lt (Measure.measurable_coe .univ) measurable_const)).mpr
            (ae_of_all _ fun y => by simp [finitePointMeasure,Measure.finsetSum_apply])) hH
    · exact (finitePointMeasure_measurable n).aemeasurable
  simp_rw [hmap]
  have hinner (n : ℕ) (y : Fin n → S) :
      (∫⁻ x, H (finitePointMeasure n y,x) ∂finitePointMeasure n y) =
        ∑ i, H (finitePointMeasure n y,y i) :=
    finitePointMeasure_lintegral (hH.comp (measurable_const.prodMk measurable_id)) _ _
  simp only [hinner,smul_eq_mul]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero,lintegral_zero,mul_zero,zero_add]
  simp_rw [finite_point_mecke ν _ hH,← mul_assoc,poissonMeasure_succ_mul,mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmn (n : ℕ) : Measurable (fun x : S => ∫⁻ y : Fin n → S,
      H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν)) := by
    have hm : Measurable (fun p : S × (Fin n → S) => Measure.dirac p.1 + finitePointMeasure n p.2) := by
      fun_prop
    exact (hH.comp (hm.prodMk measurable_fst)).lintegral_prod_right'
  symm
  calc
    _ = ∫⁻ x, ∑' n : ℕ, poissonMeasure r {n} * ∫⁻ y : Fin n → S,
        H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_congr
      intro x
      rw [lintegral_sum_measure]
      simp only [lintegral_smul_measure,smul_eq_mul]
      apply tsum_congr
      intro n
      congr 1
      exact lintegral_map
        (hH.comp ((measurable_const.add measurable_id).prodMk measurable_const))
        (finitePointMeasure_measurable n)
    _ = _ := by
      rw [lintegral_tsum (f := fun (n : ℕ) (x : S) => poissonMeasure r {n} *
        ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν))
        (fun n => (measurable_const.mul (hmn n)).aemeasurable)]
      apply tsum_congr
      intro n
      exact lintegral_const_mul' _ _ (measure_ne_top _ _)

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

lemma poissonRandomMeasureLaw_superposition {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ ζ : Measure S) [SFinite κ] [SFinite ζ] :
    ((poissonRandomMeasureLaw κ).prod (poissonRandomMeasureLaw ζ)).map
      (fun p => p.1+p.2) = poissonRandomMeasureLaw (κ+ζ) := by
  have hm : Measurable (fun p : Measure S × Measure S => p.1+p.2) := by fun_prop
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [integral_map hm.aemeasurable (poissonLaplace_measurable hf).aestronglyMeasurable]
  have hsum (p : Measure S × Measure S) : poissonLaplace f (p.1+p.2) =
      poissonLaplace f p.1 * poissonLaplace f p.2 := by
    simp only [poissonLaplace,lintegral_add_measure,expNegENNReal_add]
  simp_rw [hsum]
  have hi (ν : Measure S) [SFinite ν] : Integrable (poissonLaplace f) (poissonRandomMeasureLaw ν) :=
    Integrable.of_bound (poissonLaplace_measurable hf).aestronglyMeasurable 1
      (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds f η).1]
        using (poissonLaplace_bounds f η).2)
  rw [integral_prod _ ((hi κ).mul_prod (hi ζ))]
  simp_rw [integral_const_mul]
  rw [integral_mul_const,poissonRandomMeasureLaw_laplace κ hf hf0,
    poissonRandomMeasureLaw_laplace ζ hf hf0,poissonRandomMeasureLaw_laplace (κ+ζ) hf hf0,
    lintegral_add_measure,expNegENNReal_add]

lemma poissonRandomMeasureLaw_of_finite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ] :
    poissonRandomMeasureLaw κ = finitePoissonLaw (κ univ).toNNReal (finiteIntensityMarks κ) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [poissonRandomMeasureLaw_laplace κ hf hf0,finitePoissonLaw_laplace_nonneg _ _ hf hf0]
  have hi : Integrable (fun x => 1 - Real.exp (-f x)) (finiteIntensityMarks κ) := by
    apply Integrable.of_bound (measurable_const.sub hf.neg.exp).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      change |1-Real.exp (-f x)| ≤ 1
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x))))]
      linarith [Real.exp_pos (-f x)]
  congr 1
  calc
    _ = ((κ univ).toNNReal : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (1-Real.exp (-f x))
        ∂finiteIntensityMarks κ := by
      conv_lhs => rw [← finiteIntensityMarks_smul κ]
      rw [lintegral_smul_measure]
      rfl
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun x => sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x)))),
        ENNReal.ofReal_mul (NNReal.coe_nonneg _),ENNReal.ofReal_coe_nnreal]

lemma aemeasurable_randomMeasure_lintegral_of_finite {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {P : Measure Ω} {A : Ω → Measure S}
    (hA : Measurable A) (hfinite : ∀ᵐ ω ∂P, A ω univ < ⊤)
    {H : Ω × S → ℝ≥0∞} (hH : Measurable H) :
    AEMeasurable (fun ω => ∫⁻ x, H (ω,x) ∂A ω) P := by
  have hm : Measurable (fun ω => ⨆ n : ℕ, ∫⁻ x, H (ω,x) ∂finiteMeasureCutKernel n (A ω)) := by
    apply Measurable.iSup
    intro n
    exact hH.lintegral_kernel_prod_right' (κ := (finiteMeasureCutKernel n).comap A hA)
  apply hm.aemeasurable.congr
  filter_upwards [hfinite] with ω hω
  apply le_antisymm
  · apply iSup_le
    intro n
    change (∫⁻ x, H (ω,x) ∂(if A ω univ ≤ n then A ω else 0)) ≤ _
    split_ifs <;> simp
  · obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hω.ne
    calc
      (∫⁻ x, H (ω,x) ∂A ω) = ∫⁻ x, H (ω,x) ∂finiteMeasureCutKernel n (A ω) := by
        change _ = ∫⁻ x, H (ω,x) ∂(if A ω univ ≤ n then A ω else 0)
        rw [ite_eq_left hn.le]
      _ ≤ _ := le_iSup (fun m : ℕ => ∫⁻ x, H (ω,x) ∂finiteMeasureCutKernel m (A ω)) n

lemma poissonRandomMeasureLaw_ae_restrict_finite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {E : Set S} (hE : MeasurableSet E) (hκ : κ E < ⊤) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, (η.restrict E) univ < ⊤ := by
  have he : (∫⁻ η, η E ∂poissonRandomMeasureLaw κ) = κ E := by
    simpa only [lintegral_indicator hE,lintegral_one,Measure.restrict_apply_univ]
      using poissonRandomMeasureLaw_campbell κ (measurable_const.indicator hE :
        Measurable (E.indicator (fun _ : S => (1 : ℝ≥0∞))))
  simpa only [Measure.restrict_apply_univ] using
    ae_lt_top (Measure.measurable_coe hE) (he ▸ hκ.ne)

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

lemma poissonRandomMeasureLaw_mecke_finite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ]
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂poissonRandomMeasureLaw κ) =
      ∫⁻ x, ∫⁻ η, H (Measure.dirac x + η,x) ∂poissonRandomMeasureLaw κ ∂κ := by
  rw [poissonRandomMeasureLaw_of_finite κ,finitePoissonLaw_mecke _ _ hH]
  calc
    _ = ∫⁻ x, ∫⁻ η, H (Measure.dirac x+η,x)
        ∂finitePoissonLaw (κ univ).toNNReal (finiteIntensityMarks κ)
        ∂((κ univ).toNNReal : ℝ≥0∞) • finiteIntensityMarks κ := by
      rw [lintegral_smul_measure]; rfl
    _ = _ := by rw [finiteIntensityMarks_smul κ]

lemma poissonRandomMeasureLaw_mecke_restrict {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {E : Set S} (hE : MeasurableSet E) (hκ : κ E < ⊤)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x in E, H (η,x) ∂η ∂poissonRandomMeasureLaw κ) =
      ∫⁻ x in E, ∫⁻ η, H (Measure.dirac x + η,x) ∂poissonRandomMeasureLaw κ ∂κ := by
  let ν := κ.restrict E
  let ζ := κ.restrict Eᶜ
  let P := poissonRandomMeasureLaw ν
  let Q := poissonRandomMeasureLaw ζ
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hκ⟩
  have hsum : ν+ζ = κ := Measure.restrict_add_restrict_compl hE
  have hadd : Measurable (fun p : Measure S × Measure S => p.1+p.2) := by fun_prop
  have hPQ : (P.prod Q).map (fun p => p.1+p.2) = poissonRandomMeasureLaw κ := by
    dsimp [P,Q]
    rw [poissonRandomMeasureLaw_superposition]
    simp only [hsum]
  have hm : AEMeasurable (fun η : Measure S => ∫⁻ x in E, H (η,x) ∂η)
      (poissonRandomMeasureLaw κ) :=
    aemeasurable_randomMeasure_lintegral_of_finite (measurable_measure_restrict hE)
      (poissonRandomMeasureLaw_ae_restrict_finite κ hE hκ) hH
  have hPnull : ∀ᵐ η ∂P, η Eᶜ = 0 := by
    apply poissonRandomMeasureLaw_ae_null ν hE.compl
    simp [ν,Measure.restrict_apply,hE.compl]
  have hQnull : ∀ᵐ η ∂Q, η E = 0 := by
    apply poissonRandomMeasureLaw_ae_null ζ hE
    simp [ζ,Measure.restrict_apply,hE]
  have hPQnull : ∀ᵐ p : Measure S × Measure S ∂P.prod Q,
      p.1 Eᶜ = 0 ∧ p.2 E = 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_eq_fun ((Measure.measurable_coe hE.compl).comp measurable_fst) measurable_const).inter
        (measurableSet_eq_fun ((Measure.measurable_coe hE).comp measurable_snd) measurable_const))).mpr
    filter_upwards [hPnull] with η hη
    filter_upwards [hQnull] with ξ hξ
    exact ⟨hη,hξ⟩
  have hrestrict (η ξ : Measure S) (hη : η Eᶜ = 0) (hξ : ξ E = 0) :
      (η+ξ).restrict E = η := by
    rw [Measure.restrict_add,Measure.restrict_eq_zero.mpr hξ,add_zero]
    have hh := Measure.restrict_add_restrict_compl (μ := η) hE
    rwa [Measure.restrict_eq_zero.mpr hη,add_zero] at hh
  have haefin : ∀ᵐ p : Measure S × Measure S ∂P.prod Q, p.1 univ < ⊤ := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp measurable_fst) measurable_const)).mpr
    filter_upwards [poissonRandomMeasureLaw_ae_restrict_finite ν MeasurableSet.univ
      (measure_lt_top ν univ)] with η hη
    exact ae_of_all _ fun _ => by simpa using hη
  have hmeas : AEMeasurable (fun p : Measure S × Measure S =>
      ∫⁻ x, H (p.1+p.2,x) ∂p.1) (P.prod Q) :=
    aemeasurable_randomMeasure_lintegral_of_finite measurable_fst haefin
      (hH.comp (by fun_prop : Measurable (fun p : (Measure S × Measure S) × S => (p.1.1+p.1.2,p.2))))
  calc
    _ = ∫⁻ p : Measure S × Measure S, ∫⁻ x in E, H (p.1+p.2,x) ∂(p.1+p.2) ∂P.prod Q := by
      rw [← hPQ] at hm ⊢
      exact lintegral_map' hm hadd.aemeasurable
    _ = ∫⁻ p : Measure S × Measure S, ∫⁻ x, H (p.1+p.2,x) ∂p.1 ∂P.prod Q := by
      apply lintegral_congr_ae
      filter_upwards [hPQnull] with p hp
      rw [hrestrict p.1 p.2 hp.1 hp.2]
    _ = ∫⁻ ξ, ∫⁻ η, ∫⁻ x, H (η+ξ,x) ∂η ∂P ∂Q := lintegral_prod_symm _ hmeas
    _ = ∫⁻ ξ, ∫⁻ x, ∫⁻ η, H (Measure.dirac x+η+ξ,x) ∂P ∂ν ∂Q := by
      apply lintegral_congr
      intro ξ
      exact poissonRandomMeasureLaw_mecke_finite ν (hH.comp
        (by fun_prop : Measurable (fun p : Measure S × S => (p.1+ξ,p.2))))
    _ = ∫⁻ x, ∫⁻ ξ, ∫⁻ η, H (Measure.dirac x+η+ξ,x) ∂P ∂Q ∂ν := by
      apply lintegral_lintegral_swap
      exact (hH.comp (by fun_prop : Measurable (fun p : (Measure S × S) × Measure S =>
        (Measure.dirac p.1.2+p.2+p.1.1,p.1.2)))).lintegral_prod_right'.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      rw [← lintegral_prod_symm (μ := P) (ν := Q)
        (fun p : Measure S × Measure S => H (Measure.dirac x+p.1+p.2,x)) (hH.comp (by fun_prop : Measurable
        (fun p : Measure S × Measure S => (Measure.dirac x+p.1+p.2,x)))).aemeasurable]
      rw [← hPQ,lintegral_map (f := fun η : Measure S => H (Measure.dirac x+η,x)) (hH.comp (by fun_prop : Measurable
        (fun η : Measure S => (Measure.dirac x+η,x)))) hadd]
      apply lintegral_congr
      intro p
      rw [add_assoc]

lemma poissonRandomMeasureLaw_mecke {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SigmaFinite κ] {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂poissonRandomMeasureLaw κ) =
      ∫⁻ x, ∫⁻ η, H (Measure.dirac x + η,x) ∂poissonRandomMeasureLaw κ ∂κ := by
  have hset (η : Measure S) : (∫⁻ x, H (η,x) ∂η) =
      ⨆ n : ℕ, ∫⁻ x in spanningSets κ n, H (η,x) ∂η := by
    rw [← setLIntegral_iUnion_of_directed _ (monotone_spanningSets κ).directed_le,
      iUnion_spanningSets,Measure.restrict_univ]
  simp_rw [hset]
  rw [lintegral_iSup']
  · simp_rw [poissonRandomMeasureLaw_mecke_restrict κ (measurableSet_spanningSets κ _)
      (measure_spanningSets_lt_top κ _) hH]
    rw [← setLIntegral_iUnion_of_directed _ (monotone_spanningSets κ).directed_le,
      iUnion_spanningSets,Measure.restrict_univ]
  · intro n
    exact aemeasurable_randomMeasure_lintegral_of_finite (measurable_measure_restrict (measurableSet_spanningSets κ n))
      (poissonRandomMeasureLaw_ae_restrict_finite κ (measurableSet_spanningSets κ n)
        (measure_spanningSets_lt_top κ n)) hH
  · exact ae_of_all _ fun η n m hnm => lintegral_mono_set (monotone_spanningSets κ hnm)

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
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereIsometryMap
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

lemma normalizedMeasure_probability {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (h0 : μ univ ≠ 0) (hf : μ univ ≠ ⊤) : IsProbabilityMeasure (normalizedMeasure μ) := by
  constructor
  change (μ univ)⁻¹ * μ univ = 1
  exact ENNReal.inv_mul_cancel h0 hf

lemma normalizedMeasure_smul {S : Type*} [MeasurableSpace S] (μ : Measure S)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcf : c ≠ ⊤) :
    normalizedMeasure (c • μ) = normalizedMeasure μ := by
  unfold normalizedMeasure
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.mul_inv (Or.inl hc0) (Or.inl hcf),smul_smul]
  congr 1
  calc
    c⁻¹ * (μ univ)⁻¹ * c = c⁻¹*c*(μ univ)⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hcf,one_mul]

lemma map_withDensity_comp {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) {f : S → T} (hf : Measurable f) {g : T → ℝ≥0∞} (hg : Measurable g) :
    (μ.map f).withDensity g = (μ.withDensity (g ∘ f)).map f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hh,
    lintegral_map (hg.mul hh) hf,lintegral_map hh hf]
  rw [lintegral_withDensity_eq_lintegral_mul _ (hg.comp hf) (show Measurable (fun x => h (f x)) from hh.comp hf)]
  rfl

open Matrix
open scoped RealInnerProductSpace MatrixOrder

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

lemma lintegral_comp_exp_all (g : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp x)*g (Real.exp x)) = ∫⁻ y : ℝ in Ioi 0, g y := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x (_ : x ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g
  simpa only [image_univ,Real.range_exp,Measure.restrict_univ,abs_of_pos (Real.exp_pos _)] using h.symm

lemma stableLogIntensity_laplace_moment {b r t : ℝ} (hb : 0 ≤ b) (hr : b < r) (ht : 0 < t) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)) ∂stableLogIntensity b) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)) := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  have he (x : ℝ) :
      ENNReal.ofReal (b*Real.exp (-b*x))*ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)) =
      ENNReal.ofReal b*(ENNReal.ofReal (Real.exp x)*
        ENNReal.ofReal ((Real.exp x)^(r-b-1)*Real.exp (-t*Real.exp x))) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hb (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_mul hb]
    congr 1
    rw [← Real.exp_mul]
    have hx : Real.exp (-b*x)*Real.exp (r*x) = Real.exp x*Real.exp (x*(r-b-1)) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    calc
      b*Real.exp (-b*x)*(Real.exp (r*x)*Real.exp (-t*Real.exp x)) =
          b*(Real.exp (-b*x)*Real.exp (r*x))*Real.exp (-t*Real.exp x) := by ring
      _ = _ := by rw [hx]; ring
  change (∫⁻ x : ℝ, ENNReal.ofReal (b*Real.exp (-b*x))*ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))) = _
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_exp_all (fun y : ℝ => ENNReal.ofReal (y^(r-b-1)*Real.exp (-t*y))),
    show (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (y^(r-b-1)*Real.exp (-t*y))) =
      ENNReal.ofReal (t^(-(r-b))*Real.Gamma (r-b)) from by
        simpa only [neg_mul,mul_comm t] using gamma_lintegral_positive_scale (sub_pos.mpr hr) ht,
    ← ENNReal.ofReal_mul hb]
  congr 1
  rw [neg_sub]
  ring

lemma one_sub_exp_neg_lintegral {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (1-Real.exp (-u)) =
      ∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (u*Real.exp (-t*u)) := by
  have hi : IntegrableOn (fun t : ℝ => u*Real.exp (-t*u)) (Ioc 0 1) :=
    (show Continuous (fun t : ℝ => u*Real.exp (-t*u)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => mul_nonneg hu.le (Real.exp_pos _).le)]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => -Real.exp (-s*u)) (u*Real.exp (-t*u)) t := by
    convert! (((hasDerivAt_id t).neg.mul_const u).exp).neg using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.neg_apply,id_eq,one_mul,neg_mul,mul_neg,neg_neg]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => u*Real.exp (-t*u)) by fun_prop).intervalIntegrable 0 1)]
  simp only [neg_mul,zero_mul,neg_zero,Real.exp_zero]
  ring_nf

lemma lintegral_rpow_unit {b : ℝ} (hb : 0 < b) :
    (∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (t^(b-1))) = ENNReal.ofReal b⁻¹ := by
  have hi : IntegrableOn (fun t : ℝ => t^(b-1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith : -1 < b-1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _),← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith : -1 < b-1))]
  simp [Real.zero_rpow hb.ne']

lemma stableLaplaceConstant_eq_gamma {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b = ENNReal.ofReal (Real.Gamma (1-b)) := by
  unfold stableLaplaceConstant
  simp_rw [one_sub_exp_neg_lintegral (Real.exp_pos _)]
  rw [lintegral_lintegral_swap (by fun_prop : Measurable (fun p : ℝ×ℝ =>
    ENNReal.ofReal (Real.exp p.1*Real.exp (-p.2*Real.exp p.1)))).aemeasurable]
  have he : (∫⁻ t : ℝ in Ioc 0 1, ∫⁻ x : ℝ,
      ENNReal.ofReal (Real.exp x*Real.exp (-t*Real.exp x)) ∂stableLogIntensity b) =
      ∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (b*t^(b-1)*Real.Gamma (1-b)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [one_mul] using stableLogIntensity_laplace_moment hb.le hb1 ht.1
  rw [he]
  have hG : 0 ≤ Real.Gamma (1-b) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hf (t : ℝ) : ENNReal.ofReal (b*t^(b-1)*Real.Gamma (1-b)) =
      ENNReal.ofReal (b*Real.Gamma (1-b))*ENNReal.ofReal (t^(b-1)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hb.le hG)]
    congr 1
    ring
  simp_rw [hf]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_rpow_unit hb,
    ← ENNReal.ofReal_mul (mul_nonneg hb.le hG)]
  congr 1
  field_simp

attribute [fun_prop] stablePoissonTotal_measurable

lemma stablePoissonTotal_add_dirac (x : ℝ) (η : Measure ℝ)
    (hη : (∫⁻ y, ENNReal.ofReal (Real.exp y) ∂η) ≠ ⊤) :
    stablePoissonTotal (Measure.dirac x+η) = Real.exp x+stablePoissonTotal η := by
  unfold stablePoissonTotal
  rw [lintegral_add_measure,lintegral_dirac,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hη,ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma stablePoissonTotal_laplace_lintegral {b t : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫⁻ η, ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have hi : Integrable (fun η => Real.exp (-t*stablePoissonTotal η))
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
        ENNReal.toReal_nonneg)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le),
    stablePoissonTotal_laplace hb hb1 ht,stableLaplaceConstant_eq_gamma hb hb1,
    ENNReal.toReal_ofReal (Real.Gamma_pos_of_pos (by linarith)).le]

lemma stablePoisson_palm_laplace {b r t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : b < r) (ht : 0 < t) :
    (∫⁻ η, ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal η))
      ∂η ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)*Real.exp (-Real.Gamma (1-b)*t^b)) := by
  rw [poissonRandomMeasureLaw_mecke (stableLogIntensity b) (by fun_prop : Measurable
    (fun p : Measure ℝ×ℝ => ENNReal.ofReal (Real.exp (r*p.2)*Real.exp (-t*stablePoissonTotal p.1))))]
  have he (x : ℝ) :
      (∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal (Measure.dirac x+η)))
        ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
        ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
    calc
      _ = ∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
          ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
          ∂poissonRandomMeasureLaw (stableLogIntensity b) := by
        apply lintegral_congr_ae
        filter_upwards [stablePoisson_total_finite hb hb1] with η hη
        rw [stablePoissonTotal_add_dirac x η hη,mul_add,Real.exp_add,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
        congr 1
        ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,stablePoissonTotal_laplace_lintegral hb hb1 ht]
  change (∫⁻ x, ∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal (Measure.dirac x+η)))
        ∂poissonRandomMeasureLaw (stableLogIntensity b) ∂stableLogIntensity b) = _
  simp_rw [he]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,stableLogIntensity_laplace_moment hb.le hr ht,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hb.le (Real.rpow_nonneg ht.le _))
      (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]

lemma gamma_lintegral_rpow_scale {q b c : ℝ} (hq : -1 < q) (hb : 0 < b) (hc : 0 < c) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^q*Real.exp (-c*t^b))) =
      ENNReal.ofReal (c^(-(q+1)/b)*(1/b)*Real.Gamma ((q+1)/b)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_rpow_mul_exp_neg_mul_rpow hq hb hc) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le),
    integral_rpow_mul_exp_neg_mul_rpow hb hq hc]

lemma stablePoisson_palm_laplace' {b r t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : b < r) (ht : 0 < t) :
    (∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)*Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have hh := stablePoisson_palm_laplace hb hb1 hr ht
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top] at hh
  exact hh

lemma stablePoisson_palm_mellin_mul {a b r : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (hr : b < r) :
    (∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (r-a)) =
      ENNReal.ofReal (Real.Gamma (r-b)*Real.Gamma (1-a/b)*
        (Real.Gamma (1-b))^(a/b-1)) := by
  let P := poissonRandomMeasureLaw (stableLogIntensity b)
  let c := Real.Gamma (1-b)
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hra : 0 < r-a := by linarith
  let K := fun (η : Measure ℝ) (t : ℝ) => stableJumpMomentE r η*
    ENNReal.ofReal (t^(r-a-1)*Real.exp (-t*stablePoissonTotal η))
  have hm : Measurable (Function.uncurry K) := by dsimp [K]; fun_prop
  have hgamma : ∀ᵐ η ∂P,
      stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))*ENNReal.ofReal (Real.Gamma (r-a)) =
        ∫⁻ t : ℝ in Ioi 0, K η t := by
    filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
    dsimp [K]
    rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_positive_scale hra hη,
      show -(r-a) = a-r by ring,ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _),mul_assoc]
  have hinner (t : ℝ) (ht : 0 < t) : (∫⁻ η, K η t ∂P) =
      ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-a-1)*Real.exp (-c*t^b)) := by
    have hfac (η : Measure ℝ) : K η t = ENNReal.ofReal (t^(r-a-1))*
        (stableJumpMomentE r η*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))) := by
      dsimp [K]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      ring
    simp_rw [hfac]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,stablePoisson_palm_laplace' hb hb1 hr ht,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]
    congr 1
    have hp : t^(r-a-1)*t^(b-r) = t^(b-a-1) := by rw [← Real.rpow_add ht]; congr 1; ring
    calc
      _ = b*Real.Gamma (r-b)*(t^(r-a-1)*t^(b-r))*Real.exp (-c*t^b) := by dsimp [c]; ring
      _ = _ := by rw [hp]; ring
  calc
    _ = ∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))*
        ENNReal.ofReal (Real.Gamma (r-a)) ∂P :=
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ η, (∫⁻ t : ℝ in Ioi 0, K η t) ∂P := lintegral_congr_ae hgamma
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ η, K η t ∂P := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-a-1)*Real.exp (-c*t^b)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hinner t ht
    _ = ENNReal.ofReal (b*Real.Gamma (r-b))*
        ENNReal.ofReal (c^(-((b-a-1)+1)/b)*(1/b)*Real.Gamma (((b-a-1)+1)/b)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,gamma_lintegral_rpow_scale (by linarith) hb hc]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]
      congr 1
      rw [show -((b-a-1)+1)/b = a/b-1 by field_simp; ring,
        show ((b-a-1)+1)/b = 1-a/b by field_simp; ring]
      dsimp [c]
      field_simp

lemma stablePoissonTotal_rpow_lintegral_mul {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) :
    (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (1-a)) =
      ENNReal.ofReal (Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)) := by
  have he := stablePoisson_palm_mellin_mul hb hb1 ha hb1
  have hrew : (fun η => stableJumpMomentE 1 η*ENNReal.ofReal (stablePoissonTotal η^(a-1))) =ᵐ[
      poissonRandomMeasureLaw (stableLogIntensity b)] (fun η => ENNReal.ofReal (stablePoissonTotal η^a)) := by
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hη hpos
    have hJ : stableJumpMomentE 1 η = ENNReal.ofReal (stablePoissonTotal η) := by
      simp only [stableJumpMomentE,one_mul,stablePoissonTotal]
      exact (ENNReal.ofReal_toReal hη).symm
    rw [hJ,← ENNReal.ofReal_mul hpos.le]
    congr 1
    calc
      _ = stablePoissonTotal η^((1:ℝ)+(a-1)) := by rw [Real.rpow_add hpos,Real.rpow_one]
      _ = _ := by congr 1; ring
  rw [lintegral_congr_ae hrew] at he
  rw [he]
  congr 1
  have hc : 0 < Real.Gamma (1-b) := Real.Gamma_pos_of_pos (by linarith)
  calc
    _ = Real.Gamma (1-a/b)*((Real.Gamma (1-b))^((1:ℝ)+(a/b-1))) := by
      rw [Real.rpow_add hc,Real.rpow_one]; ring
    _ = _ := by congr 2; ring

lemma stablePoissonTotal_rpow_integral {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) :
    (∫ η, stablePoissonTotal η^a ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)/Real.Gamma (1-a) := by
  have hga : 0 < Real.Gamma (1-a) := Real.Gamma_pos_of_pos (by linarith)
  have hgab : 0 < Real.Gamma (1-a/b) := Real.Gamma_pos_of_pos (by
    have : a/b < 1 := (div_lt_one hb).mpr ha
    linarith)
  have hi := stablePoissonTotal_rpow_integrable hb hb1 ha
  have hn : ∀ η : Measure ℝ, 0 ≤ stablePoissonTotal η^a := fun η =>
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have he := stablePoissonTotal_rpow_lintegral_mul hb hb1 ha
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)] at he
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal hga.le,ENNReal.toReal_ofReal
      (mul_nonneg hgab.le (Real.rpow_nonneg (Real.Gamma_pos_of_pos (by linarith : 0 < 1-b)).le _))] at her
  exact (eq_div_iff hga.ne').mpr her

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableMassKernel
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

lemma stableCountKernel_eq (η : Measure ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) :
    stableCountKernel η = η := by
  rw [stableCountKernel,Kernel.withDensity_apply _ (by fun_prop : Measurable
    (Function.uncurry (fun η x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x)))))]
  change (((η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ)⁻¹) •
    η.withDensity (fun x => ENNReal.ofReal (Real.exp x))).withDensity
      (fun x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) = η
  have hmass : η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ =
      ENNReal.ofReal (stablePoissonTotal η) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ENNReal.ofReal_toReal (by simpa [stableJumpMomentE] using hf)).symm
  rw [hmass,withDensity_smul_measure,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have hd : (fun x => ENNReal.ofReal (Real.exp x)*
      ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) =
      (fun _ : ℝ => ENNReal.ofReal (stablePoissonTotal η)) := by
    funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.exp_neg]
    field_simp
  change (ENNReal.ofReal (stablePoissonTotal η))⁻¹ • η.withDensity
    (fun x => ENNReal.ofReal (Real.exp x)*ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) = η
  rw [hd,withDensity_const,smul_smul,ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,one_smul]

lemma stableJumpMomentE_one_add_dirac (x : ℝ) (η : Measure ℝ) :
    stableJumpMomentE 1 (Measure.dirac x+η) = ENNReal.ofReal (Real.exp x)+stableJumpMomentE 1 η := by
  simp [stableJumpMomentE,lintegral_add_measure]

lemma stableCountKernel_add_dirac (η : Measure ℝ) (x : ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) :
    stableCountKernel (Measure.dirac x+η) = Measure.dirac x+η := by
  apply stableCountKernel_eq
  · rw [stableJumpMomentE_one_add_dirac]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hf⟩
  · rw [stablePoissonTotal_add_dirac x η (by simpa [stableJumpMomentE] using hf)]
    positivity

lemma cascadeMeasurableSet_exists {A I : Type*} [MeasurableSpace A] [Countable I]
    {p : I → A → Prop} (h : ∀ i, MeasurableSet {a | p i a}) :
    MeasurableSet {a | ∃ i, p i a} := by
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion h

lemma stableDistinctMoment_measurable (rs : List ℝ) (m : ℕ) :
    Measurable (fun p : Measure ℝ × (Fin m → ℝ) => stableDistinctMoment rs p.1 p.2) := by
  induction rs generalizing m with
  | nil => exact measurable_const
  | cons r rs ih =>
    let κ : Kernel (Measure ℝ × (Fin m → ℝ)) ℝ := stableCountKernel.comap (Prod.fst : Measure ℝ × (Fin m → ℝ) → Measure ℝ) measurable_fst
    have hD : Measurable (fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ =>
        stableDistinctMoment rs p.1.1 (Fin.cons p.2 p.1.2)) := by
      exact (ih (m+1)).comp (measurable_fst.fst.prodMk
        (measurable_fin_cons measurable_snd measurable_fst.snd))
    have hset : MeasurableSet {p : (Measure ℝ × (Fin m → ℝ)) × ℝ | ∃ i, p.1.2 i = p.2} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd
    exact (measurable_const.ite hset ((by fun_prop : Measurable (fun p :
      (Measure ℝ × (Fin m → ℝ)) × ℝ => ENNReal.ofReal (Real.exp (r*p.2)))).mul hD)).lintegral_kernel_prod_right'
      (κ := κ)

lemma stableDistinctMoment_add_dirac (rs : List ℝ) (η : Measure ℝ) (x : ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η)
    {m : ℕ} (z : Fin m → ℝ) (hz : ∃ i, z i = x) :
    stableDistinctMoment rs (Measure.dirac x+η) z = stableDistinctMoment rs η z := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    simp only [stableDistinctMoment,stableCountKernel_add_dirac η x hf hp,
      stableCountKernel_eq η hf hp,lintegral_add_measure,lintegral_dirac,ite_eq_left hz,zero_add]
    apply lintegral_congr
    intro y
    split_ifs
    · rfl
    · rw [ih (Fin.cons y z) (by obtain ⟨i,hi⟩ := hz; exact ⟨i.succ,hi⟩)]

lemma stableDistinctMoment_palm_laplace {b t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ht : 0 < t) (rs : List ℝ) (hr : ∀ r ∈ rs, b < r) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ((rs.map (fun r => ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)))).prod)*
        ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  induction rs generalizing m with
  | nil => simpa [stableDistinctMoment] using stablePoissonTotal_laplace_lintegral hb hb1 ht
  | cons r rs ih =>
    let P := poissonRandomMeasureLaw (stableLogIntensity b)
    let L := ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b))
    let C := (rs.map (fun r => ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)))).prod
    let H : Measure ℝ × ℝ → ℝ≥0∞ := fun p => if ∃ i, z i = p.2 then 0 else
      ENNReal.ofReal (Real.exp (r*p.2))*stableDistinctMoment rs p.1 (Fin.cons p.2 z)*
        ENNReal.ofReal (Real.exp (-t*stablePoissonTotal p.1))
    have hH : Measurable H := by
      have hD : Measurable (fun p : Measure ℝ × ℝ => stableDistinctMoment rs p.1 (Fin.cons p.2 z)) :=
        (stableDistinctMoment_measurable rs (m+1)).comp (measurable_fst.prodMk
          (measurable_fin_cons measurable_snd measurable_const))
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_snd) (by fun_prop)
    have hstart : (∫⁻ η, stableDistinctMoment (r::rs) η z*
        ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η)) ∂P) =
        ∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂P := by
      apply lintegral_congr_ae
      filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hf hp
      rw [stableDistinctMoment,stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp,
        ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      dsimp [H]
      split_ifs <;> simp
    have hinner (x : ℝ) : (∫⁻ η, H (Measure.dirac x+η,x) ∂P) =
        (if ∃ i, z i = x then 0 else ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)))*(C*L) := by
      by_cases hx : ∃ i, z i = x
      · simp [H,hx]
      have he : (fun η => H (Measure.dirac x+η,x)) =ᵐ[P]
          (fun η => ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
            (stableDistinctMoment rs η (Fin.cons x z)*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η)))) := by
        filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hf hp
        dsimp [H]
        rw [ite_eq_right hx,stableDistinctMoment_add_dirac rs η x (by simpa [stableJumpMomentE] using hf) hp
          (Fin.cons x z) ⟨0,rfl⟩,stablePoissonTotal_add_dirac x η hf,mul_add,Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      rw [lintegral_congr_ae he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ih (fun s hs => hr s (List.mem_cons_of_mem r hs)) (Fin.cons x z),ite_eq_right hx]
    rw [hstart,poissonRandomMeasureLaw_mecke _ hH]
    change (∫⁻ x, ∫⁻ η, H (Measure.dirac x+η,x) ∂P ∂stableLogIntensity b) = _
    simp_rw [hinner]
    rw [lintegral_mul_const]
    · have hx : ∀ᵐ x ∂stableLogIntensity b, ¬ ∃ i, z i = x := by
        filter_upwards [ae_all_iff.mpr (fun i : Fin m => (stableLogIntensity b).ae_ne (z i))] with x hx
        exact fun h => by obtain ⟨i,hi⟩ := h; exact hx i hi.symm
      rw [lintegral_congr_ae (hx.mono fun x hx => ite_eq_right hx),
        stableLogIntensity_laplace_moment hb.le (hr r (by simp)) ht]
      simp only [List.map_cons,List.prod_cons]
      dsimp [C,L]
      ring
    · exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_id) (by fun_prop)

lemma stableLaplaceProduct_shape {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (rs : List ℝ) (hr : ∀ r ∈ rs, b < r) :
    (rs.map (fun r => ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)))).prod =
      (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod*
        ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum)) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hrr : b < r := hr r (by simp)
    have hc : 0 ≤ b*Real.Gamma (r-b) := mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hrr)).le
    have he : ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)) =
        ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-r)) := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    simp only [List.map_cons,List.prod_cons,List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    rw [he,ih (fun v hv => hr v (List.mem_cons_of_mem r hv))]
    calc
      _ = (ENNReal.ofReal (b*Real.Gamma (r-b))*(rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod)*
          (ENNReal.ofReal (t^(b-r))*ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum))) := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),← Real.rpow_add ht]
        congr 3
        ring

lemma list_length_mul_le_sum {rs : List ℝ} {b : ℝ} (hr : ∀ r ∈ rs, b ≤ r) :
    (rs.length:ℝ)*b ≤ rs.sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hrr := hr r (by simp)
    have hi := ih (fun s hs => hr s (List.mem_cons_of_mem r hs))
    simp only [List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma stableDistinctMoment_palm_mellin_mul {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (rs : List ℝ) (hne : rs ≠ []) (hr : ∀ r ∈ rs, b < r)
    {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (rs.sum-a)) =
      (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod*
        ENNReal.ofReal ((Real.Gamma (1-b))^(a/b-(rs.length:ℝ))*(1/b)*
          Real.Gamma ((rs.length:ℝ)-a/b)) := by
  let P := poissonRandomMeasureLaw (stableLogIntensity b)
  let c := Real.Gamma (1-b)
  let A := (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hj : (1:ℝ) ≤ rs.length := by
    have hj : 1 ≤ rs.length := by cases rs <;> simp_all
    exact_mod_cast hj
  have hjb : 0 < (rs.length:ℝ)*b-a := by nlinarith
  have hsum : 0 < rs.sum-a := by
    have hsum := list_length_mul_le_sum (fun r hr' => (hr r hr').le)
    linarith
  have hD : Measurable (fun η => stableDistinctMoment rs η z) :=
    (stableDistinctMoment_measurable rs m).comp (measurable_id.prodMk measurable_const)
  let K := fun (η : Measure ℝ) (t : ℝ) => stableDistinctMoment rs η z*
    ENNReal.ofReal (t^(rs.sum-a-1)*Real.exp (-t*stablePoissonTotal η))
  have hm : Measurable (Function.uncurry K) := by
    exact (hD.comp measurable_fst).mul (by fun_prop)
  have hgamma : ∀ᵐ η ∂P,
      stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))*
        ENNReal.ofReal (Real.Gamma (rs.sum-a)) = ∫⁻ t : ℝ in Ioi 0, K η t := by
    filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
    dsimp [K]
    rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_positive_scale hsum hη,
      show -(rs.sum-a) = a-rs.sum by ring,ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _),mul_assoc]
  have hinner (t : ℝ) (ht : 0 < t) : (∫⁻ η, K η t ∂P) =
      A*ENNReal.ofReal (t^((rs.length:ℝ)*b-a-1)*Real.exp (-c*t^b)) := by
    have hfac (η : Measure ℝ) : K η t = ENNReal.ofReal (t^(rs.sum-a-1))*
        (stableDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))) := by
      dsimp [K]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      ring
    simp_rw [hfac]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      stableDistinctMoment_palm_laplace hb hb1 ht rs hr z,stableLaplaceProduct_shape hb ht rs hr]
    change ENNReal.ofReal (t^(rs.sum-a-1))*(A*ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum))*
      ENNReal.ofReal (Real.exp (-c*t^b))) = _
    calc
      _ = A*(ENNReal.ofReal (t^(rs.sum-a-1))*ENNReal.ofReal (t^((rs.length:ℝ)*b-rs.sum)))*
          ENNReal.ofReal (Real.exp (-c*t^b)) := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),← Real.rpow_add ht,
          show rs.sum-a-1+((rs.length:ℝ)*b-rs.sum) = (rs.length:ℝ)*b-a-1 by ring,
          mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  calc
    _ = ∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))*
        ENNReal.ofReal (Real.Gamma (rs.sum-a)) ∂P :=
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ η, (∫⁻ t : ℝ in Ioi 0, K η t) ∂P := lintegral_congr_ae hgamma
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ η, K η t ∂P := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t : ℝ in Ioi 0,
        A*ENNReal.ofReal (t^((rs.length:ℝ)*b-a-1)*Real.exp (-c*t^b)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hinner t ht
    _ = A*ENNReal.ofReal (c^(-(((rs.length:ℝ)*b-a-1)+1)/b)*(1/b)*
        Real.Gamma ((((rs.length:ℝ)*b-a-1)+1)/b)) := by
      rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_rpow_scale (by linarith) hb hc]
    _ = _ := by
      rw [show -(((rs.length:ℝ)*b-a-1)+1)/b = a/b-(rs.length:ℝ) by field_simp; ring,
        show (((rs.length:ℝ)*b-a-1)+1)/b = (rs.length:ℝ)-a/b by field_simp; ring]

lemma gamma_stable_product {a b : ℝ} (hb : 0 < b) (ha : a < b) (k : ℕ) :
    b^k * Real.Gamma (((k+1:ℕ):ℝ)-a/b) =
      Real.Gamma (1-a/b) * ∏ ℓ ∈ Finset.range k, (((ℓ:ℝ)+1)*b-a) := by
  have hab : a/b < 1 := (div_lt_one hb).mpr ha
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < ((k+1:ℕ):ℝ)-a/b := by
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      push_cast
      linarith
    rw [show ((k+1+1:ℕ):ℝ)-a/b = (((k+1:ℕ):ℝ)-a/b)+1 by push_cast; ring,
      Real.Gamma_add_one hp.ne',pow_succ,Finset.prod_range_succ]
    calc
      _ = (b^k*Real.Gamma (((k+1:ℕ):ℝ)-a/b))*(((k:ℝ)+1)*b-a) := by
        push_cast
        field_simp
      _ = _ := by rw [ih]; ring

lemma stable_eppf_scalar {a b c n G : ℝ} (hb : 0 < b) (ha : a < b)
    (hc : 0 < c) (hn : 0 < n-a) (ha1 : a < 1) (k : ℕ) :
    (b^(k+1)*G*(c^(a/b-((k+1:ℕ):ℝ))*(1/b)*Real.Gamma (((k+1:ℕ):ℝ)-a/b)) /
      Real.Gamma (n-a))/(Real.Gamma (1-a/b)*c^(a/b)/Real.Gamma (1-a)) =
    Real.Gamma (1-a)/Real.Gamma (n-a)*
      (∏ ℓ ∈ Finset.range k, (((ℓ:ℝ)+1)*b-a))*(G/c^(k+1)) := by
  have hγ : Real.Gamma (1-a/b) ≠ 0 := (Real.Gamma_pos_of_pos (by
    have := (div_lt_one hb).mpr ha
    linarith)).ne'
  have hγn : Real.Gamma (n-a) ≠ 0 := (Real.Gamma_pos_of_pos hn).ne'
  have hpow : c^(a/b) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hg := gamma_stable_product hb ha k
  rw [Real.rpow_sub hc, Real.rpow_natCast]
  have hga : Real.Gamma (1-a) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne'
  have hcpow : c^(k+1) ≠ 0 := pow_ne_zero _ hc.ne'
  have hN : b^(k+1)*G*(c^(a/b)/c^(k+1)*(1/b)*Real.Gamma (((k+1:ℕ):ℝ)-a/b)) =
      G*(c^(a/b)/c^(k+1))*(b^k*Real.Gamma (((k+1:ℕ):ℝ)-a/b)) := by
    rw [pow_succ]
    field_simp
  rw [hN,hg]
  have hγ' : Real.Gamma ((b-a)/b) ≠ 0 := by simpa [sub_div, hb.ne'] using hγ
  field_simp

lemma list_prod_map_const_mul (c : ℝ) (f : ℝ → ℝ) (rs : List ℝ) :
    (rs.map (fun r => c*f r)).prod = c^rs.length*(rs.map f).prod := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ih]; ring

lemma list_prod_map_div_const (c : ℝ) (f : ℝ → ℝ) (rs : List ℝ) :
    (rs.map (fun r => f r/c)).prod = (rs.map f).prod/c^rs.length := by
  simp [div_eq_mul_inv,mul_comm,inv_pow]

lemma list_prod_ofReal (rs : List ℝ) (hr : ∀ r ∈ rs, 0 ≤ r) :
    (rs.map ENNReal.ofReal).prod = ENNReal.ofReal rs.prod := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.map_cons,List.prod_cons,List.prod_cons,ih (fun x hx => hr x (by simp [hx])),
      ENNReal.ofReal_mul (hr r (by simp))]

theorem stableDistinctMoment_eppf {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (rs : List ℝ) (hne : rs ≠ []) (hr : ∀ r ∈ rs, b < r)
    {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))/
      (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
        ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma (rs.sum-a)*
        (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
        (rs.map (fun r => Real.Gamma (r-b)/Real.Gamma (1-b))).prod) := by
  let c := Real.Gamma (1-b)
  let G := (rs.map (fun r => Real.Gamma (r-b))).prod
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hga : 0 < Real.Gamma (1-a) := Real.Gamma_pos_of_pos (by linarith)
  have hgab : 0 < Real.Gamma (1-a/b) := Real.Gamma_pos_of_pos (by
    have := (div_lt_one hb).mpr ha
    linarith)
  have hj : 1 ≤ rs.length := by cases rs <;> simp_all
  have hjR : (1:ℝ) ≤ rs.length := by exact_mod_cast hj
  have hj1 : rs.length-1+1 = rs.length := Nat.sub_add_cancel hj
  have hsum : 0 < rs.sum-a := by
    have := list_length_mul_le_sum (fun r hr' => (hr r hr').le)
    nlinarith
  have hgn : 0 < Real.Gamma (rs.sum-a) := Real.Gamma_pos_of_pos hsum
  have hG : 0 ≤ G := List.prod_nonneg (by
    intro x hx
    obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hx
    exact (Real.Gamma_pos_of_pos (sub_pos.mpr (hr r hr'))).le)
  have hA : (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod =
      ENNReal.ofReal (b^rs.length*G) := by
    rw [show (rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))) =
      (rs.map (fun r => b*Real.Gamma (r-b))).map ENNReal.ofReal by simp only [List.map_map,Function.comp_def],
      list_prod_ofReal _ (by
        intro x hx
        obtain ⟨r,hr',rfl⟩ := List.mem_map.mp hx
        exact mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr (hr r hr'))).le),
      list_prod_map_const_mul]
  have hMpos : 0 < Real.Gamma (1-a/b)*c^(a/b)/Real.Gamma (1-a) :=
    div_pos (mul_pos hgab (Real.rpow_pos_of_pos hc _)) hga
  have hM : (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.Gamma (1-a/b)*c^(a/b)/Real.Gamma (1-a)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (stablePoissonTotal_rpow_integrable hb hb1 ha)
      (ae_of_all _ (fun η => Real.rpow_nonneg ENNReal.toReal_nonneg _)),
      stablePoissonTotal_rpow_integral hb hb1 ha]
  have he := stableDistinctMoment_palm_mellin_mul hb hb1 ha rs hne hr z
  have hI : (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ((rs.map (fun r => ENNReal.ofReal (b*Real.Gamma (r-b)))).prod*
        ENNReal.ofReal ((Real.Gamma (1-b))^(a/b-(rs.length:ℝ))*(1/b)*
          Real.Gamma ((rs.length:ℝ)-a/b)))/ENNReal.ofReal (Real.Gamma (rs.sum-a)) := by
    apply (ENNReal.eq_div_iff (ENNReal.ofReal_ne_zero_iff.mpr hgn) ENNReal.ofReal_ne_top).mpr
    rw [mul_comm]
    exact he
  rw [hI,hA,hM,← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hb.le _) hG),
    ← ENNReal.ofReal_div_of_pos hgn,← ENNReal.ofReal_div_of_pos hMpos]
  congr 1
  rw [list_prod_map_div_const]
  exact (by simpa only [hj1,c,G] using stable_eppf_scalar hb ha hc hsum (by linarith) (rs.length-1))

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

lemma stableEppfValue_singleton_one {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    stableEppfValue a b [1] = 1 := by
  have hga : Real.Gamma (1-a) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr ha)).ne'
  have hgb : Real.Gamma (1-b) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr hb)).ne'
  simp [stableEppfValue,hga,hgb]

lemma stableOrderedDistinctMass_measurable (rs : List ℝ) {m : ℕ} (z : Fin m → ℝ) :
    Measurable (fun η => stableOrderedDistinctMass rs η z) :=
  ((stableDistinctMoment_measurable rs m).comp (measurable_id.prodMk measurable_const)).mul (by fun_prop)

lemma stableOrderedDistinctMass_biased {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (_ha : a < b) (rs : List ℝ) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableOrderedDistinctMass rs η z ∂stableTotalBiasedLaw a b) =
    (∫⁻ η, stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(a-rs.sum))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))/
      (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
        ∂poissonRandomMeasureLaw (stableLogIntensity b)) := by
  unfold stableTotalBiasedLaw normalizedMeasure
  rw [lintegral_smul_measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (stableOrderedDistinctMass_measurable rs z)]
  simp only [smul_eq_mul,Pi.mul_apply]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [stablePoissonTotal_pos hb hb1] with η hp
  unfold stableOrderedDistinctMass
  calc
    _ = stableDistinctMoment rs η z*(ENNReal.ofReal (stablePoissonTotal η^a)*
      ENNReal.ofReal (stablePoissonTotal η^(-rs.sum))) := by ring
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _),← Real.rpow_add hp,sub_eq_add_neg]

lemma stableOrderedDistinctMass_eppf {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (rs : List ℝ) (hne : rs ≠ []) (hr : ∀ r ∈ rs, b < r)
    {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableOrderedDistinctMass rs η z ∂stableTotalBiasedLaw a b) =
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma (rs.sum-a)*
        (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
        (rs.map (fun r => Real.Gamma (r-b)/Real.Gamma (1-b))).prod) := by
  rw [stableOrderedDistinctMass_biased hb hb1 ha,stableDistinctMoment_eppf hb hb1 ha rs hne hr]

lemma stableCountAtom_measurable :
    Measurable (fun p : Measure ℝ × ℝ => stableCountKernel p.1 {p.2}) := by
  let κ : Kernel (Measure ℝ × ℝ) ℝ := stableCountKernel.comap (Prod.fst : Measure ℝ × ℝ → Measure ℝ) measurable_fst
  have hm : Measurable (fun p : (Measure ℝ × ℝ) × ℝ => if p.2 = p.1.2 then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_eq_fun measurable_snd measurable_fst.snd) measurable_const
  have hh := hm.lintegral_kernel_prod_right' (κ := κ)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  change _ = ∫⁻ y, if y = p.2 then (1:ℝ≥0∞) else 0 ∂stableCountKernel p.1
  rw [show (fun y : ℝ => if y = p.2 then (1:ℝ≥0∞) else 0) =
    ({p.2}:Set ℝ).indicator (fun _ => (1:ℝ≥0∞)) by rfl,
    lintegral_indicator (measurableSet_singleton _),lintegral_one,Measure.restrict_apply_univ]

lemma stablePoissonCount_simple {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b), ∀ᵐ x ∂η, η {x} = 1 := by
  let P := poissonRandomMeasureLaw (stableLogIntensity b)
  let H := fun p : Measure ℝ × ℝ => if stableCountKernel p.1 {p.2} = 1 then (0:ℝ≥0∞) else 1
  have hm : Measurable H := measurable_const.ite (measurableSet_eq_fun stableCountAtom_measurable measurable_const) measurable_const
  have hright (x : ℝ) : (∫⁻ η, H (Measure.dirac x+η,x) ∂P) = 0 := by
    apply (lintegral_eq_zero_iff (hm.comp ((measurable_const.add measurable_id).prodMk measurable_const))).mpr
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1,
      poissonRandomMeasureLaw_ae_null (stableLogIntensity b) (measurableSet_singleton x) (measure_singleton x)] with η hf hp hnull
    have hf' : stableJumpMomentE 1 η ≠ ⊤ := by simpa [stableJumpMomentE] using hf
    simp [H,stableCountKernel_add_dirac η x hf' hp,hnull]
  have he : (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂P) = 0 := by
    rw [poissonRandomMeasureLaw_mecke (stableLogIntensity b) hm]
    change (∫⁻ x, ∫⁻ η, H (Measure.dirac x+η,x) ∂P ∂stableLogIntensity b) = 0
    simp_rw [hright]
    exact lintegral_zero
  have hkernel : Measurable (fun η => ∫⁻ x, H (η,x) ∂stableCountKernel η) :=
    hm.lintegral_kernel_prod_right'
  have he' : (∫⁻ η, ∫⁻ x, H (η,x) ∂stableCountKernel η ∂P) = 0 := by
    rw [← he]
    apply lintegral_congr_ae
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hf hp
    rw [stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp]
  have hae := (lintegral_eq_zero_iff hkernel).mp he'
  filter_upwards [hae,stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hzero hf hp
  rw [stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp] at hzero
  have hz := (lintegral_eq_zero_iff (hm.comp (measurable_const.prodMk measurable_id))).mp hzero
  filter_upwards [hz] with x hx
  dsimp [H] at hx
  rw [stableCountKernel_eq η (by simpa [stableJumpMomentE] using hf) hp] at hx
  by_contra h
  simp [h] at hx

lemma stableMassKernel_atom_eq (η : Measure ℝ) {x : ℝ}
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) (hx : η {x} = 1) :
    stableMassKernel η {x} = ENNReal.ofReal (Real.exp x/stablePoissonTotal η) := by
  change ((η.withDensity (fun y => ENNReal.ofReal (Real.exp y)) univ)⁻¹ •
    η.withDensity (fun y => ENNReal.ofReal (Real.exp y))) {x} = _
  rw [Measure.smul_apply,smul_eq_mul,withDensity_apply _ (measurableSet_singleton x),lintegral_singleton,hx,mul_one,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have htotal : (∫⁻ y, ENNReal.ofReal (Real.exp y) ∂η) = ENNReal.ofReal (stablePoissonTotal η) := by
    exact (ENNReal.ofReal_toReal (by simpa [stableJumpMomentE] using hf)).symm
  rw [htotal,ENNReal.ofReal_div_of_pos hp,div_eq_mul_inv,mul_comm]

lemma stableMassAtom_measurable :
    Measurable (fun p : Measure ℝ × ℝ => stableMassKernel p.1 {p.2}) := by
  let κ : Kernel (Measure ℝ × ℝ) ℝ := stableMassKernel.comap (Prod.fst : Measure ℝ × ℝ → Measure ℝ) measurable_fst
  have hm : Measurable (fun p : (Measure ℝ × ℝ) × ℝ => if p.2 = p.1.2 then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_eq_fun measurable_snd measurable_fst.snd) measurable_const
  have hh := hm.lintegral_kernel_prod_right' (κ := κ)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  change _ = ∫⁻ y, if y = p.2 then (1:ℝ≥0∞) else 0 ∂stableMassKernel p.1
  rw [show (fun y : ℝ => if y = p.2 then (1:ℝ≥0∞) else 0) =
    ({p.2}:Set ℝ).indicator (fun _ => (1:ℝ≥0∞)) by rfl,
    lintegral_indicator (measurableSet_singleton _),lintegral_one,Measure.restrict_apply_univ]

lemma stableMassAtom_measurable_comp {A : Type*} [MeasurableSpace A]
    {f : A → Measure ℝ} {g : A → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => stableMassKernel (f a) {g a}) := by
  exact Measurable.comp (g := (fun p : Measure ℝ × ℝ => stableMassKernel p.1 {p.2}))
    (f := (fun a => (f a,g a))) stableMassAtom_measurable (hf.prodMk hg)

lemma stableBlockProbability_measurable (ns : List ℕ) (m : ℕ) :
    Measurable (fun p : Measure ℝ × (Fin m → ℝ) => stableBlockProbability ns p.1 p.2) := by
  induction ns generalizing m with
  | nil => exact measurable_const
  | cons n ns ih =>
    let κ : Kernel (Measure ℝ × (Fin m → ℝ)) ℝ := stableMassKernel.comap (Prod.fst : Measure ℝ × (Fin m → ℝ) → Measure ℝ) measurable_fst
    have hD : Measurable (fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ =>
        stableBlockProbability ns p.1.1 (Fin.cons p.2 p.1.2)) := by
      exact (ih (m+1)).comp (measurable_fst.fst.prodMk
        (measurable_fin_cons measurable_snd measurable_fst.snd))
    have ha : Measurable (fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ =>
        stableMassKernel p.1.1 {p.2}) :=
      stableMassAtom_measurable_comp (f := fun p : (Measure ℝ × (Fin m → ℝ)) × ℝ => p.1.1)
        (g := fun p => p.2) measurable_fst.fst measurable_snd
    have hset : MeasurableSet {p : (Measure ℝ × (Fin m → ℝ)) × ℝ | ∃ i, p.1.2 i = p.2} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd
    exact (measurable_const.ite hset ((ha.pow_const _).mul hD)).lintegral_kernel_prod_right' (κ := κ)

lemma stableBlockProbability_moment (ns : List ℕ) (hn : ∀ n ∈ ns, 1 ≤ n) (η : Measure ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η)
    (hs : ∀ᵐ x ∂η, η {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    stableBlockProbability ns η z = stableDistinctMoment (ns.map (fun n : ℕ => (n:ℝ))) η z*
      ((ENNReal.ofReal (stablePoissonTotal η))⁻¹)^ns.sum := by
  induction ns generalizing m with
  | nil => simp [stableBlockProbability,stableDistinctMoment]
  | cons n ns ih =>
    have hn0 : 1 ≤ n := hn n (by simp)
    have hn' : n-1+1 = n := Nat.sub_add_cancel hn0
    have hns : ∀ k ∈ ns, 1 ≤ k := fun k hk => hn k (by simp [hk])
    have hm : Measurable (fun x => if ∃ i, z i = x then (0:ℝ≥0∞) else
        (stableMassKernel η {x})^(n-1)*stableBlockProbability ns η (Fin.cons x z)) := by
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_id)
        (((stableMassAtom_measurable.comp (measurable_const.prodMk measurable_id)).pow_const _).mul
          ((stableBlockProbability_measurable ns (m+1)).comp
            (measurable_const.prodMk (measurable_fin_cons measurable_id measurable_const))))
    have htotal : (η.withDensity (fun x => ENNReal.ofReal (Real.exp x))) univ =
        ENNReal.ofReal (stablePoissonTotal η) := by
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      exact (ENNReal.ofReal_toReal (by simpa [stableJumpMomentE] using hf)).symm
    unfold stableBlockProbability
    change (∫⁻ x, (if ∃ i, z i = x then 0 else (stableMassKernel η {x})^(n-1)*
      stableBlockProbability ns η (Fin.cons x z)) ∂normalizedMeasure
        (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)))) = _
    rw [normalizedMeasure,lintegral_smul_measure,htotal,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm]
    simp only [smul_eq_mul,Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp))]
    have hpoint : (fun x => (ENNReal.ofReal (stablePoissonTotal η))⁻¹ *
        (ENNReal.ofReal (Real.exp x)*(if ∃ i, z i = x then 0 else
          (stableMassKernel η {x})^(n-1)*stableBlockProbability ns η (Fin.cons x z)))) =ᵐ[η]
        (fun x => (if ∃ i, z i = x then 0 else ENNReal.ofReal (Real.exp ((n:ℝ)*x))*
          stableDistinctMoment (ns.map (fun n : ℕ => (n:ℝ))) η (Fin.cons x z))*
          ((ENNReal.ofReal (stablePoissonTotal η))⁻¹)^(n+ns.sum)) := by
      filter_upwards [hs] with x hx
      split_ifs
      · simp
      · rw [stableMassKernel_atom_eq η hf hp hx,ENNReal.ofReal_div_of_pos hp,
          ih hns (Fin.cons x z),div_eq_mul_inv,mul_pow,Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_pos _).le,
          pow_add,← hn',pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
    rw [lintegral_congr_ae hpoint,lintegral_mul_const' _ _ (ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp)))]
    simp only [List.map_cons,List.sum_cons]
    rw [stableDistinctMoment,stableCountKernel_eq η hf hp]

lemma stableTotalBiasedLaw_absolutelyContinuous (a b : ℝ) :
    stableTotalBiasedLaw a b ≪ poissonRandomMeasureLaw (stableLogIntensity b) := by
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

lemma stableBlockProbability_ordered (ns : List ℕ) (hn : ∀ n ∈ ns, 1 ≤ n) (η : Measure ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η)
    (hs : ∀ᵐ x ∂η, η {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    stableBlockProbability ns η z = stableOrderedDistinctMass (ns.map (fun n : ℕ => (n:ℝ))) η z := by
  rw [stableBlockProbability_moment ns hn η hf hp hs]
  unfold stableOrderedDistinctMass
  congr 1
  rw [Real.rpow_neg hp.le,ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hp _)]
  have hsum : (ns.map (fun n : ℕ => (n:ℝ))).sum = (ns.sum:ℝ) := by
    induction ns with
    | nil => simp
    | cons n ns ih => simp
  rw [hsum,Real.rpow_natCast,ENNReal.ofReal_pow hp.le,ENNReal.inv_pow]

lemma stableBlockProbability_eppf {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (ns : List ℕ) (hne : ns ≠ []) (hn : ∀ n ∈ ns, 1 ≤ n) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, stableBlockProbability ns η z ∂stableTotalBiasedLaw a b) =
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma ((ns.map (fun n : ℕ => (n:ℝ))).sum-a)*
        (∏ ℓ ∈ Finset.range (ns.length-1), (((ℓ:ℝ)+1)*b-a))*
        (ns.map (fun n : ℕ => Real.Gamma ((n:ℝ)-b)/Real.Gamma (1-b))).prod) := by
  have hr : ∀ r ∈ ns.map (fun n : ℕ => (n:ℝ)), b < r := by
    intro r hr
    obtain ⟨n,hnn,rfl⟩ := List.mem_map.mp hr
    exact hb1.trans_le (by exact_mod_cast hn n hnn)
  have he := stableOrderedDistinctMass_eppf hb hb1 ha (ns.map (fun n : ℕ => (n:ℝ)))
    (by simpa using hne) hr z
  have hae : (fun η => stableBlockProbability ns η z) =ᵐ[stableTotalBiasedLaw a b]
      (fun η => stableOrderedDistinctMass (ns.map (fun n : ℕ => (n:ℝ))) η z) := by
    apply (stableTotalBiasedLaw_absolutelyContinuous a b).ae_eq
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1,
      stablePoissonCount_simple hb hb1] with η hf hp hs
    exact stableBlockProbability_ordered ns hn η (by simpa [stableJumpMomentE] using hf) hp hs z
  rw [lintegral_congr_ae hae]
  simpa only [List.length_map,List.map_map,Function.comp_def] using he

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

lemma markedStableTotalE_add_dirac (p : ℝ × S) (η : Measure (ℝ × S)) :
    markedStableTotalE (Measure.dirac p+η) = ENNReal.ofReal (Real.exp p.1)+markedStableTotalE η := by
  simp only [markedStableTotalE,lintegral_add_measure]
  rw [lintegral_dirac' _ (by fun_prop)]

lemma markedStableTotal_add_dirac (p : ℝ × S) (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) :
    markedStableTotal (Measure.dirac p+η) = Real.exp p.1+markedStableTotal η := by
  rw [markedStableTotal,markedStableTotalE_add_dirac,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hf,ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rfl

lemma markedStableCountKernel_add_dirac (η : Measure (ℝ × S)) (p : ℝ × S)
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η) :
    markedStableCountKernel (Measure.dirac p+η) = Measure.dirac p+η := by
  apply markedStableCountKernel_eq
  · rw [markedStableTotalE_add_dirac]; exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hf⟩
  · rw [markedStableTotal_add_dirac p η hf]; linarith [Real.exp_pos p.1]

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

lemma markedStable_laplace (ν : Measure S) [IsProbabilityMeasure ν] {b t : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫⁻ η, ENNReal.ofReal (Real.exp (-t*markedStableTotal η))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have he := stablePoissonTotal_laplace_lintegral hb hb1 ht
  rw [← markedStable_project_law ν b] at he
  rw [lintegral_map (by fun_prop) (Measure.measurable_map _ measurable_fst)] at he
  simpa only [markedStableTotal_projection] using he

omit [Nonempty S] in
lemma markedDistinctMoment_measurable (rs : List (ℝ × (S → ℝ≥0∞)))
    (hr : ∀ rf ∈ rs, Measurable rf.2) (m : ℕ) :
    Measurable (fun p : Measure (ℝ × S) × (Fin m → ℝ) => markedDistinctMoment rs p.1 p.2) := by
  induction rs generalizing m with
  | nil => exact measurable_const
  | cons rf rs ih =>
    let κ : Kernel (Measure (ℝ × S) × (Fin m → ℝ)) (ℝ × S) := markedStableCountKernel.comap
      (Prod.fst : Measure (ℝ × S) × (Fin m → ℝ) → Measure (ℝ × S)) measurable_fst
    have hD : Measurable (fun p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) =>
        markedDistinctMoment rs p.1.1 (Fin.cons p.2.1 p.1.2)) := by
      exact (ih (fun r hr' => hr r (List.mem_cons_of_mem rf hr')) (m+1)).comp
        (measurable_fst.fst.prodMk (measurable_fin_cons measurable_snd.fst measurable_fst.snd))
    have hset : MeasurableSet {p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) |
        ∃ i, p.1.2 i = p.2.1} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd.fst
    exact (measurable_const.ite hset (((by fun_prop : Measurable (fun p :
      (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) => ENNReal.ofReal (Real.exp (rf.1*p.2.1)))).mul
      ((hr rf (by simp)).comp measurable_snd.snd)).mul hD)).lintegral_kernel_prod_right' (κ := κ)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedTotalBiasedLaw
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
variable [Nonempty S]
omit [Nonempty S] in
lemma markedDistinctMoment_add_dirac (rs : List (ℝ × (S → ℝ≥0∞)))
    (hr : ∀ rf ∈ rs, Measurable rf.2) (η : Measure (ℝ × S)) (p : ℝ × S)
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η)
    {m : ℕ} (z : Fin m → ℝ) (hz : ∃ i, z i = p.1) :
    markedDistinctMoment rs (Measure.dirac p+η) z = markedDistinctMoment rs η z := by
  induction rs generalizing m with
  | nil => rfl
  | cons rf rs ih =>
    have ht : ∀ r ∈ rs, Measurable r.2 := fun r hr' => hr r (List.mem_cons_of_mem rf hr')
    have hm : Measurable (fun q : ℝ × S => if ∃ i, z i = q.1 then (0:ℝ≥0∞) else
        ENNReal.ofReal (Real.exp (rf.1*q.1))*rf.2 q.2*
          markedDistinctMoment rs (Measure.dirac p+η) (Fin.cons q.1 z)) := by
      have hF : Measurable (fun q : ℝ × S => ENNReal.ofReal (Real.exp (rf.1*q.1))*rf.2 q.2) :=
        (by fun_prop : Measurable (fun q : ℝ × S => ENNReal.ofReal (Real.exp (rf.1*q.1)))).mul
          ((hr rf (by simp)).comp measurable_snd)
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_fst)
        (hF.mul ((markedDistinctMoment_measurable rs ht (m+1)).comp
            (measurable_const.prodMk (measurable_fin_cons measurable_fst measurable_const))))
    rw [markedDistinctMoment,markedStableCountKernel_add_dirac η p hf hp,
      lintegral_add_measure,lintegral_dirac' _ hm,ite_eq_left hz,zero_add,
      markedDistinctMoment,markedStableCountKernel_eq η hf hp]
    apply lintegral_congr
    intro q
    split_ifs
    · rfl
    · rw [ih ht (Fin.cons q.1 z) (by obtain ⟨i,hi⟩ := hz; exact ⟨i.succ,hi⟩)]

lemma markedDistinctMoment_palm_laplace (ν : Measure S) [IsProbabilityMeasure ν]
    {b t : ℝ} (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*markedStableTotal η))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      ((rs.map (fun rf => ENNReal.ofReal (b*t^(b-rf.1)*Real.Gamma (rf.1-b))*(∫⁻ c, rf.2 c ∂ν))).prod)*
        ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  induction rs generalizing m with
  | nil => simpa [markedDistinctMoment] using markedStable_laplace ν hb hb1 ht
  | cons rf rs ih =>
    have hmt : ∀ r ∈ rs, Measurable r.2 := fun r hr' => hm r (List.mem_cons_of_mem rf hr')
    let P := poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)
    let L := ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b))
    let C := (rs.map (fun r => ENNReal.ofReal (b*t^(b-r.1)*Real.Gamma (r.1-b))*(∫⁻ c, r.2 c ∂ν))).prod
    let H : Measure (ℝ × S) × (ℝ × S) → ℝ≥0∞ := fun p => if ∃ i, z i = p.2.1 then 0 else
      ENNReal.ofReal (Real.exp (rf.1*p.2.1))*rf.2 p.2.2*
        markedDistinctMoment rs p.1 (Fin.cons p.2.1 z)*
        ENNReal.ofReal (Real.exp (-t*markedStableTotal p.1))
    have hH : Measurable H := by
      have hD : Measurable (fun p : Measure (ℝ × S) × (ℝ × S) =>
          markedDistinctMoment rs p.1 (Fin.cons p.2.1 z)) :=
        (markedDistinctMoment_measurable rs hmt (m+1)).comp (measurable_fst.prodMk
          (measurable_fin_cons measurable_snd.fst measurable_const))
      have hF : Measurable (fun p : Measure (ℝ × S) × (ℝ × S) =>
          ENNReal.ofReal (Real.exp (rf.1*p.2.1))*rf.2 p.2.2) :=
        (by fun_prop : Measurable (fun p : Measure (ℝ × S) × (ℝ × S) => ENNReal.ofReal (Real.exp (rf.1*p.2.1)))).mul
          ((hm rf (by simp)).comp measurable_snd.snd)
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_snd.fst) ((hF.mul hD).mul (by fun_prop))
    have hstart : (∫⁻ η, markedDistinctMoment (rf::rs) η z*
        ENNReal.ofReal (Real.exp (-t*markedStableTotal η)) ∂P) =
        ∫⁻ η, ∫⁻ p, H (η,p) ∂η ∂P := by
      apply lintegral_congr_ae
      filter_upwards [markedStable_regular ν hb hb1] with η hη
      rw [markedDistinctMoment,markedStableCountKernel_eq η hη.1 hη.2,
        ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro p
      dsimp [H]
      split_ifs <;> simp
    have hinner (p : ℝ × S) : (∫⁻ η, H (Measure.dirac p+η,p) ∂P) =
        (if ∃ i, z i = p.1 then 0 else ENNReal.ofReal (Real.exp (rf.1*p.1)*Real.exp (-t*Real.exp p.1))*rf.2 p.2)*(C*L) := by
      by_cases hx : ∃ i, z i = p.1
      · simp [H,hx]
      have he : (fun η => H (Measure.dirac p+η,p)) =ᵐ[P]
          (fun η => (ENNReal.ofReal (Real.exp (rf.1*p.1)*Real.exp (-t*Real.exp p.1))*rf.2 p.2)*
            (markedDistinctMoment rs η (Fin.cons p.1 z)*ENNReal.ofReal (Real.exp (-t*markedStableTotal η)))) := by
        filter_upwards [markedStable_regular ν hb hb1] with η hη
        dsimp [H]
        rw [ite_eq_right hx,markedDistinctMoment_add_dirac rs hmt η p hη.1 hη.2
          (Fin.cons p.1 z) ⟨0,rfl⟩,markedStableTotal_add_dirac p η hη.1,mul_add,Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      have hM : Measurable (fun η => markedDistinctMoment rs η (Fin.cons p.1 z)*
          ENNReal.ofReal (Real.exp (-t*markedStableTotal η))) :=
        ((markedDistinctMoment_measurable rs hmt (m+1)).comp (measurable_id.prodMk measurable_const)).mul (by fun_prop)
      rw [lintegral_congr_ae he,lintegral_const_mul _ hM,
        ih (fun r hr' => hr r (List.mem_cons_of_mem rf hr')) hmt (Fin.cons p.1 z),ite_eq_right hx]
    rw [hstart,poissonRandomMeasureLaw_mecke _ hH]
    change (∫⁻ p, ∫⁻ η, H (Measure.dirac p+η,p) ∂P ∂(stableLogIntensity b).prod ν) = _
    simp_rw [hinner]
    rw [lintegral_mul_const]
    · have hx : ∀ᵐ x ∂stableLogIntensity b, ¬ ∃ i, z i = x := by
        filter_upwards [ae_all_iff.mpr (fun i : Fin m => (stableLogIntensity b).ae_ne (z i))] with x hx
        exact fun h => by obtain ⟨i,hi⟩ := h; exact hx i hi.symm
      have hp : ∀ᵐ p ∂(stableLogIntensity b).prod ν, ¬ ∃ i, z i = p.1 :=
        (measurePreserving_fst (μ := stableLogIntensity b) (ν := ν)).quasiMeasurePreserving.ae hx
      rw [lintegral_congr_ae (hp.mono fun p hp => ite_eq_right hp),lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (Real.exp (rf.1*x)*Real.exp (-t*Real.exp x)))
          (g := rf.2) (by fun_prop) (hm rf (by simp)).aemeasurable,
        stableLogIntensity_laplace_moment hb.le (hr rf (by simp)) ht]
      simp only [List.map_cons,List.prod_cons]
      dsimp [C,L]
      ring
    · exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_fst)
        ((by fun_prop : Measurable (fun p : ℝ × S => ENNReal.ofReal (Real.exp (rf.1*p.1)*Real.exp (-t*Real.exp p.1)))).mul ((hm rf (by simp)).comp measurable_snd))

lemma markedDistinctMoment_laplace_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {b t : ℝ} (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (Real.exp (-t*markedStableTotal η))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      (rs.map (fun rf => ∫⁻ c, rf.2 c ∂ν)).prod*
        (∫⁻ η, stableDistinctMoment (rs.map Prod.fst) η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
          ∂poissonRandomMeasureLaw (stableLogIntensity b)) := by
  rw [markedDistinctMoment_palm_laplace ν hb hb1 ht rs hr hm,
    stableDistinctMoment_palm_laplace hb hb1 ht (rs.map Prod.fst)
      (by intro r hr'; obtain ⟨rf,hmem,rfl⟩ := List.mem_map.mp hr'; exact hr rf hmem)]
  simp only [List.prod_map_mul,List.map_map,Function.comp_def]
  ring

omit [Nonempty S] in
lemma mellin_weighted_identity (μ : Measure S) [SFinite μ] {D : S → ℝ≥0∞} {T : S → ℝ}
    (hD : Measurable D) (hT : Measurable T) (hpos : ∀ᵐ x ∂μ, 0 < T x) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, D x*ENNReal.ofReal (T x^(-q)) ∂μ)*ENNReal.ofReal (Real.Gamma q) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^(q-1))*
        (∫⁻ x, D x*ENNReal.ofReal (Real.exp (-t*T x)) ∂μ) := by
  have hm : Measurable (fun p : S × ℝ => D p.1*ENNReal.ofReal (p.2^(q-1)*Real.exp (-p.2*T p.1))) :=
    (hD.comp measurable_fst).mul (by fun_prop)
  calc
    _ = ∫⁻ x, D x*ENNReal.ofReal (T x^(-q))*ENNReal.ofReal (Real.Gamma q) ∂μ :=
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x, (∫⁻ t : ℝ in Ioi 0, D x*ENNReal.ofReal (t^(q-1)*Real.exp (-t*T x))) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with x hx
      rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_positive_scale hq hx,
        ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),mul_assoc]
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ x, D x*ENNReal.ofReal (t^(q-1)*Real.exp (-t*T x)) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),show ∀ x,
        D x*(ENNReal.ofReal (t^(q-1))*ENNReal.ofReal (Real.exp (-t*T x))) =
        ENNReal.ofReal (t^(q-1))*(D x*ENNReal.ofReal (Real.exp (-t*T x))) from fun x => by ring]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma markedDistinctMoment_mellin_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hne : rs ≠ []) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (markedStableTotal η^(a-(rs.map Prod.fst).sum))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      (rs.map (fun rf => ∫⁻ c, rf.2 c ∂ν)).prod*
        (∫⁻ η, stableDistinctMoment (rs.map Prod.fst) η z*ENNReal.ofReal (stablePoissonTotal η^(a-(rs.map Prod.fst).sum))
          ∂poissonRandomMeasureLaw (stableLogIntensity b)) := by
  let q := (rs.map Prod.fst).sum-a
  have hrr : ∀ r ∈ rs.map Prod.fst, b < r := by
    intro r hr'; obtain ⟨rf,hmem,rfl⟩ := List.mem_map.mp hr'; exact hr rf hmem
  have hj : (1:ℝ) ≤ rs.length := by
    have hj : 1 ≤ rs.length := by cases rs <;> simp_all
    exact_mod_cast hj
  have hq : 0 < q := by
    have hs := list_length_mul_le_sum (fun r hr' => (hrr r hr').le)
    simp only [List.length_map] at hs
    dsimp [q]; nlinarith
  have hG0 : ENNReal.ofReal (Real.Gamma q) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.Gamma_pos_of_pos hq)
  have hDm : Measurable (fun η => markedDistinctMoment rs η z) :=
    (markedDistinctMoment_measurable rs hm m).comp (measurable_id.prodMk measurable_const)
  have hDu : Measurable (fun η => stableDistinctMoment (rs.map Prod.fst) η z) :=
    (stableDistinctMoment_measurable (rs.map Prod.fst) m).comp (measurable_id.prodMk measurable_const)
  have h1 := mellin_weighted_identity _ hDm markedStableTotal_measurable
    ((markedStable_regular ν hb hb1).mono fun _ h => h.2) hq
  have h2 := mellin_weighted_identity _ hDu stablePoissonTotal_measurable (stablePoissonTotal_pos hb hb1) hq
  have hneg : -q = a-(rs.map Prod.fst).sum := by dsimp [q]; ring
  rw [hneg] at h1 h2
  apply (ENNReal.mul_left_inj hG0 ENNReal.ofReal_ne_top).mp
  rw [h1,mul_assoc,h2]
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal (t^(q-1))*
      (∫⁻ η, stableDistinctMoment (rs.map Prod.fst) η z*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
        ∂poissonRandomMeasureLaw (stableLogIntensity b))) := by
    apply (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t^(q-1)))).mul
    have hM : Measurable (fun p : ℝ × Measure ℝ => stableDistinctMoment (rs.map Prod.fst) p.2 z*
        ENNReal.ofReal (Real.exp (-p.1*stablePoissonTotal p.2))) := (hDu.comp measurable_snd).mul (by fun_prop)
    exact hM.lintegral_prod_right
  rw [← lintegral_const_mul _ hmeas]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [markedDistinctMoment_laplace_factor ν hb hb1 ht rs hr hm]
  ring

lemma markedStableTotal_momentE (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) :
    (∫⁻ η, ENNReal.ofReal (markedStableTotal η^a) ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
      ∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a) ∂poissonRandomMeasureLaw (stableLogIntensity b) := by
  rw [← markedStable_project_law ν b,
    lintegral_map (by fun_prop) (Measure.measurable_map _ measurable_fst)]
  simp only [markedStableTotal_projection]

omit [Nonempty S] in
lemma markedOrderedDistinctMass_measurable (rs : List (ℝ × (S → ℝ≥0∞)))
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    Measurable (fun η => markedOrderedDistinctMass rs η z) :=
  ((markedDistinctMoment_measurable rs hm m).comp (measurable_id.prodMk measurable_const)).mul (by fun_prop)

lemma markedOrderedDistinctMass_biased (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (rs : List (ℝ × (S → ℝ≥0∞)))
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedOrderedDistinctMass rs η z ∂markedTotalBiasedLaw ν a b) =
    (∫⁻ η, markedDistinctMoment rs η z*ENNReal.ofReal (markedStableTotal η^(a-(rs.map Prod.fst).sum))
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))/
      (∫⁻ η, ENNReal.ofReal (markedStableTotal η^a)
        ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) := by
  unfold markedTotalBiasedLaw normalizedMeasure
  rw [lintegral_smul_measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (markedOrderedDistinctMass_measurable rs hm z)]
  simp only [smul_eq_mul,Pi.mul_apply]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [markedStable_regular ν hb hb1] with η hη
  unfold markedOrderedDistinctMass
  calc
    _ = markedDistinctMoment rs η z*(ENNReal.ofReal (markedStableTotal η^a)*
      ENNReal.ofReal (markedStableTotal η^(-(rs.map Prod.fst).sum))) := by ring
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hη.2.le _),← Real.rpow_add hη.2,sub_eq_add_neg]

lemma markedOrderedDistinctMass_eppf (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (rs : List (ℝ × (S → ℝ≥0∞))) (hne : rs ≠ []) (hr : ∀ rf ∈ rs, b < rf.1)
    (hm : ∀ rf ∈ rs, Measurable rf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedOrderedDistinctMass rs η z ∂markedTotalBiasedLaw ν a b) =
      (rs.map (fun rf => ∫⁻ c, rf.2 c ∂ν)).prod*
      ENNReal.ofReal (Real.Gamma (1-a)/Real.Gamma ((rs.map Prod.fst).sum-a)*
        (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
        (rs.map (fun rf => Real.Gamma (rf.1-b)/Real.Gamma (1-b))).prod) := by
  rw [markedOrderedDistinctMass_biased ν hb hb1 rs hm z,
    markedDistinctMoment_mellin_factor ν hb hb1 ha rs hne hr hm,
    markedStableTotal_momentE ν a b,mul_div_assoc,stableDistinctMoment_eppf hb hb1 ha (rs.map Prod.fst)
      (by simpa using hne) (by intro r hr'; obtain ⟨rf,hmem,rfl⟩ := List.mem_map.mp hr'; exact hr rf hmem)]
  simp only [List.length_map,List.map_map,Function.comp_def]

omit [Nonempty S] in
lemma normalizedMeasure_map {A : Type*} [MeasurableSpace A] (μ : Measure S)
    {f : S → A} (hf : Measurable f) :
    (normalizedMeasure μ).map f = normalizedMeasure (μ.map f) := by
  simp only [normalizedMeasure,Measure.map_smul,
    Measure.map_apply hf MeasurableSet.univ,Set.preimage_univ]

omit [Nonempty S] in
lemma markedBlockProbability_measurable (ns : List (ℕ × (S → ℝ≥0∞)))
    (hm : ∀ nf ∈ ns, Measurable nf.2) (m : ℕ) :
    Measurable (fun p : Measure (ℝ × S) × (Fin m → ℝ) => markedBlockProbability ns p.1 p.2) := by
  induction ns generalizing m with
  | nil => exact measurable_const
  | cons nf ns ih =>
    let κ : Kernel (Measure (ℝ × S) × (Fin m → ℝ)) (ℝ × S) := markedStableMassKernel.comap
      (Prod.fst : Measure (ℝ × S) × (Fin m → ℝ) → Measure (ℝ × S)) measurable_fst
    have hD : Measurable (fun p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) =>
        markedBlockProbability ns p.1.1 (Fin.cons p.2.1 p.1.2)) := by
      exact (ih (fun r hr' => hm r (List.mem_cons_of_mem nf hr')) (m+1)).comp
        (measurable_fst.fst.prodMk (measurable_fin_cons measurable_snd.fst measurable_fst.snd))
    have ha : Measurable (fun p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) =>
        stableMassKernel (p.1.1.map Prod.fst) {p.2.1}) :=
      stableMassAtom_measurable_comp ((Measure.measurable_map _ measurable_fst).comp measurable_fst.fst) measurable_snd.fst
    have hset : MeasurableSet {p : (Measure (ℝ × S) × (Fin m → ℝ)) × (ℝ × S) | ∃ i, p.1.2 i = p.2.1} := by
      exact cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd.fst
    exact (measurable_const.ite hset (((ha.pow_const _).mul ((hm nf (by simp)).comp measurable_snd.snd)).mul hD)).lintegral_kernel_prod_right' (κ := κ)

omit [Nonempty S] in
lemma markedBlockProbability_moment (ns : List (ℕ × (S → ℝ≥0∞)))
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η)
    (hs : ∀ᵐ x ∂η.map Prod.fst, (η.map Prod.fst) {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    markedBlockProbability ns η z = markedDistinctMoment (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η z*
      ((ENNReal.ofReal (markedStableTotal η))⁻¹)^(ns.map Prod.fst).sum := by
  induction ns generalizing m with
  | nil => simp [markedBlockProbability,markedDistinctMoment]
  | cons nf ns ih =>
    have hn0 : 1 ≤ nf.1 := hn nf (by simp)
    have hn' : nf.1-1+1 = nf.1 := Nat.sub_add_cancel hn0
    have hns : ∀ k ∈ ns, 1 ≤ k.1 := fun k hk => hn k (by simp [hk])
    have hmt : ∀ k ∈ ns, Measurable k.2 := fun k hk => hm k (by simp [hk])
    have ha : Measurable (fun p : ℝ × S => stableMassKernel (η.map Prod.fst) {p.1}) :=
      stableMassAtom_measurable_comp measurable_const measurable_fst
    have hmeas : Measurable (fun p : ℝ × S => if ∃ i, z i = p.1 then (0:ℝ≥0∞) else
        (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*
          markedBlockProbability ns η (Fin.cons p.1 z)) := by
      exact measurable_const.ite (cascadeMeasurableSet_exists fun i =>
        measurableSet_eq_fun measurable_const measurable_fst)
        (((ha.pow_const _).mul ((hm nf (by simp)).comp measurable_snd)).mul
          ((markedBlockProbability_measurable ns hmt (m+1)).comp
            (measurable_const.prodMk (measurable_fin_cons measurable_fst measurable_const))))
    have htotal : (η.withDensity (fun p : ℝ × S => ENNReal.ofReal (Real.exp p.1))) univ =
        ENNReal.ofReal (markedStableTotal η) := by
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      exact (ENNReal.ofReal_toReal hf).symm
    unfold markedBlockProbability
    change (∫⁻ p, (if ∃ i, z i = p.1 then 0 else (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*
      markedBlockProbability ns η (Fin.cons p.1 z)) ∂normalizedMeasure
        (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)))) = _
    rw [normalizedMeasure,lintegral_smul_measure,htotal,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hmeas]
    simp only [smul_eq_mul,Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp))]
    have hpoint : (fun p : ℝ × S => (ENNReal.ofReal (markedStableTotal η))⁻¹ *
        (ENNReal.ofReal (Real.exp p.1)*(if ∃ i, z i = p.1 then 0 else
          (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*markedBlockProbability ns η (Fin.cons p.1 z)))) =ᵐ[η]
        (fun p : ℝ × S => (if ∃ i, z i = p.1 then 0 else ENNReal.ofReal (Real.exp ((nf.1:ℝ)*p.1))*nf.2 p.2*
          markedDistinctMoment (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η (Fin.cons p.1 z))*
          ((ENNReal.ofReal (markedStableTotal η))⁻¹)^(nf.1+(ns.map Prod.fst).sum)) := by
      filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hs] with p hx
      split_ifs
      · simp
      · rw [stableMassKernel_atom_eq (η.map Prod.fst) (by simpa [← markedStableTotalE_projection] using hf)
          (by simpa [← markedStableTotal_projection] using hp) hx,← markedStableTotal_projection,
          ENNReal.ofReal_div_of_pos hp,ih hns hmt (Fin.cons p.1 z),div_eq_mul_inv,mul_pow,
          Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_pos _).le,pow_add,← hn',pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
    rw [lintegral_congr_ae hpoint,lintegral_mul_const' _ _ (ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp)))]
    simp only [List.map_cons,List.sum_cons]
    rw [markedDistinctMoment,markedStableCountKernel_eq η hf hp]

omit [Nonempty S] in
lemma markedBlockProbability_ordered (ns : List (ℕ × (S → ℝ≥0∞)))
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) (η : Measure (ℝ × S))
    (hf : markedStableTotalE η ≠ ⊤) (hp : 0 < markedStableTotal η)
    (hs : ∀ᵐ x ∂η.map Prod.fst, (η.map Prod.fst) {x} = 1) {m : ℕ} (z : Fin m → ℝ) :
    markedBlockProbability ns η z = markedOrderedDistinctMass (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η z := by
  rw [markedBlockProbability_moment ns hn hm η hf hp hs]
  unfold markedOrderedDistinctMass
  congr 1
  rw [Real.rpow_neg hp.le,ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hp _)]
  have hsum : ((ns.map (fun nf => ((nf.1:ℝ),nf.2))).map Prod.fst).sum = ((ns.map Prod.fst).sum:ℝ) := by
    simpa only [List.map_map,Function.comp_def] using
      (Nat.cast_list_sum (R := ℝ) (ns.map Prod.fst)).symm
  rw [hsum,Real.rpow_natCast,ENNReal.ofReal_pow hp.le,ENNReal.inv_pow]

lemma markedTotalBiasedLaw_absolutelyContinuous (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) :
    markedTotalBiasedLaw ν a b ≪ poissonRandomMeasureLaw ((stableLogIntensity b).prod ν) := by
  exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

lemma markedBlockProbability_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (ns : List (ℕ × (S → ℝ≥0∞))) (hne : ns ≠ []) (hn : ∀ nf ∈ ns, 1 ≤ nf.1)
    (hm : ∀ nf ∈ ns, Measurable nf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedBlockProbability ns η z ∂markedTotalBiasedLaw ν a b) =
      (ns.map (fun nf => ∫⁻ c, nf.2 c ∂ν)).prod*
        (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η z ∂stableTotalBiasedLaw a b) := by
  have hr : ∀ rf ∈ ns.map (fun nf => ((nf.1:ℝ),nf.2)), b < rf.1 := by
    intro rf hr
    obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hr
    exact hb1.trans_le (by change (1:ℝ) ≤ (nf.1:ℝ); exact_mod_cast hn nf hmem)
  have hm' : ∀ rf ∈ ns.map (fun nf => ((nf.1:ℝ),nf.2)), Measurable rf.2 := by
    intro rf hr
    obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hr
    exact hm nf hmem
  have he := markedOrderedDistinctMass_eppf ν hb hb1 ha (ns.map (fun nf => ((nf.1:ℝ),nf.2)))
    (by simpa using hne) hr hm' z
  have hpres : MeasurePreserving (Measure.map (Prod.fst : ℝ × S → ℝ))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ measurable_fst,markedStable_project_law ν b⟩
  have hs := hpres.quasiMeasurePreserving.ae (stablePoissonCount_simple hb hb1)
  have hae : (fun η => markedBlockProbability ns η z) =ᵐ[markedTotalBiasedLaw ν a b]
      (fun η => markedOrderedDistinctMass (ns.map (fun nf => ((nf.1:ℝ),nf.2))) η z) := by
    apply (markedTotalBiasedLaw_absolutelyContinuous ν a b).ae_eq
    filter_upwards [markedStable_regular ν hb hb1,hs] with η hf hs
    exact markedBlockProbability_ordered ns hn hm η hf.1 hf.2 hs z
  rw [lintegral_congr_ae hae,he,stableBlockProbability_eppf hb hb1 ha (ns.map Prod.fst)
    (by simpa using hne) (by intro n hn'; obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hn'; exact hn nf hmem)]
  simp only [List.map_map,Function.comp_def,List.length_map]

omit [Nonempty S] in
lemma markedStableTotal_map_shift (η : Measure (ℝ × S)) {F : S → ℝ} (hF : Measurable F) :
    markedStableTotal (η.map (logMarkShift F)) = poissonWeightedTotal F η := by
  unfold markedStableTotal markedStableTotalE poissonWeightedTotal
  rw [lintegral_map (by fun_prop) (logMarkShift_measurable hF)]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedTotalBiasedLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cascadeShapeReplicas_fintype _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
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
section MarkedStable
variable {S : Type*} [MeasurableSpace S]
variable [Nonempty S]

lemma weightedTotalBiasedLaw_shift (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 ≤ b) {F : S → ℝ} (hF : Measurable F)
    [IsProbabilityMeasure (ν.withDensity (fun c => ENNReal.ofReal (Real.exp (b*F c))))] :
    (weightedTotalBiasedLaw ν a b F).map (Measure.map (logMarkShift F)) =
      markedTotalBiasedLaw (ν.withDensity (fun c => ENNReal.ofReal (Real.exp (b*F c)))) a b := by
  let Φ := Measure.map (logMarkShift F)
  have hΦ : Measurable Φ := Measure.measurable_map _ (logMarkShift_measurable hF)
  have hpow : Measurable (fun η : Measure (ℝ × S) => ENNReal.ofReal (markedStableTotal η^a)) := by fun_prop
  unfold weightedTotalBiasedLaw markedTotalBiasedLaw
  rw [normalizedMeasure_map _ hΦ]
  congr 1
  have hd := map_withDensity_comp (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) hΦ hpow
  dsimp [Function.comp_def,Φ] at hd
  simp_rw [markedStableTotal_map_shift _ hF] at hd
  rw [stablePoisson_mark_shift ν hb hF] at hd
  exact hd.symm

lemma weightedTotalBiasedLaw_add_const (ν : Measure S) [IsProbabilityMeasure ν]
    (a b : ℝ) {F : S → ℝ} (hF : Measurable F) (c : ℝ) :
    weightedTotalBiasedLaw ν a b (fun x => F x+c) = weightedTotalBiasedLaw ν a b F := by
  have hpw (η : Measure (ℝ × S)) : poissonWeightedTotal (fun x => F x+c) η^a =
      (Real.exp c)^a*(poissonWeightedTotal F η)^a := by
    rw [poissonWeightedTotal_add_const hF c η]
    exact Real.mul_rpow (Real.exp_pos c).le (show 0 ≤ poissonWeightedTotal F η from ENNReal.toReal_nonneg)
  unfold weightedTotalBiasedLaw
  simp_rw [hpw,ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos c).le a)]
  have he := withDensity_smul' (μ := poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
    (ENNReal.ofReal ((Real.exp c)^a)) (fun η => ENNReal.ofReal (poissonWeightedTotal F η^a)) ENNReal.ofReal_ne_top
  simp only [Pi.smul_def,smul_eq_mul] at he
  rw [he,normalizedMeasure_smul _
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos (Real.exp_pos c) a)) ENNReal.ofReal_ne_top]

omit [Nonempty S] in
lemma centeredLogMark_measurable (ν : Measure S) (b : ℝ) {X : S → ℝ} (hX : Measurable X) :
    Measurable (centeredLogMark ν b X) := hX.sub_const _

omit [Nonempty S] in
lemma exponentialMarkTilt_probability (ν : Measure S) [IsProbabilityMeasure ν]
    {b : ℝ} {X : S → ℝ} (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    IsProbabilityMeasure (exponentialMarkTilt ν b X) := by
  have hMpos := integral_exp_pos hI
  apply normalizedMeasure_probability
  all_goals rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => (Real.exp_pos _).le)]
  · exact ENNReal.ofReal_ne_zero_iff.mpr hMpos
  · exact ENNReal.ofReal_ne_top

omit [Nonempty S] in
lemma centeredLogMark_density (ν : Measure S) [IsProbabilityMeasure ν]
    {b : ℝ} (hb : b ≠ 0) {X : S → ℝ} (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*centeredLogMark ν b X x))) =
      exponentialMarkTilt ν b X := by
  let M := ∫ y, Real.exp (b*X y) ∂ν
  have hMpos : 0 < M := integral_exp_pos hI
  have hd (x : S) : ENNReal.ofReal (Real.exp (b*centeredLogMark ν b X x)) =
      (ENNReal.ofReal M)⁻¹*ENNReal.ofReal (Real.exp (b*X x)) := by
    unfold centeredLogMark
    rw [mul_sub,show b*(Real.log (∫ y, Real.exp (b*X y) ∂ν)/b) = Real.log M by dsimp [M]; field_simp,
      Real.exp_sub,Real.exp_log hMpos,ENNReal.ofReal_div_of_pos hMpos,div_eq_mul_inv,mul_comm]
  simp_rw [hd]
  have he := withDensity_smul' (μ := ν) (ENNReal.ofReal M)⁻¹
    (fun x => ENNReal.ofReal (Real.exp (b*X x)))
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hMpos))
  simp only [Pi.smul_def,smul_eq_mul] at he
  rw [he]
  unfold exponentialMarkTilt normalizedMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma weightedTotalBiasedLaw_centered (ν : Measure S) [IsProbabilityMeasure ν]
    (a b : ℝ) {X : S → ℝ} (hX : Measurable X) :
    weightedTotalBiasedLaw ν a b (centeredLogMark ν b X) = weightedTotalBiasedLaw ν a b X := by
  change weightedTotalBiasedLaw ν a b (fun x => X x-Real.log (∫ y, Real.exp (b*X y) ∂ν)/b) = _
  simpa only [sub_eq_add_neg] using
    weightedTotalBiasedLaw_add_const ν a b hX (-(Real.log (∫ y, Real.exp (b*X y) ∂ν)/b))

lemma weightedRootBlock_factor (ν : Measure S) [IsProbabilityMeasure ν]
    {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    {X : S → ℝ} (hX : Measurable X) (hI : Integrable (fun x => Real.exp (b*X x)) ν)
    (ns : List (ℕ × (S → ℝ≥0∞))) (hne : ns ≠ []) (hn : ∀ nf ∈ ns, 1 ≤ nf.1)
    (hm : ∀ nf ∈ ns, Measurable nf.2) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ η, markedBlockProbability ns (η.map (logMarkShift (centeredLogMark ν b X))) z
      ∂weightedTotalBiasedLaw ν a b X) =
      (ns.map (fun nf => ∫⁻ c, nf.2 c ∂exponentialMarkTilt ν b X)).prod*
        (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η z ∂stableTotalBiasedLaw a b) := by
  let F := centeredLogMark ν b X
  have hF : Measurable F := centeredLogMark_measurable ν b hX
  have : IsProbabilityMeasure (exponentialMarkTilt ν b X) := exponentialMarkTilt_probability ν hI
  have hd := centeredLogMark_density ν hb.ne' hI
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) := by
    simpa only [F,hd] using (exponentialMarkTilt_probability ν hI)
  have he := weightedTotalBiasedLaw_shift (a := a) ν hb.le hF
  rw [weightedTotalBiasedLaw_centered ν a b hX] at he
  have hD : Measurable (fun η : Measure (ℝ × S) => markedBlockProbability ns η z) :=
    (markedBlockProbability_measurable ns hm m).comp (measurable_id.prodMk measurable_const)
  rw [← lintegral_map hD (Measure.measurable_map _ (logMarkShift_measurable hF)),he,
    markedBlockProbability_factor _ hb hb1 ha ns hne hn hm]
  simp only [F,hd]

end MarkedStable

lemma cascadeLogTotalMoment_integrable (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : ∀ i, a < z i) :
    Integrable (fun η => Real.exp (a*Real.log (cascadeTotal n η)))
      (cascadeLaw n z : Measure (StableCascade n)) := by
  obtain ⟨hp,hi⟩ := cascadeTotal_regular n z hz hz0 hz1
  apply (hi a ha).congr
  filter_upwards [hp] with η hη
  rw [Real.rpow_def_of_pos hη,mul_comm]

lemma cascadeVisitCount_pos (n : ℕ) (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    1 ≤ cascadeVisitCount n s := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    obtain ⟨hne,hs⟩ := hs
    change (s.map (cascadeVisitCount n)).sum ≥ 1
    cases s with
    | nil => exact (hne rfl).elim
    | cons h t =>
      simp only [List.map_cons,List.sum_cons]
      have := ih h (hs h (by simp))
      omega

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

lemma stableBlockProbability_eppf_value {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (ns : List ℕ) (hne : ns ≠ []) (hn : ∀ n ∈ ns, 1 ≤ n) :
    (∫⁻ η, stableBlockProbability ns η (Fin.elim0 : Fin 0 → ℝ) ∂stableTotalBiasedLaw a b) =
      ENNReal.ofReal (stableEppfValue a b (ns.map (fun n : ℕ => (n:ℝ)))) := by
  simpa only [stableEppfValue,List.length_map,List.map_map,Function.comp_def] using
    stableBlockProbability_eppf hb hb1 ha ns hne hn (Fin.elim0 : Fin 0 → ℝ)

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

lemma markedStableCountKernel_ae_eq {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν), markedStableCountKernel η = η := by
  exact (markedStable_regular ν hb0 hb1).mono (fun η hη => markedStableCountKernel_eq η hη.1 hη.2)

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

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProductMarkLaw
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

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CascadeIndependentTilt
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
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedTiltedLeaves
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexedShiftSum_telescoping (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (H : X → ℝ) (p : X×IndexedCascadeMarks S n)
    (l : IndexedLeaf n) :
    indexedShiftSum step n (finiteCascadeShifts ν step n z H) p l =
      H (indexedLeafState step n p l)-finiteCascadeLogRecursion ν step n z H p.1 := by
  induction n with
  | zero => simp [indexedShiftSum,indexedLeafState,finiteCascadeLogRecursion]
  | succ n ih =>
    simp only [indexedShiftSum,finiteCascadeShifts,Fin.cases_zero,Fin.cases_succ]
    rw [ih]
    change _ = H (indexedLeafState step n (step (p.1,(p.2 l.1 l.2.1).1),
      (p.2 l.1 l.2.1).2) l.2.2)-_
    ring

lemma indexedLeafMeasure_shift_identity {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (m : IndexedCascadeMarks S n) (x : X) :
    decoratedWeightedTotalE step n F (x,indexedCascadeRealize n (b,m)) =
      ∫⁻ l, ENNReal.ofReal (Real.exp (indexedShiftSum step n F (x,m) l))
        ∂indexedLeafMeasure n b := by
  induction n generalizing x with
  | zero =>
    rw [indexedLeafMeasure_lintegral]
    simp [decoratedWeightedTotalE,indexedShiftSum,indexedLeafWeight,IndexedLeaf]
  | succ n ih =>
    rw [decoratedWeightedTotalE,indexedCascadeGood_countKernel hb]
    unfold indexedCascadeRealize
    dsimp only [Prod.fst,Prod.snd]
    have hm : Measurable (fun q : ℝ×(S×DecoratedCascade S n) =>
        ENNReal.ofReal (Real.exp (q.1+F 0 (x,q.2.1))) *
          decoratedWeightedTotalE step n (fun i => F i.succ) (step (x,q.2.1),q.2.2)) :=
      ((measurable_fst.add ((hF 0).comp (by fun_prop))).exp.ennreal_ofReal).mul
        ((decoratedWeightedTotalE_measurable step hs n _ (fun i => hF i.succ)).comp (by fun_prop))
    rw [indexedPoissonMeasure_lintegral _ hm,indexedLeafMeasure_lintegral_succ]
    apply tsum_congr
    intro i
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih _ (fun i => hF i.succ) _ (hb.2 i j.val) (m i j.val).2 (step (x,(m i j.val).1))]
    simp only [indexedShiftSum,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    exact mul_assoc _ _ _

lemma indexedTiltedLeafMeasure_normalized_terminal (ν : ProbabilityMeasure S)
    (step : X×S → X) (n : ℕ) (z : Fin n → ℝ) (H : X → ℝ)
    (x : X) (b : IndexedCascadeBase n) (m : IndexedCascadeMarks S n) :
    normalizedMeasure (indexedTiltedLeafMeasure step n (finiteCascadeShifts ν step n z H) x b m) =
      normalizedMeasure ((indexedLeafMeasure n b).withDensity (fun l =>
        ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))))) := by
  have he : indexedTiltedLeafMeasure step n (finiteCascadeShifts ν step n z H) x b m =
      ENNReal.ofReal (Real.exp (-finiteCascadeLogRecursion ν step n z H x)) •
        ((indexedLeafMeasure n b).withDensity (fun l =>
          ENNReal.ofReal (Real.exp (H (indexedLeafState step n (x,m) l))))) := by
    unfold indexedTiltedLeafMeasure
    rw [← withDensity_smul _ (measurable_of_countable _)]
    apply withDensity_congr_ae
    filter_upwards [] with l
    simp only [indexedShiftSum_telescoping,sub_eq_add_neg,Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_comm _ _
  rw [he,normalizedMeasure_smul _ (by positivity) ENNReal.ofReal_ne_top]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DecoratedTiltTotal
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

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [Nonempty S] in
lemma decoratedWeightedTotal_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (decoratedWeightedTotal step n F) := by
  have he : decoratedWeightedTotal step n F =
      fun p => cascadeTotal n (decoratedCascadeTransform step n F p) := by
    funext p; exact decoratedWeightedTotal_transform step hs n F hF p
  rw [he]
  exact (cascadeTotal_measurable n).comp (decoratedCascadeTransform_measurable step hs n F hF)

lemma decoratedWeightedTotal_pos (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)),
      0 < decoratedWeightedTotal step n F (x,η) :=
  (decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 F hF hI hM x).symm.ae_snd
    measurableSet_Ioi (cascadeTotal_regular n z hz hz0 hz1).1

lemma decoratedLogTotalMoment_integrable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (x : X) (a : ℝ) (ha : ∀ i, a < z i) :
    Integrable (fun η => Real.exp (a*Real.log (decoratedWeightedTotal step n F (x,η))))
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  have hid := (decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 F hF hI hM x).comp
    (Real.measurable_exp.comp (Real.measurable_log.const_mul a))
  exact hid.integrable_iff.mpr (cascadeLogTotalMoment_integrable n z hz hz0 hz1 a ha)

lemma decoratedLogTotalMoment_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (a : ℝ) :
    (∫ η, Real.exp (a*Real.log (decoratedWeightedTotal step n F (x,η)))
      ∂decoratedCascadeLaw ν n z) =
      ∫ η, Real.exp (a*Real.log (cascadeTotal n η)) ∂cascadeLaw n z := by
  exact ((decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 F hF hI hM x).comp
    (Real.measurable_exp.comp (Real.measurable_log.const_mul a))).integral_eq

lemma decoratedBiasedLaw_eq_exponentialTilt (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (a : ℝ) :
    decoratedBiasedLaw ν step n z F x a =
      exponentialMarkTilt (decoratedCascadeLaw ν n z) a
        (fun η => Real.log (decoratedWeightedTotal step n F (x,η))) := by
  unfold decoratedBiasedLaw exponentialMarkTilt
  congr 1
  apply withDensity_congr_ae
  filter_upwards [decoratedWeightedTotal_pos ν step hs n z hz hz0 hz1 F hF hI hM x] with η hη
  rw [Real.rpow_def_of_pos hη,mul_comm]

lemma decoratedBiasedLaw_probability (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (x : X) (a : ℝ) (ha : ∀ i, a < z i) :
    IsProbabilityMeasure (decoratedBiasedLaw ν step n z F x a) := by
  rw [decoratedBiasedLaw_eq_exponentialTilt ν step hs n z hz hz0 hz1 F hF hI hM x a]
  exact exponentialMarkTilt_probability _
    (decoratedLogTotalMoment_integrable ν step hs n z hz hz0 hz1 F hF hI hM x a ha)

omit [Nonempty S] in
lemma decoratedRootPotential_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (decoratedRootPotential step n F) :=
  ((hF 0).comp (measurable_fst.prodMk measurable_snd.fst)).add
    (((decoratedWeightedTotal_measurable step hs n _ (fun i => hF i.succ)).comp
      ((hs.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)).log)

lemma decoratedRootPotential_integrable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    Integrable (fun p => Real.exp (z 0*decoratedRootPotential step n F (x,p)))
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) := by
  let ρ : Measure (DecoratedCascade S n) := decoratedCascadeLaw ν n (fun i => z i.succ)
  let θ : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
  let T : S×DecoratedCascade S n → StableCascade n := fun p =>
    decoratedCascadeTransform step n (fun i => F i.succ) (step (x,p.1),p.2)
  have hT : Measurable T := (decoratedCascadeTransform_measurable step hs n _
    (fun i => hF i.succ)).comp
      ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have hLaw (s) : ρ.map (fun c => T (s,c)) = θ := by
    exact decoratedCascadeTransform_law ν step hs n (fun i => z i.succ)
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (fun i => F i.succ)
      (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ) (step (x,s))
  have hp : MeasurePreserving (fun p : S×DecoratedCascade S n => (p.1,T p))
      ((ν : Measure S).prod ρ) ((ν : Measure S).prod θ) :=
    ⟨measurable_fst.prodMk hT,descendant_transform_independent _ _ _ T hT hLaw⟩
  have htail := cascadeLogTotalMoment_integrable n (fun i => z i.succ)
    (fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)) (fun i => hz0 i.succ)
    (fun i => hz1 i.succ) (z 0) (fun i => hz (by simp))
  have hprod := (hI 0 x).mul_prod htail
  have he := (hp.integrable_comp hprod.aestronglyMeasurable).mpr hprod
  apply he.congr
  filter_upwards [] with p
  dsimp [Function.comp,T,decoratedRootPotential]
  rw [decoratedWeightedTotal_transform step hs n _ (fun i => hF i.succ),mul_add,Real.exp_add]

lemma decoratedWeightedTotal_succ_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν (n+1) z : Measure (DecoratedCascade S (n+1))),
      decoratedWeightedTotal step (n+1) F (x,η) =
        poissonWeightedTotal (fun p => decoratedRootPotential step n F (x,p)) η := by
  have hT : Measurable (fun η : DecoratedCascade S (n+1) =>
      decoratedCascadeTransform step (n+1) F (x,η)) :=
    (decoratedCascadeTransform_measurable step hs (n+1) F hF).comp
      (measurable_const.prodMk measurable_id)
  have hp : MeasurePreserving (fun η => decoratedCascadeTransform step (n+1) F (x,η))
      (decoratedCascadeLaw ν (n+1) z : Measure (DecoratedCascade S (n+1))) (cascadeLaw (n+1) z) :=
    ⟨hT,decoratedCascadeTransform_law ν step hs (n+1) z hz0 hz1 F hF hI hM x⟩
  have htail := (cascadeTotal_regular n (fun i => z i.succ)
    (fun i j h => hz (Fin.succ_lt_succ_iff.mpr h))
    (fun i => hz0 i.succ) (fun i => hz1 i.succ)).1
  have hae := hp.quasiMeasurePreserving.ae (cascadeTotal_succ_eq z htail)
  have hreg := markedStable_regular
    ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ) : Measure (DecoratedCascade S n))) (hz0 0) (hz1 0)
  filter_upwards [hae,hreg] with η hη hr
  rw [decoratedWeightedTotal_transform step hs (n+1) F hF,hη]
  change poissonWeightedTotal (fun C => Real.log (cascadeTotal n C))
    ((markedStableCountKernel η).map (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (x,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (x,q.2.1),q.2.2)))) = _
  rw [markedStableCountKernel_eq η hr.1 hr.2]
  have hmap : Measurable (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (x,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (x,q.2.1),q.2.2))) :=
    (measurable_fst.add ((hF 0).comp (measurable_const.prodMk measurable_snd.fst))).prodMk
      ((decoratedCascadeTransform_measurable step hs n _ (fun i => hF i.succ)).comp
        ((hs.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  unfold poissonWeightedTotal
  have hobs : Measurable (fun p : ℝ×StableCascade n =>
      ENNReal.ofReal (Real.exp (p.1+Real.log (cascadeTotal n p.2)))) :=
    (measurable_fst.add ((cascadeTotal_measurable n).comp measurable_snd).log).exp.ennreal_ofReal
  rw [lintegral_map hobs hmap]
  congr 1
  apply lintegral_congr
  intro q
  dsimp [decoratedRootPotential]
  rw [decoratedWeightedTotal_transform step hs n _ (fun i => hF i.succ),add_assoc]

lemma decoratedBiasedLaw_succ_eq_weighted (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (a : ℝ) :
    decoratedBiasedLaw ν step (n+1) z F x a = weightedTotalBiasedLaw
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) a (z 0)
      (fun p => decoratedRootPotential step n F (x,p)) := by
  unfold decoratedBiasedLaw weightedTotalBiasedLaw
  congr 1
  apply withDensity_congr_ae
  filter_upwards [decoratedWeightedTotal_succ_eq ν step hs n z hz hz0 hz1 F hF hI hM x] with η hη
  rw [hη]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedBlockParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cascadeShapeReplicas_fintype _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma markedBlockProbability_parameter_measurable {X S : Type*}
    [MeasurableSpace X] [MeasurableSpace S]
    (ns : List (ℕ × (X×S → ℝ≥0∞)))
    (hm : ∀ nf ∈ ns, Measurable nf.2) (m : ℕ) :
    Measurable (fun p : X×(Measure (ℝ×S)×(Fin m → ℝ)) =>
      markedBlockProbability (ns.map (fun nf => (nf.1,fun s => nf.2 (p.1,s))))
        p.2.1 p.2.2) := by
  induction ns generalizing m with
  | nil => exact measurable_const
  | cons nf ns ih =>
    let κ : Kernel (X×(Measure (ℝ×S)×(Fin m → ℝ))) (ℝ×S) :=
      markedStableMassKernel.comap (fun p => p.2.1) measurable_snd.fst
    have hD : Measurable (fun p : (X×(Measure (ℝ×S)×(Fin m → ℝ)))×(ℝ×S) =>
        markedBlockProbability (ns.map (fun nf => (nf.1,fun s => nf.2 (p.1.1,s))))
          p.1.2.1 (Fin.cons p.2.1 p.1.2.2)) := by
      exact (ih (fun r hr => hm r (List.mem_cons_of_mem nf hr)) (m+1)).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
          (measurable_fin_cons measurable_snd.fst measurable_fst.snd.snd)))
    have ha : Measurable (fun p : (X×(Measure (ℝ×S)×(Fin m → ℝ)))×(ℝ×S) =>
        stableMassKernel (p.1.2.1.map Prod.fst) {p.2.1}) :=
      stableMassAtom_measurable_comp
        ((Measure.measurable_map _ measurable_fst).comp measurable_fst.snd.fst)
        measurable_snd.fst
    have hset : MeasurableSet {p : (X×(Measure (ℝ×S)×(Fin m → ℝ)))×(ℝ×S) |
        ∃ i, p.1.2.2 i = p.2.1} :=
      cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd.fst
    simp only [List.map_cons,markedBlockProbability]
    exact (measurable_const.ite hset
      (((ha.pow_const (nf.1-1)).mul ((hm nf (by simp)).comp
        (measurable_fst.fst.prodMk measurable_snd.snd))).mul hD)).lintegral_kernel_prod_right' (κ := κ)

lemma DecoratedVisitShape.bare_valid {X : Type} [MeasurableSpace X]
    (n : ℕ) (s : DecoratedVisitShape X n) (hs : s.Valid n) :
    CascadeVisitShape.Valid n (s.bare n) := by
  induction n with
  | zero => exact hs.1
  | succ n ih =>
    exact ⟨by simpa [DecoratedVisitShape.bare] using hs.1,
      by intro t ht; obtain ⟨s',hm,rfl⟩ := List.mem_map.mp ht; exact ih s' (hs.2 s' hm)⟩

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma decoratedCenteredRoot_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (decoratedCenteredRoot ν step n z F) := by
  have hR := decoratedRootPotential_measurable step hs n F hF
  have hE : StronglyMeasurable (fun p : X×(S×DecoratedCascade S n) =>
      Real.exp (z 0*decoratedRootPotential step n F p)) :=
    (hR.const_mul _).exp.stronglyMeasurable
  have hM : Measurable (fun x => ∫ t : S×DecoratedCascade S n,
      Real.exp (z 0*decoratedRootPotential step n F (x,t))
      ∂((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))) :=
    (StronglyMeasurable.integral_prod_right
      (f := fun x t => Real.exp (z 0*decoratedRootPotential step n F (x,t))) hE).measurable
  exact hR.sub ((hM.comp measurable_fst).log.div_const _)

lemma decoratedShapeProbability_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (s : DecoratedVisitShape X n) (hs' : s.Valid n) :
    Measurable (decoratedShapeProbability ν step n z F s) := by
  induction n with
  | zero => exact hs'.2.comp measurable_fst
  | succ n ih =>
    let ns : List (ℕ×(X×(S×DecoratedCascade S n) → ℝ≥0∞)) :=
      s.map (fun t => (cascadeVisitCount n (t.bare n),fun p =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) t
          (step (p.1,p.2.1),p.2.2)))
    have hm : ∀ nf ∈ ns, Measurable nf.2 := by
      intro nf hnf; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hnf
      exact (ih (fun i => z i.succ) (fun i => F i.succ) (fun i => hF i.succ) t
        (hs'.2 t ht)).comp
        ((hs.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
    have hmap := countKernel_parameter_map_measurable
      (fun p : X×(ℝ×(S×DecoratedCascade S n)) =>
        (p.2.1+decoratedCenteredRoot ν step n z F (p.1,p.2.2),p.2.2))
      ((measurable_snd.fst.add ((decoratedCenteredRoot_measurable ν step hs n z F hF).comp
        (measurable_fst.prodMk measurable_snd.snd))).prodMk measurable_snd.snd)
    have hh := (markedBlockProbability_parameter_measurable ns hm 0).comp
      (measurable_fst.prodMk (hmap.prodMk (measurable_const (a := (Fin.elim0 : Fin 0 → ℝ)))))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [decoratedShapeProbability,ns,List.map_map,Function.comp_def]

omit [Nonempty S] in
lemma decoratedShapeMarkValue_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (s : DecoratedVisitShape X n) (hs' : s.Valid n) :
    Measurable (decoratedShapeMarkValue ν step n z F s) := by
  induction n with
  | zero => exact hs'.2
  | succ n ih =>
    have hterm (t : DecoratedVisitShape X n) (ht : t ∈ s) :
        Measurable (fun x => ∫⁻ u, ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
          decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
            t (step (x,u)) ∂ν) := by
      have h : Measurable (fun p : X×S => ENNReal.ofReal (Real.exp (z 0*F 0 p))*
          decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
            t (step p)) :=
        ((hF 0).const_mul _).exp.ennreal_ofReal.mul
          ((ih _ _ (fun i => hF i.succ) t (hs'.2 t ht)).comp hs)
      exact h.lintegral_prod_right
    change Measurable (fun x => (s.map (fun t => ∫⁻ u,
      ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
        decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
          t (step (x,u)) ∂ν)).prod)
    clear hs' ih
    induction s with
    | nil => exact measurable_const
    | cons t ts iht =>
      simp only [List.map_cons,List.prod_cons]
      exact (hterm t (by simp)).mul (iht (fun u hu => hterm u (by simp [hu])))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedTiltedWeights
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

section
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexedTiltedTotal_eq {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (hb : IndexedCascadeGood n p.2.1) :
    indexedTiltedTotal step n F p =
      decoratedWeightedTotalE step n F (p.1,indexedCascadeRealize n p.2) := by
  rw [indexedLeafMeasure_shift_identity hs n F hF p.2.1 hb p.2.2 p.1,
    indexedLeafMeasure_lintegral]
  rfl

omit [MeasurableSpace X] in
lemma indexedTiltedProbability_lintegral (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (f : IndexedLeaf n → ℝ≥0∞) :
    (∫⁻ l, f l ∂normalizedMeasure (indexedTiltedLeafMeasure step n F p.1 p.2.1 p.2.2)) =
      ∑' l, indexedTiltedProbability step n F p l*f l := by
  rw [normalizedMeasure,lintegral_smul_measure,smul_eq_mul,indexedTiltedLeafMeasure,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) (measurable_of_countable _),
    indexedLeafMeasure_lintegral,indexedLeafMeasure_lintegral,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  change (∑' l, (indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
    ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l)))⁻¹ *
      ((indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
        (ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l))*f l)) = _
  simp only [indexedTiltedProbability,indexedTiltedTotal,indexedTiltedWeight,mul_assoc]

omit [MeasurableSpace X] in
lemma indexedTiltedWeight_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (i j : ℕ) (l : IndexedLeaf n) :
    indexedTiltedWeight step (n+1) F p (i,j,l) =
      if j < (p.2.1 i).1 then ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
        indexedTiltedWeight step n (fun a => F a.succ)
          (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l else 0 := by
  by_cases hj : j<(p.2.1 i).1
  · simp only [indexedTiltedWeight,indexedLeafWeight,indexedShiftSum,ite_eq_left hj,
      ENNReal.coe_mul,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    change (ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1))*_)*(_*_) = _
    ac_rfl
  · simp [indexedTiltedWeight,indexedLeafWeight,indexedShiftSum,hj]

omit [MeasurableSpace X] in
lemma indexedTiltedWeight_tsum_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (f : IndexedLeaf (n+1) → ℝ≥0∞) :
    (∑' l, indexedTiltedWeight step (n+1) F p l*f l) =
      ∑' i, ∑ j : Fin ((p.2.1 i).1),
        ENNReal.ofReal (Real.exp (((p.2.1 i).2 j.val).1+F 0 (p.1,(p.2.2 i j.val).1)))*
          ∑' l, indexedTiltedWeight step n (fun a => F a.succ)
            (step (p.1,(p.2.2 i j.val).1),(((p.2.1 i).2 j.val).2,(p.2.2 i j.val).2)) l * f (i,j.val,l) := by
  change (∑' l : ℕ×ℕ×IndexedLeaf n, _) = _
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro i
  rw [ENNReal.tsum_prod']
  simp_rw [indexedTiltedWeight_succ]
  have he (j : ℕ) : (∑' l : IndexedLeaf n,
      (if j<(p.2.1 i).1 then ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
        indexedTiltedWeight step n (fun a => F a.succ)
          (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l else 0)*f (i,j,l)) =
      if j<(p.2.1 i).1 then ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
        ∑' l, indexedTiltedWeight step n (fun a => F a.succ)
          (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l*f (i,j,l) else 0 := by
    split_ifs with h
    · simp_rw [mul_assoc,ENNReal.tsum_mul_left]
    · simp
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range ((p.2.1 i).1)) (fun j hj => by simp [Finset.mem_range.not.mp hj])]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    ENNReal.ofReal (Real.exp (((p.2.1 i).2 j).1+F 0 (p.1,(p.2.2 i j).1)))*
      ∑' l, indexedTiltedWeight step n (fun a => F a.succ)
        (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2)) l * f (i,j,l))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (Finset.mem_range.mp hj)]

omit [MeasurableSpace X] in
lemma indexedTiltedTotal_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1))) :
    indexedTiltedTotal step (n+1) F p =
      ∑' i, ∑ j : Fin ((p.2.1 i).1),
        ENNReal.ofReal (Real.exp (((p.2.1 i).2 j.val).1+F 0 (p.1,(p.2.2 i j.val).1)))*
          indexedTiltedTotal step n (fun a => F a.succ)
            (step (p.1,(p.2.2 i j.val).1),(((p.2.1 i).2 j.val).2,(p.2.2 i j.val).2)) := by
  simpa only [mul_one,indexedTiltedTotal] using indexedTiltedWeight_tsum_succ step n F p (fun _ => 1)

end
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedBranchWeight_tsum (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1))) :
    (∑' a, indexedBranchWeight step n F p a) = indexedTiltedTotal step (n+1) F p := by
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype,indexedBranchWeight,indexedChildPoint]
  exact (indexedTiltedTotal_succ step n F p).symm

lemma indexedRootPoint_weight (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (a : Σ i, Fin ((p.2.1 i).1)) :
    ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p a).1) =
      ENNReal.ofReal (Real.exp (-(Real.log (∫ t : S×DecoratedCascade S n,
        Real.exp (z 0*decoratedRootPotential step n F (p.1,t))
        ∂((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))))/z 0)))*
          indexedBranchWeight step n F p a := by
  have he := indexedTiltedTotal_eq hs n (fun i => F i.succ) (fun i => hF i.succ)
    (indexedChildPoint step n p a.1 a.2.val) (hb.2 a.1 a.2.val)
  dsimp only [indexedChildPoint] at he
  have hpos := hc a.1 a.2.val
  have hfinite := (ENNReal.toReal_pos_iff.mp hpos).2.ne
  simp only [indexedRootPoint,decoratedCenteredRoot,centeredLogMark,decoratedRootPotential,
    decoratedWeightedTotal,← he,indexedBranchWeight]
  let A := (((p.2.1 a.1).2 a.2.val).1)
  let B := F 0 (p.1,(p.2.2 a.1 a.2.val).1)
  let C := Real.log (∫ t : S×DecoratedCascade S n,
    Real.exp (z 0*decoratedRootPotential step n F (p.1,t))
      ∂((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))) / z 0
  let T := indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val)
  change ENNReal.ofReal (Real.exp (A + (B + Real.log T.toReal - C))) =
    ENNReal.ofReal (Real.exp (-C))*(ENNReal.ofReal (Real.exp (A+B))*T)
  rw [show A+(B+Real.log T.toReal-C) = -C+((A+B)+Real.log T.toReal) by ring,
    Real.exp_add,Real.exp_add,Real.exp_log hpos,
    ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_toReal hfinite]

lemma indexedRootPoint_probability (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (a : Σ i, Fin ((p.2.1 i).1)) :
    ((∑' b, ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p b).1))⁻¹)*
      ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p a).1) =
        indexedBranchProbability step n F p a := by
  simp_rw [indexedRootPoint_weight ν step hs n z F hF p hb hc,
    ENNReal.tsum_mul_left,indexedBranchWeight_tsum]
  rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
    (Or.inl ENNReal.ofReal_ne_top)]
  simp only [indexedBranchProbability]
  rw [mul_mul_mul_comm,ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
    ENNReal.ofReal_ne_top,one_mul]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedReplicaWeights
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedLeaf_tsum_active (n : ℕ) (b : IndexedCascadeBase (n+1))
    (f : IndexedLeaf (n+1) → ℝ≥0∞)
    (hf : ∀ i j, ¬j<(b i).1 → ∀ l : IndexedLeaf n, f (i,j,l)=0) :
    (∑' l, f l) = ∑' a : Σ i, Fin ((b i).1), ∑' l : IndexedLeaf n, f (a.1,a.2.val,l) := by
  change (∑' l : ℕ×ℕ×IndexedLeaf n, f l) = _
  rw [ENNReal.tsum_prod',ENNReal.tsum_sigma']
  apply tsum_congr
  intro i
  rw [ENNReal.tsum_prod']
  conv_rhs => rw [tsum_fintype]
  rw [tsum_eq_sum (s := Finset.range ((b i).1)) (fun j hj => by
    simp only [hf i j (Finset.mem_range.not.mp hj),tsum_zero])]
  exact (Fin.sum_univ_eq_sum_range (fun j => ∑' l : IndexedLeaf n, f (i,j,l)) _).symm

variable {X S : Type} [MeasurableSpace S]

lemma indexedTiltedProbability_active (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1))
    (hc : 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p a.1 a.2.val)).toReal) (l : IndexedLeaf n) :
    indexedTiltedProbability step (n+1) F p (a.1,a.2.val,l) =
      indexedBranchProbability step n F p a * indexedTiltedProbability step n (fun i => F i.succ)
        (indexedChildPoint step n p a.1 a.2.val) l := by
  rw [indexedTiltedProbability,indexedTiltedWeight_succ,ite_eq_left a.2.isLt]
  simp only [indexedBranchProbability,indexedBranchWeight,indexedTiltedProbability]
  rw [show (indexedTiltedTotal step (n+1) F p)⁻¹ *
      (ENNReal.ofReal (Real.exp (((p.2.1 a.1).2 a.2.val).1+F 0 (p.1,(p.2.2 a.1 a.2.val).1)))*
        indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val)) *
      ((indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val))⁻¹ *
        indexedTiltedWeight step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val) l) =
      (indexedTiltedTotal step (n+1) F p)⁻¹ *
      (ENNReal.ofReal (Real.exp (((p.2.1 a.1).2 a.2.val).1+F 0 (p.1,(p.2.2 a.1 a.2.val).1)))*
        ((indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val))*
          (indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val))⁻¹)*
        indexedTiltedWeight step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val) l) by ac_rfl,
    ENNReal.mul_inv_cancel (ENNReal.toReal_pos_iff.mp hc).1.ne' (ENNReal.toReal_pos_iff.mp hc).2.ne,
    mul_one]
  rfl

lemma indexedTiltedProbability_inactive (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (i j : ℕ) (hj : ¬j<(p.2.1 i).1) (l : IndexedLeaf n) :
    indexedTiltedProbability step (n+1) F p (i,j,l) = 0 := by
  simp [indexedTiltedProbability,indexedTiltedWeight_succ,hj]

lemma indexedTiltedProbability_tsum_succ (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) (f : IndexedLeaf (n+1) → ℝ≥0∞) :
    (∑' l, indexedTiltedProbability step (n+1) F p l*f l) =
      ∑' a : Σ i, Fin ((p.2.1 i).1), indexedBranchProbability step n F p a *
        ∑' l, indexedTiltedProbability step n (fun i => F i.succ)
          (indexedChildPoint step n p a.1 a.2.val) l * f (a.1,a.2.val,l) := by
  rw [indexedLeaf_tsum_active n p.2.1 _ (by
    intro i j hj l; rw [indexedTiltedProbability_inactive step n F p i j hj l,zero_mul])]
  apply tsum_congr
  intro a
  simp_rw [indexedTiltedProbability_active step n F p a (hc a.1 a.2.val),mul_assoc,ENNReal.tsum_mul_left]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedVertices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkTiltKernel
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

lemma normalized_product_tilt_lintegral {S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [SFinite ν] [SFinite ρ]
    {f : S → ℝ≥0∞} {g : S×T → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcf : c ≠ ⊤)
    (hrow : ∀ s, (∫⁻ t, g (s,t) ∂ρ) = c)
    {H : S×T → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H p ∂normalizedMeasure ((ν.prod ρ).withDensity (fun p => f p.1*g p))) =
    ∫⁻ s, (∫⁻ t, H (s,t) ∂normalizedMeasure (ρ.withDensity (fun t => g (s,t))))
      ∂normalizedMeasure (ν.withDensity f) := by
  have hfg : Measurable (fun p : S×T => f p.1*g p) := (hf.comp measurable_fst).mul hg
  have hgh : Measurable (fun p : S×T => g p*H p) := hg.mul hH
  have hfgH : Measurable (fun p : S×T => (f p.1*g p)*H p) := hfg.mul hH
  have hgs (s : S) : Measurable (fun t => g (s,t)) := hg.comp (measurable_const.prodMk measurable_id)
  have hHs (s : S) : Measurable (fun t => H (s,t)) := hH.comp (measurable_const.prodMk measurable_id)
  have hmass : ((ν.prod ρ).withDensity (fun p => f p.1*g p)) univ =
      (ν.withDensity f) univ*c := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      lintegral_prod _ hfg.aemeasurable]
    simp_rw [lintegral_const_mul _ (hgs _),hrow]
    rw [lintegral_mul_const _ hf,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hi (s : S) : (∫⁻ t, H (s,t) ∂normalizedMeasure (ρ.withDensity (fun t => g (s,t)))) =
      c⁻¹ * ∫⁻ t, g (s,t)*H (s,t) ∂ρ := by
    rw [normalizedMeasure,lintegral_smul_measure,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hrow,
      lintegral_withDensity_eq_lintegral_mul ρ
        (hgs s) (hHs s)]
    rfl
  have hJ : Measurable (fun s => ∫⁻ t, g (s,t)*H (s,t) ∂ρ) :=
    (hg.mul hH).lintegral_prod_right
  simp_rw [hi]
  rw [normalizedMeasure,lintegral_smul_measure,hmass,
    lintegral_withDensity_eq_lintegral_mul _ hfg hH]
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ hfgH.aemeasurable,
    normalizedMeasure,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hf (hJ.const_mul _)]
  simp only [smul_eq_mul,Pi.mul_apply]
  have hinner (s : S) : (∫⁻ t, f s*(g (s,t)*H (s,t)) ∂ρ) =
      f s*(∫⁻ t, g (s,t)*H (s,t) ∂ρ) :=
    lintegral_const_mul (f s) (hgs s |>.mul (hHs s))
  simp_rw [mul_assoc,hinner]
  rw [ENNReal.mul_inv (Or.inr hcf) (Or.inr hc0)]
  simp_rw [← mul_assoc, mul_right_comm (f _) c⁻¹]
  have hfj : Measurable (fun s => f s * ∫⁻ t, g (s,t)*H (s,t) ∂ρ) := hf.mul hJ
  rw [lintegral_mul_const _ hfj]
  ac_rfl

lemma exponential_product_tilt_lintegral {S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [SFinite ν] [SFinite ρ]
    {f : S → ℝ} {g : S×T → ℝ}
    (hf : Measurable f) (hg : Measurable g) (b : ℝ) {c : ℝ}
    (hc : 0 < c)
    (hI : ∀ s, Integrable (fun t => Real.exp (b*g (s,t))) ρ)
    (hrow : ∀ s, (∫ t, Real.exp (b*g (s,t)) ∂ρ) = c)
    {H : S×T → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H p ∂exponentialMarkTilt (ν.prod ρ) b (fun p => f p.1+g p)) =
    ∫⁻ s, (∫⁻ t, H (s,t) ∂exponentialMarkTilt ρ b (fun t => g (s,t)))
      ∂exponentialMarkTilt ν b f := by
  have he (p : S×T) : ENNReal.ofReal (Real.exp (b*(f p.1+g p))) =
      ENNReal.ofReal (Real.exp (b*f p.1))*ENNReal.ofReal (Real.exp (b*g p)) := by
    rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold exponentialMarkTilt
  simp_rw [he]
  apply normalized_product_tilt_lintegral ν ρ
    (hf.const_mul b |>.exp.ennreal_ofReal) (hg.const_mul b |>.exp.ennreal_ofReal)
    (c := ENNReal.ofReal c) (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top
  · intro s
    rw [← ofReal_integral_eq_lintegral_ofReal (hI s)
      (ae_of_all _ fun t => (Real.exp_pos _).le),hrow s]
  · exact hH

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma decoratedBiasedLaw_absolutelyContinuous (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ) (x : X) (a : ℝ) :
    decoratedBiasedLaw ν step n z F x a ≪ (decoratedCascadeLaw ν n z) :=
  Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

lemma decoratedRootTilt_disintegrate (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X)
    (H : S×DecoratedCascade S n → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p, H p ∂exponentialMarkTilt
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) (z 0)
      (fun p => decoratedRootPotential step n F (x,p))) =
    ∫⁻ s, (∫⁻ C, H (s,C) ∂decoratedBiasedLaw ν step n
      (fun i => z i.succ) (fun i => F i.succ) (step (x,s)) (z 0))
      ∂exponentialMarkTilt ν (z 0) (fun s => F 0 (x,s)) := by
  have htail : StrictMono (fun i : Fin n => z i.succ) :=
    fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
  have hrange : ∀ i : Fin n, z 0 < z i.succ := fun i => hz (by simp)
  have hC := cascadeLogTotalMoment_integrable n (fun i => z i.succ) htail
    (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) hrange
  have hG : Measurable (fun p : S×DecoratedCascade S n =>
      Real.log (decoratedWeightedTotal step n (fun i => F i.succ) (step (x,p.1),p.2))) :=
    ((decoratedWeightedTotal_measurable step hs n _ (fun i => hF i.succ)).comp
      ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)).log
  have he := exponential_product_tilt_lintegral (ν : Measure S)
    (decoratedCascadeLaw ν n (fun i => z i.succ) : Measure (DecoratedCascade S n))
    ((hF 0).comp ((measurable_const (a := x)).prodMk measurable_id)) hG (z 0)
    (integral_exp_pos hC)
    (fun s => decoratedLogTotalMoment_integrable ν step hs n (fun i => z i.succ)
      htail (fun i => hz0 i.succ) (fun i => hz1 i.succ) (fun i => F i.succ)
      (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ)
      (step (x,s)) (z 0) hrange)
    (fun s => decoratedLogTotalMoment_eq ν step hs n (fun i => z i.succ)
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (fun i => F i.succ)
      (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ)
      (step (x,s)) (z 0)) hH
  have hb (s : S) := decoratedBiasedLaw_eq_exponentialTilt ν step hs n
    (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
    (fun i => F i.succ) (fun i => hF i.succ) (fun i => hI i.succ)
    (fun i => hM i.succ) (step (x,s)) (z 0)
  simp_rw [hb]
  exact he

lemma decoratedRootBlock_factor (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X)
    (a : ℝ) (ha : a < z 0)
    (ns : List (ℕ×(S×DecoratedCascade S n → ℝ≥0∞))) (hne : ns ≠ [])
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) :
    (∫⁻ η, markedBlockProbability ns
      ((markedStableCountKernel η).map (logMarkShift
        (centeredLogMark ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))
          (z 0) (fun p => decoratedRootPotential step n F (x,p))))) (Fin.elim0 : Fin 0 → ℝ)
      ∂decoratedBiasedLaw ν step (n+1) z F x a) =
    (ns.map (fun nf => ∫⁻ s, (∫⁻ C, nf.2 (s,C) ∂decoratedBiasedLaw ν step n
      (fun i => z i.succ) (fun i => F i.succ) (step (x,s)) (z 0))
        ∂exponentialMarkTilt ν (z 0) (fun s => F 0 (x,s)))).prod *
      (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η (Fin.elim0 : Fin 0 → ℝ)
        ∂stableTotalBiasedLaw a (z 0)) := by
  have hreg := (decoratedBiasedLaw_absolutelyContinuous ν step (n+1) z F x a).ae_eq
    (markedStableCountKernel_ae_eq
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ) : Measure (DecoratedCascade S n)))
      (hz0 0) (hz1 0))
  let G : Measure (ℝ×(S×DecoratedCascade S n)) → ℝ≥0∞ := fun η =>
    markedBlockProbability ns (η.map (logMarkShift (centeredLogMark
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) (z 0)
      (fun p => decoratedRootPotential step n F (x,p))))) (Fin.elim0 : Fin 0 → ℝ)
  have he := lintegral_congr_ae (hreg.mono (fun η hη => congrArg G hη))
  dsimp [G] at he
  have hR : Measurable (fun p : S×DecoratedCascade S n =>
      decoratedRootPotential step n F (x,p)) :=
    (decoratedRootPotential_measurable step hs n F hF).comp
      (measurable_const.prodMk measurable_id)
  rw [he,decoratedBiasedLaw_succ_eq_weighted ν step hs n z hz hz0 hz1 F hF hI hM x a,
    weightedRootBlock_factor _ (hz0 0) (hz1 0) ha
      hR
      (decoratedRootPotential_integrable ν step hs n z hz hz0 hz1 F hF hI hM x) ns hne hn hm]
  congr 2
  apply List.map_congr_left
  intro nf hnf
  exact decoratedRootTilt_disintegrate ν step hs n z hz hz0 hz1 F hF hI hM x nf.2 (hm nf hnf)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DecoratedShapeLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cascadeShapeReplicas_fintype _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
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

lemma exponentialMarkTilt_eq_density_of_one {S : Type*} [MeasurableSpace S]
    (ν : Measure S) {b : ℝ} {F : S → ℝ}
    (hI : Integrable (fun s => Real.exp (b*F s)) ν)
    (hM : (∫ s, Real.exp (b*F s) ∂ν) = 1) :
    exponentialMarkTilt ν b F = ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s))) := by
  unfold exponentialMarkTilt normalizedMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun s => (Real.exp_pos _).le),hM]
  simp

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

theorem decoratedShapeProbability_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (a : ℝ) (ha : ∀ i, a < z i) (s : DecoratedVisitShape X n)
    (hv : s.Valid n) (x : X) :
    (∫⁻ η, decoratedShapeProbability ν step n z F s (x,η)
      ∂decoratedBiasedLaw ν step n z F x a) =
      cascadeShapeLikelihood n z a (s.bare n)*decoratedShapeMarkValue ν step n z F s x := by
  induction n generalizing a x with
  | zero =>
    have := decoratedBiasedLaw_probability ν step hs 0 z hz hz0 hz1 F hF hI hM x a ha
    simp only [decoratedShapeProbability,cascadeShapeLikelihood,decoratedShapeMarkValue,
      lintegral_const,measure_univ,mul_one,one_mul]
  | succ n ih =>
    have htail : StrictMono (fun i : Fin n => z i.succ) :=
      fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
    have hrange : ∀ i : Fin n, z 0 < z i.succ := fun i => hz (by simp)
    let ns : List (ℕ×(S×DecoratedCascade S n → ℝ≥0∞)) := s.map (fun t =>
      (cascadeVisitCount n (t.bare n),fun p =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) t
          (step (x,p.1),p.2)))
    have hne : ns ≠ [] := by simpa [ns] using hv.1
    have hn : ∀ nf ∈ ns, 1 ≤ nf.1 := by
      intro nf hnf; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hnf
      exact cascadeVisitCount_pos n _ (t.bare_valid n (hv.2 t ht))
    have hm : ∀ nf ∈ ns, Measurable nf.2 := by
      intro nf hnf; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hnf
      exact (decoratedShapeProbability_measurable ν step hs n (fun i => z i.succ)
        (fun i => F i.succ) (fun i => hF i.succ) t (hv.2 t ht)).comp
        ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have he := decoratedRootBlock_factor ν step hs n z hz hz0 hz1 F hF hI hM x a
      (ha 0) ns hne hn hm
    change (∫⁻ η, markedBlockProbability ns
      ((markedStableCountKernel η).map (logMarkShift
        (centeredLogMark ((ν : Measure S).prod
          (decoratedCascadeLaw ν n (fun i => z i.succ))) (z 0)
          (fun p => decoratedRootPotential step n F (x,p)))))
      (Fin.elim0 : Fin 0 → ℝ) ∂decoratedBiasedLaw ν step (n+1) z F x a) = _
    rw [he,stableBlockProbability_eppf_value (hz0 0) (hz1 0) (ha 0)
      (ns.map Prod.fst) (by simpa using hne)
      (by intro k hk; obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hk; exact hn nf hmem)]
    have hchild (t : DecoratedVisitShape X n) (ht : t ∈ s) :
        (∫⁻ u, (∫⁻ C, decoratedShapeProbability ν step n (fun i => z i.succ)
          (fun i => F i.succ) t (step (x,u),C) ∂decoratedBiasedLaw ν step n
          (fun i => z i.succ) (fun i => F i.succ) (step (x,u)) (z 0))
            ∂exponentialMarkTilt ν (z 0) (fun u => F 0 (x,u))) =
        cascadeShapeLikelihood n (fun i => z i.succ) (z 0) (t.bare n)*
          ∫⁻ u, ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
            decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
              t (step (x,u)) ∂ν := by
      have hval : Measurable (fun u => decoratedShapeMarkValue ν step n
          (fun i => z i.succ) (fun i => F i.succ) t (step (x,u))) :=
        (decoratedShapeMarkValue_measurable ν step hs n (fun i => z i.succ)
          (fun i => F i.succ) (fun i => hF i.succ) t (hv.2 t ht)).comp
          (hs.comp (measurable_const.prodMk measurable_id))
      calc
        _ = ∫⁻ u, cascadeShapeLikelihood n (fun i => z i.succ) (z 0) (t.bare n)*
            decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
              t (step (x,u)) ∂exponentialMarkTilt ν (z 0) (fun u => F 0 (x,u)) := by
          apply lintegral_congr
          intro u
          exact ih (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
            (fun i => F i.succ) (fun i => hF i.succ) (fun i => hI i.succ)
            (fun i => hM i.succ) (z 0) hrange t (hv.2 t ht) (step (x,u))
        _ = _ := by
          have hweight : Measurable (fun u : S => ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))) :=
            (((hF 0).comp (measurable_const.prodMk measurable_id)).const_mul _).exp.ennreal_ofReal
          rw [lintegral_const_mul _ hval,
            exponentialMarkTilt_eq_density_of_one (ν : Measure S) (b := z 0)
              (F := fun u => F 0 (x,u)) (hI 0 x) (hM 0 x),
            lintegral_withDensity_eq_lintegral_mul _ hweight hval]
          rfl
    simp only [ns,List.map_map,Function.comp_def] at *
    rw [show (s.map (fun t => ∫⁻ u, (∫⁻ C, decoratedShapeProbability ν step n
      (fun i => z i.succ) (fun i => F i.succ) t (step (x,u),C)
        ∂decoratedBiasedLaw ν step n (fun i => z i.succ) (fun i => F i.succ)
          (step (x,u)) (z 0)) ∂exponentialMarkTilt ν (z 0) (fun u => F 0 (x,u)))) =
      s.map (fun t => cascadeShapeLikelihood n (fun i => z i.succ) (z 0) (t.bare n)*
        ∫⁻ u, ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
          decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
            t (step (x,u)) ∂ν) by exact List.map_congr_left hchild]
    rw [List.prod_map_mul]
    simp only [cascadeShapeLikelihood,DecoratedVisitShape.bare,decoratedShapeMarkValue,
      List.map_map,Function.comp_def]
    ac_rfl

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedChildLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedCascadeMarks_child_law {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (n : ℕ) (i j : ℕ) :
    MeasurePreserving (fun m : IndexedCascadeMarks S (n+1) => m i j)
      (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1)))
      ((ν : Measure S).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ =>
    (ν : Measure S).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) j).comp
      (measurePreserving_eval_infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        (ν : Measure S).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) i)

lemma indexedCascade_joint_child_law {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (n : ℕ) (z : Fin (n+1) → ℝ) (i j : ℕ) :
    MeasurePreserving (fun p : IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1) =>
      ((p.2 i j).1,(((p.1 i).2 j).2,(p.2 i j).2)))
      ((indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
        (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))))
      ((ν : Measure S).prod ((indexedCascadeBaseLaw n (fun l => z l.succ) :
        Measure (IndexedCascadeBase n)).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) := by
  let B : Measure (IndexedCascadeBase n) := indexedCascadeBaseLaw n (fun l => z l.succ)
  let M : Measure (IndexedCascadeMarks S n) := indexedCascadeMarksLaw ν n
  have hr : MeasurePreserving (fun p : IndexedCascadeBase n×(S×IndexedCascadeMarks S n) =>
      (p.2.1,(p.1,p.2.2))) (B.prod ((ν : Measure S).prod M)) ((ν : Measure S).prod (B.prod M)) :=
    ⟨by fun_prop,prod_rotate_front B (ν : Measure S) M⟩
  exact hr.comp ((indexedCascadeBase_child_law n z i j).prod
    (indexedCascadeMarks_child_law ν n i j))

lemma indexedCascade_ae_children {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin (n+1) → ℝ) (P : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) → Prop)
    (hP : MeasurableSet {p | P p})
    (h : ∀ x, ∀ᵐ p ∂(indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)), P (x,p)) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
      (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))), ∀ i j,
        P (step (x,(p.2 i j).1),(((p.1 i).2 j).2,(p.2 i j).2)) := by
  have hprod : ∀ᵐ p ∂(ν : Measure S).prod
      ((indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))), P (step (x,p.1),p.2) :=
    (Measure.ae_prod_iff_ae_ae (hP.preimage (by fun_prop))).mpr
      (ae_of_all _ fun s => h (step (x,s)))
  exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    (indexedCascade_joint_child_law ν n z i j).quasiMeasurePreserving.ae hprod

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AtomicBranches
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma injective_of_simple_count_map {I A : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : I → A) (hp : Measurable p)
    (hs : ∀ᵐ x ∂(Measure.count.map p), (Measure.count.map p) {x} = 1) :
    Function.Injective p := by
  classical
  have h : ∀ i, (Measure.count.map p) {p i} = 1 :=
    Measure.ae_count_iff.mp (ae_of_ae_map hp.aemeasurable hs)
  intro i j hij
  by_contra hn
  have hle : (Measure.count : Measure I) {i,j} ≤ 1 := by
    rw [← h i,Measure.map_apply hp (measurableSet_singleton _)]
    apply measure_mono
    intro k hk
    rcases hk with rfl | hk
    · rfl
    · simpa only [mem_singleton_iff] using hk ▸ hij.symm
  have htwo : (Measure.count : Measure I) {i,j} = 2 := by
    have he : (↑({i,j} : Finset I) : Set I) = {i,j} := by ext k; simp
    rw [← he,Measure.count_apply_finset]
    simp [hn]
  rw [htwo] at hle
  norm_num at hle

lemma markedStableMassKernel_count_map {I S : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace S]
    (p : I → ℝ×S) (hp : Measurable p) :
    markedStableMassKernel (Measure.count.map p) =
      (normalizedMeasure (Measure.count.withDensity
        (fun i => ENNReal.ofReal (Real.exp (p i).1)))).map p := by
  rw [normalizedMeasure_map _ hp]
  change normalizedMeasure ((Measure.count.map p).withDensity
    (fun t : ℝ×S => ENNReal.ofReal (Real.exp t.1))) = _
  rw [map_withDensity_comp Measure.count hp (by fun_prop)]
  rfl

lemma stableMassKernel_count_map_atom {I S : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace S]
    (p : I → ℝ×S) (hp : Measurable p) (hinj : Function.Injective (fun i => (p i).1))
    (i : I) :
    stableMassKernel ((Measure.count.map p).map Prod.fst) {(p i).1} =
      ((∑' j, ENNReal.ofReal (Real.exp (p j).1))⁻¹) *
        ENNReal.ofReal (Real.exp (p i).1) := by
  rw [Measure.map_map measurable_fst hp]
  change normalizedMeasure ((Measure.count.map (fun j => (p j).1)).withDensity
    (fun x => ENNReal.ofReal (Real.exp x))) {(p i).1} = _
  have hp' : Measurable (fun j => (p j).1) := hp.fst
  rw [map_withDensity_comp Measure.count hp' (by fun_prop),
    ← normalizedMeasure_map _ hp',
    Measure.map_apply hp' (measurableSet_singleton _)]
  have hpre : (fun j => (p j).1) ⁻¹' {(p i).1} = {i} := by
    ext j
    simp only [mem_preimage,mem_singleton_iff,hinj.eq_iff]
  rw [hpre,normalizedMeasure,Measure.smul_apply,smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton i),withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,lintegral_count]
  simp

lemma markedBlockProbability_count_map {I S : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace S]
    (p : I → ℝ×S) (hp : Measurable p) (hinj : Function.Injective (fun i => (p i).1))
    (ns : List (ℕ×(S → ℝ≥0∞)))
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2)
    {m : ℕ} (z : Fin m → ℝ) :
    markedBlockProbability ns (Measure.count.map p) z = countedBlockProbability p ns z := by
  classical
  induction ns generalizing m with
  | nil => rfl
  | cons nf ns ih =>
    have hnf := hn nf (by simp)
    have hn' : ∀ n ∈ ns, 1 ≤ n.1 := fun n h => hn n (by simp [h])
    have hm' : ∀ n ∈ ns, Measurable n.2 := fun n h => hm n (by simp [h])
    unfold markedBlockProbability countedBlockProbability
    rw [markedStableMassKernel_count_map p hp]
    have ha : Measurable (fun t : ℝ×S =>
        stableMassKernel ((Measure.count.map p).map Prod.fst) {t.1}) :=
      stableMassAtom_measurable_comp measurable_const measurable_fst
    have ht : Measurable (fun t : ℝ×S =>
        markedBlockProbability ns (Measure.count.map p) (Fin.cons t.1 z)) :=
      (markedBlockProbability_measurable ns hm' (m+1)).comp
        (measurable_const.prodMk (measurable_fin_cons measurable_fst measurable_const))
    have hf : Measurable (fun t : ℝ×S => if ∃ j, z j = t.1 then (0:ℝ≥0∞) else
        (stableMassKernel ((Measure.count.map p).map Prod.fst) {t.1})^(nf.1-1)*
          nf.2 t.2*markedBlockProbability ns (Measure.count.map p) (Fin.cons t.1 z)) :=
      measurable_const.ite (cascadeMeasurableSet_exists fun j =>
        measurableSet_eq_fun measurable_const measurable_fst)
        (((ha.pow_const _).mul ((hm nf (by simp)).comp measurable_snd)).mul ht)
    have hweight : Measurable (fun i => ENNReal.ofReal (Real.exp (p i).1)) :=
      hp.fst.exp.ennreal_ofReal
    have hfp : Measurable (fun i => if ∃ j, z j = (p i).1 then (0:ℝ≥0∞) else
        (stableMassKernel ((Measure.count.map p).map Prod.fst) {(p i).1})^(nf.1-1)*
          nf.2 (p i).2*markedBlockProbability ns (Measure.count.map p) (Fin.cons (p i).1 z)) :=
      hf.comp hp
    rw [lintegral_map hf hp,normalizedMeasure,lintegral_smul_measure,smul_eq_mul,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      lintegral_withDensity_eq_lintegral_mul _ hweight hfp,
      lintegral_count,lintegral_count,← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro i
    simp only [Pi.mul_apply]
    split_ifs with hi
    · simp
    · rw [stableMassKernel_count_map_atom p hp hinj,ih hn' hm']
      have hpw := pow_succ (((∑' k, ENNReal.ofReal (Real.exp (p k).1))⁻¹)*
        ENNReal.ofReal (Real.exp (p i).1)) (nf.1-1)
      rw [Nat.sub_add_cancel hnf] at hpw
      rw [hpw]
      ring

lemma indexedPoissonMeasure_eq_map_count {A : Type*} [MeasurableSpace A]
    (a : ℕ → ℕ×(ℕ → A)) :
    indexedPoissonMeasure a = Measure.count.map
      (fun i : Σ j, Fin ((a j).1) => (a i.1).2 i.2.val) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [indexedPoissonMeasure_lintegral a hf,
    lintegral_map hf (measurable_of_countable _),lintegral_count,ENNReal.tsum_sigma']
  simp only [tsum_fintype]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedTiltedRegular
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma indexedTiltedTotal_regular (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
       0 < (indexedTiltedTotal step n F (x,p)).toReal := by
  have hR : MeasurePreserving (indexedCascadeRealize (S := S) n)
      ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) :=
    ⟨indexedCascadeRealize_measurable n,indexedCascadeRealize_law ν n z⟩
  have hp := hR.quasiMeasurePreserving.ae
    (decoratedWeightedTotal_pos ν step hs n z hz hz0 hz1 F hF hI hM x)
  have hg := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
    (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae
      (indexedCascadeGood_ae n z hz0 hz1)
  filter_upwards [hp,hg] with p hp hg
  rwa [indexedTiltedTotal_eq hs n F hF (x,p) hg]

lemma centeredMarkedPoisson_simple (ν : Measure S) [IsProbabilityMeasure ν]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun s => Real.exp (b*F s)) ν) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν),
      ∀ᵐ t ∂((η.map (logMarkShift (centeredLogMark ν b F))).map Prod.fst),
        ((η.map (logMarkShift (centeredLogMark ν b F))).map Prod.fst) {t} = 1 := by
  let τ := exponentialMarkTilt ν b F
  have : IsProbabilityMeasure τ := exponentialMarkTilt_probability ν hI
  have hc : Measurable (centeredLogMark ν b F) := centeredLogMark_measurable ν b hF
  have ht : MeasurePreserving (Measure.map (logMarkShift (centeredLogMark ν b F)))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod τ)) := by
    refine ⟨Measure.measurable_map _ (logMarkShift_measurable hc), ?_⟩
    rw [stablePoisson_mark_shift ν hb.le hc]
    congr 1
    exact congrArg ((stableLogIntensity b).prod) (centeredLogMark_density ν hb.ne' hI)
  have hp : MeasurePreserving (Measure.map (Prod.fst : ℝ×S → ℝ))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod τ))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ measurable_fst,markedStable_project_law τ b⟩
  exact (hp.comp ht).quasiMeasurePreserving.ae (stablePoissonCount_simple hb hb1)

lemma indexedCenteredRoot_simple (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
      (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))),
      Function.Injective (fun a : Σ i, Fin ((p.1 i).1) =>
        (((p.1 a.1).2 a.2.val).1 + decoratedCenteredRoot ν step n z F
          (x,((p.2 a.1 a.2.val).1,indexedCascadeRealize n
            ((((p.1 a.1).2 a.2.val).2,(p.2 a.1 a.2.val).2)))))) := by
  let D := ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ) :
    Measure (DecoratedCascade S n)))
  have hR : MeasurePreserving (indexedCascadeRealize (S := S) (n+1))
      ((indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
        (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))))
      (decoratedCascadeLaw ν (n+1) z : Measure (DecoratedCascade S (n+1))) :=
    ⟨indexedCascadeRealize_measurable (n+1),indexedCascadeRealize_law ν (n+1) z⟩
  have hpot : Measurable (fun t => decoratedRootPotential step n F (x,t)) :=
    (decoratedRootPotential_measurable step hs n F hF).comp (measurable_const.prodMk measurable_id)
  have he := centeredMarkedPoisson_simple D (hz0 0) (hz1 0) hpot
    (decoratedRootPotential_integrable ν step hs n z hz hz0 hz1 F hF hI hM x)
  have hae := hR.quasiMeasurePreserving.ae he
  filter_upwards [hae] with p hp
  let a : ℕ → ℕ×(ℕ → ℝ×(S×DecoratedCascade S n)) := fun i => ((p.1 i).1,fun j =>
      (((p.1 i).2 j).1,((p.2 i j).1,indexedCascadeRealize n ((((p.1 i).2 j).2,(p.2 i j).2)))))
  let f : (Σ i, Fin ((p.1 i).1)) → ℝ := fun q => ((a q.1).2 q.2.val).1 +
    decoratedCenteredRoot ν step n z F (x,((a q.1).2 q.2.val).2)
  have hmap : (((indexedCascadeRealize (n+1) p).map
      (logMarkShift (centeredLogMark D (z 0) (fun t => decoratedRootPotential step n F (x,t))))).map
        Prod.fst) = Measure.count.map f := by
    change ((indexedPoissonMeasure a).map _).map _ = _
    rw [indexedPoissonMeasure_eq_map_count,
      Measure.map_map (logMarkShift_measurable (centeredLogMark_measurable D (z 0) hpot))
          (measurable_of_countable _),
      Measure.map_map measurable_fst (measurable_of_countable _)]
    rfl
  rw [hmap] at hp
  exact injective_of_simple_count_map f (measurable_of_countable _) hp

lemma indexedShapeRoot_counted (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (ss : List (DecoratedVisitShape X n)) (hv : ∀ s ∈ ss, s.Valid n) :
    decoratedShapeProbability ν step (n+1) z F ss (p.1,indexedCascadeRealize (n+1) p.2) =
      countedBlockProbability (indexedRootPoint ν step n z F p)
        (ss.map (fun s => (cascadeVisitCount n (s.bare n),fun t : S×DecoratedCascade S n =>
          decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
            (step (p.1,t.1),t.2)))) (Fin.elim0 : Fin 0 → ℝ) := by
  rw [decoratedShapeProbability,indexedCascadeGood_countKernel hb]
  have hc : Measurable (fun t : ℝ×(S×DecoratedCascade S n) =>
      (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2)) :=
    (measurable_fst.add ((decoratedCenteredRoot_measurable ν step hs n z F hF).comp
      (measurable_const.prodMk measurable_snd))).prodMk measurable_snd
  have he : (indexedCascadeRealize (n+1) p.2).map
      (fun t : ℝ×(S×DecoratedCascade S n) =>
        (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2)) =
      Measure.count.map (indexedRootPoint ν step n z F p) := by
    unfold indexedCascadeRealize
    rw [indexedPoissonMeasure_eq_map_count,Measure.map_map hc (measurable_of_countable _)]
    rfl
  rw [he]
  apply markedBlockProbability_count_map _ (measurable_of_countable _) hj
  · intro nf hnf
    obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hnf
    exact cascadeVisitCount_pos n _ (s.bare_valid n (hv s hs'))
  · intro nf hnf
    obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hnf
    exact (decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) s (hv s hs')).comp
      ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)

lemma indexedShapeRoot_singleton (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (s : DecoratedVisitShape X n) (hv : s.Valid n) :
    decoratedShapeProbability ν step (n+1) z F [s] (p.1,indexedCascadeRealize (n+1) p.2) =
      ∑' a, (indexedBranchProbability step n F p a)^(cascadeVisitCount n (s.bare n))*
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
          ((indexedChildPoint step n p a.1 a.2.val).1,
            indexedCascadeRealize n (indexedChildPoint step n p a.1 a.2.val).2) := by
  rw [indexedShapeRoot_counted ν step hs n z F hF p hb hj [s] (by simpa using hv)]
  simp only [List.map_cons,List.map_nil,countedBlockProbability,Fin.exists_fin_zero,
    ite_false,mul_one,indexedRootPoint_probability ν step hs n z F hF p hb hc]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedVisit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cascadeShapeReplicas_fintype _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

section

lemma oneDecoratedVisit_valid {X : Type} [MeasurableSpace X] {h : X → ℝ≥0∞}
    (hh : Measurable h) (n : ℕ) : (oneDecoratedVisit h n).Valid n := by
  induction n with
  | zero => exact ⟨le_rfl,hh⟩
  | succ n ih => exact ⟨by simp [oneDecoratedVisit],by simpa [oneDecoratedVisit] using ih⟩

lemma oneDecoratedVisit_count {X : Type} (h : X → ℝ≥0∞) (n : ℕ) :
    cascadeVisitCount n ((oneDecoratedVisit h n).bare n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [oneDecoratedVisit,DecoratedVisitShape.bare,cascadeVisitCount] using ih

lemma oneDecoratedVisit_likelihood {X : Type} (h : X → ℝ≥0∞) (n : ℕ)
    (z : Fin n → ℝ) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : a < 1) :
    cascadeShapeLikelihood n z a ((oneDecoratedVisit h n).bare n) = 1 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [oneDecoratedVisit,DecoratedVisitShape.bare,List.map_cons,List.map_nil,
      cascadeShapeLikelihood,List.prod_cons,List.prod_nil,mul_one]
    rw [ih (fun i => z i.succ) (fun i => hz1 i.succ) (z 0) (hz1 0)]
    simp only [oneDecoratedVisit_count,Nat.cast_one,stableEppfValue_singleton_one ha (hz1 0),
      ENNReal.ofReal_one,one_mul]

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [Nonempty S] in
lemma indexedOneVisit_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    {h : X → ℝ≥0∞} (hh : Measurable h) : Measurable (indexedOneVisit step n F h) := by
  apply Measurable.tsum
  intro l
  exact ((indexedTiltedProbability_measurable hs n F hF).comp (measurable_id.prodMk measurable_const)).mul
    (hh.comp ((indexedLeafState_measurable hs n).comp (show Measurable
      (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) => ((p.1,p.2.2),l)) from by fun_prop)))

omit [Nonempty S] in
lemma indexedOneVisit_zero (step : X×S → X) (F : Fin 0 → X×S → ℝ)
    (h : X → ℝ≥0∞) (p : X×(IndexedCascadeBase 0×IndexedCascadeMarks S 0)) :
    indexedOneVisit step 0 F h p = h p.1 := by
  simp [indexedOneVisit,indexedTiltedProbability,indexedTiltedTotal,indexedTiltedWeight,
    indexedLeafWeight,indexedLeafState,indexedShiftSum,IndexedLeaf]

omit [Nonempty S] in
lemma indexedOneVisit_succ (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (h : X → ℝ≥0∞) (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) :
    indexedOneVisit step (n+1) F h p =
      ∑' a, indexedBranchProbability step n F p a * indexedOneVisit step n (fun i => F i.succ) h
        (indexedChildPoint step n p a.1 a.2.val) := by
  rw [indexedOneVisit,indexedTiltedProbability_tsum_succ step n F p hc]
  rfl

lemma indexedOneVisit_eq_shape (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
      indexedOneVisit step n F h (x,p) =
        decoratedShapeProbability ν step n z F (oneDecoratedVisit h n) (x,indexedCascadeRealize n p) := by
  induction n generalizing x with
  | zero => exact ae_of_all _ fun p => indexedOneVisit_zero step F h (x,p)
  | succ n ih =>
    have hzt : StrictMono (fun i : Fin n => z i.succ) := fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
    have he := indexedCascade_ae_children ν step hs n z
      (fun p => indexedOneVisit step n (fun i => F i.succ) h p =
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
          (oneDecoratedVisit h n) (p.1,indexedCascadeRealize n p.2))
      (measurableSet_eq_fun (indexedOneVisit_measurable hs n _ (fun i => hF i.succ) hh)
        ((decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) _
          (oneDecoratedVisit_valid hh n)).comp
          (measurable_fst.prodMk ((indexedCascadeRealize_measurable n).comp measurable_snd))))
      (fun y => ih _ hzt (fun i => hz0 i.succ) (fun i => hz1 i.succ) _ (fun i => hF i.succ)
        (fun i => hI i.succ) (fun i => hM i.succ) y) x
    have hc := indexedCascade_ae_children ν step hs n z
      (fun p => 0 < (indexedTiltedTotal step n (fun i => F i.succ) p).toReal)
      (measurableSet_lt measurable_const ((indexedTiltedTotal_measurable hs n _ (fun i => hF i.succ)).ennreal_toReal))
      (fun y => indexedTiltedTotal_regular ν step hs n _ hzt (fun i => hz0 i.succ) (fun i => hz1 i.succ)
        _ (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ) y) x
    have hj := indexedCenteredRoot_simple ν step hs n z hz hz0 hz1 F hF hI hM x
    have hb := (measurePreserving_fst
      (μ := (indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))))
      (ν := (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))))).quasiMeasurePreserving.ae
        (indexedCascadeGood_ae (n+1) z hz0 hz1)
    filter_upwards [he,hc,hj,hb] with p he hc hj hb
    rw [indexedOneVisit_succ step n F h (x,p) hc,oneDecoratedVisit,
      indexedShapeRoot_singleton ν step hs n z F hF (x,p) hb hc hj _ (oneDecoratedVisit_valid hh n),
      oneDecoratedVisit_count]
    simp only [pow_one]
    apply tsum_congr
    intro a
    exact congrArg (fun t => indexedBranchProbability step n F (x,p) a * t)
      (he a.1 a.2.val)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedTwoShape
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma decoratedBiasedLaw_zero (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ) (x : X) :
    decoratedBiasedLaw ν step n z F x 0 =
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  simp [decoratedBiasedLaw,normalizedMeasure]

lemma indexedShapeProbability_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (v : DecoratedVisitShape X n) (hv : v.Valid n) (x : X) :
    (∫⁻ p, decoratedShapeProbability ν step n z F v (x,indexedCascadeRealize n p)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      cascadeShapeLikelihood n z 0 (v.bare n)*decoratedShapeMarkValue ν step n z F v x := by
  have hm : Measurable (fun η : DecoratedCascade S n =>
      decoratedShapeProbability ν step n z F v (x,η)) :=
    (decoratedShapeProbability_measurable ν step hs n z F hF v hv).comp
    (show Measurable (fun η : DecoratedCascade S n => (x,η)) from by fun_prop)
  rw [← lintegral_map hm (indexedCascadeRealize_measurable n),indexedCascadeRealize_law ν n z,
    ← decoratedBiasedLaw_zero ν step n z F x]
  exact decoratedShapeProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM 0 hz0 v hv x

lemma indexedOneVisit_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    (∫⁻ p, indexedOneVisit step n F h (x,p)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      decoratedShapeMarkValue ν step n z F (oneDecoratedVisit h n) x := by
  rw [lintegral_congr_ae (indexedOneVisit_eq_shape ν step hs n z hz hz0 hz1 F hF hI hM h hh x),
    indexedShapeProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM _ (oneDecoratedVisit_valid hh n) x,
    oneDecoratedVisit_likelihood h n z hz1 0 zero_lt_one,one_mul]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedVisitKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma tiltedMarkKernel_markov (ν : ProbabilityMeasure S) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedMarkKernel ν z F) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [tiltedMarkKernel,Kernel.withDensity_apply _ ((hF.const_mul z).exp.ennreal_ofReal)]
  simp only [Kernel.const_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI x)
    (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)),hM x]
  exact ENNReal.ofReal_one

lemma tiltedStateStep_markov (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedStateStep ν step z F) := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  exact Kernel.IsMarkovKernel.map _ hs

lemma tiltedStateStep_lintegral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    (∫⁻ y, h y ∂tiltedStateStep ν step z F x) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (z*F (x,s)))*h (step (x,s)) ∂ν := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  rw [tiltedStateStep,Kernel.lintegral_map _ hs _ hh,
    Kernel.lintegral_id_prod (show Measurable (fun p : X×S => h (step p)) from hh.comp hs)]
  exact Kernel.lintegral_withDensity _ ((hF.const_mul z).exp.ennreal_ofReal) x
    ((hh.comp hs).comp (measurable_const.prodMk measurable_id))

lemma pathOneKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) : IsMarkovKernel (pathOneKernel n κ) := by
  induction n with
  | zero => dsimp [pathOneKernel]; infer_instance
  | succ n ih =>
    have := hκ 0
    have := ih (fun i => κ i.succ) (fun i => hκ i.succ)
    dsimp [pathOneKernel]; infer_instance

lemma path_bounded_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

lemma pathMean_succ (n : ℕ) (κ : Fin (n+1) → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) (x : X) :
    pathMean (n+1) κ f x = ∫ y, pathMean n (fun i => κ i.succ) f y ∂κ 0 x := by
  have := hκ 0
  have := pathOneKernel_markov n (fun i => κ i.succ) (fun i => hκ i.succ)
  exact Kernel.integral_comp (path_bounded_integrable _ f hf C hb)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedVisitKernelLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [Nonempty S] in
lemma pathOneKernel_lintegral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    (∫⁻ y, h y ∂pathOneKernel n (fun i => tiltedStateStep ν step (z i) (F i)) x) =
      decoratedShapeMarkValue ν step n z F (oneDecoratedVisit h n) x := by
  induction n generalizing x with
  | zero =>
    simp only [pathOneKernel,Kernel.id_apply,decoratedShapeMarkValue,oneDecoratedVisit]
    exact lintegral_dirac' _ hh
  | succ n ih =>
    rw [pathOneKernel,Kernel.lintegral_comp _ _ _ hh]
    simp_rw [ih (fun i => z i.succ) (fun i => F i.succ) (fun i => hF i.succ)
      (fun i => hI i.succ) (fun i => hM i.succ)]
    rw [tiltedStateStep_lintegral ν step hs (z 0) (F 0) (hF 0) (hI 0) (hM 0) _
      (decoratedShapeMarkValue_measurable ν step hs n _ _ (fun i => hF i.succ) _
        (oneDecoratedVisit_valid hh n))]
    simp [decoratedShapeMarkValue,oneDecoratedVisit]

section
variable {P Y I : Type} [MeasurableSpace P] [MeasurableSpace Y] [Countable I]

lemma atomicVisitKernel_lintegral (q : I → P → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    (s : I → P → Y) (hs : ∀ i, Measurable (s i)) (h : Y → ℝ≥0∞) (hh : Measurable h) (p : P) :
    (∫⁻ y, h y ∂atomicVisitKernel q hq s hs p) = ∑' i, q i p*h (s i p) := by
  change (∫⁻ y, h y ∂Measure.sum (fun i => q i p • Measure.dirac (s i p))) = _
  rw [lintegral_sum_measure]
  simp_rw [lintegral_smul_measure,smul_eq_mul,lintegral_dirac' _ hh]

lemma atomicVisitKernel_finite (q : I → P → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    (s : I → P → Y) (hs : ∀ i, Measurable (s i)) (hb : ∀ p, (∑' i, q i p) ≤ 1) :
    IsFiniteKernel (atomicVisitKernel q hq s hs) := by
  refine ⟨1,ENNReal.one_lt_top,fun p => ?_⟩
  change Measure.sum (fun i => q i p • Measure.dirac (s i p)) univ ≤ 1
  simpa [Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply] using hb p

end

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedTiltedProbability_mass_le (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) :
    (∑' l, indexedTiltedProbability step n F p l) ≤ 1 := by
  simp only [indexedTiltedProbability,ENNReal.tsum_mul_left]
  exact ENNReal.inv_mul_le_one _

omit [Nonempty S] in
instance indexedOneStateKernel_finite (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) :
    IsFiniteKernel (indexedOneStateKernel step hs n F hF x) :=
  atomicVisitKernel_finite _ _ _ _ (fun p => indexedTiltedProbability_mass_le step n F (x,p))

omit [Nonempty S] in
lemma indexedOneStateKernel_lintegral (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X)
    (h : X → ℝ≥0∞) (hh : Measurable h) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    (∫⁻ y, h y ∂indexedOneStateKernel step hs n F hF x p) = indexedOneVisit step n F h (x,p) :=
  atomicVisitKernel_lintegral _ _ _ _ h hh p

lemma indexedOneStateLaw_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    indexedOneStateKernel step hs n F hF x ∘ₘ
      ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      pathOneKernel n (fun i => tiltedStateStep ν step (z i) (F i)) x := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [Measure.comp_eq_comp_const_apply,Kernel.lintegral_comp _ _ _ hh]
  simp_rw [indexedOneStateKernel_lintegral step hs n F hF x h hh,Kernel.const_apply]
  rw [indexedOneVisit_integral ν step hs n z hz hz0 hz1 F hF hI hM h hh x,
    pathOneKernel_lintegral ν step hs n z F hF hI hM h hh x]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedTerminalGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma tiltLaw_eq_normalized_exp {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (H : A→ℝ)
    (hi : Integrable (fun x => Real.exp (H x)) μ) :
    tiltLaw μ H 1 = normalizedMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) := by
  unfold tiltLaw normalizedMeasure tiltPartition
  simp only [one_mul]
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexed_terminal_tiltLaw (ν : ProbabilityMeasure S) (step : X×S→X)
    (n : ℕ) (z : Fin n→ℝ) (H : X→ℝ) (x : X) (b : IndexedCascadeBase n)
    (m : IndexedCascadeMarks S n) (hb : 0<((indexedLeafMeasure n b) univ).toReal)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,m) l)))
      (indexedLeafProbability n b)) :
    tiltLaw (indexedLeafProbability n b) (fun l => H (indexedLeafState step n (x,m) l)) 1 =
      normalizedMeasure (indexedTiltedLeafMeasure step n (finiteCascadeShifts ν step n z H) x b m) := by
  rw [indexedTiltedLeafMeasure_normalized_terminal,tiltLaw_eq_normalized_exp _ _ hi,
    indexedLeafProbability,ite_eq_left hb,withDensity_smul_measure]
  apply normalizedMeasure_smul
  · exact ENNReal.inv_ne_zero.mpr (ENNReal.toReal_pos_iff.mp hb).2.ne
  · exact ENNReal.inv_ne_top.mpr (ENNReal.toReal_pos_iff.mp hb).1.ne'

lemma indexed_terminal_lintegral (ν : ProbabilityMeasure S) (step : X×S→X)
    (n : ℕ) (z : Fin n→ℝ) (H : X→ℝ) (x : X) (b : IndexedCascadeBase n)
    (m : IndexedCascadeMarks S n) (hb : 0<((indexedLeafMeasure n b) univ).toReal)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,m) l)))
      (indexedLeafProbability n b)) (f : IndexedLeaf n→ℝ≥0∞) :
    (∫⁻ l, f l ∂tiltLaw (indexedLeafProbability n b)
      (fun l => H (indexedLeafState step n (x,m) l)) 1) =
      ∑' l, indexedTiltedProbability step n (finiteCascadeShifts ν step n z H) (x,(b,m)) l*f l := by
  rw [indexed_terminal_tiltLaw ν step n z H x b m hb hi]
  exact indexedTiltedProbability_lintegral step n (finiteCascadeShifts ν step n z H) (x,(b,m)) f

variable [Nonempty S]

omit [Nonempty S] in
lemma indexed_terminal_oneState (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (z : Fin n→ℝ) (H : X→ℝ) (hH : Measurable H) (x : X) (b : IndexedCascadeBase n)
    (m : IndexedCascadeMarks S n) (hb : 0<((indexedLeafMeasure n b) univ).toReal)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,m) l)))
      (indexedLeafProbability n b)) :
    (tiltLaw (indexedLeafProbability n b) (fun l => H (indexedLeafState step n (x,m) l)) 1).map
      (indexedLeafState step n (x,m)) =
      indexedOneStateKernel step hs n (finiteCascadeShifts ν step n z H)
        (finiteCascadeShifts_measurable ν step hs n z hH) x (b,m) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_of_countable _),indexed_terminal_lintegral ν step n z H x b m hb hi,
    indexedOneStateKernel,atomicVisitKernel_lintegral _ _ _ _ _ hf]

lemma indexed_terminal_exp_integrable_ae (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (H : X→ℝ) (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
      Integrable (fun l => Real.exp (H (indexedLeafState step n (x,p.2) l)))
        (indexedLeafProbability n p.1) := by
  have hnorm := finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz0 i).ne') H hI
  have ht := indexedTiltedTotal_regular ν step hs n z hz hz0 hz1
    (finiteCascadeShifts ν step n z H) (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i x => (hnorm i x).1) (fun i x => (hnorm i x).2) x
  have hb := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
    (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae (indexedLeafMeasure_regular n z hz hz0 hz1)
  have hg := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
    (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae (indexedCascadeGood_ae n z hz0 hz1)
  filter_upwards [ht,hb,hg] with p ht hb hg
  refine ⟨(measurable_of_countable _).aestronglyMeasurable,?_⟩
  simp only [HasFiniteIntegral,Real.enorm_eq_ofReal (Real.exp_pos _).le]
  rw [indexedLeafProbability_terminal_identity ν hs hH n p.1 hg hb p.2 x,
    decoratedTerminalTotalE_telescoping ν step H n z,
    ←indexedTiltedTotal_eq hs n (finiteCascadeShifts ν step n z H)
      (finiteCascadeShifts_measurable ν step hs n z hH) (x,p) hg]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.toReal_pos_iff.mp hb).1)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.toReal_pos_iff.mp ht).2)

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

lemma gibbsProbabilityKernel_congr_apply {B : Type*} [MeasurableSpace B]
    (η : Kernel B S) [IsMarkovKernel η] (G : B→S→ℝ)
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G))
    (a : A) (b : B) (he : κ a=η b) (hE : H a=G b) :
    gibbsProbabilityKernel κ H a=gibbsProbabilityKernel η G b := by
  by_cases hi : Integrable (fun x => Real.exp (H a x)) (κ a)
  · have hi' : Integrable (fun x => Real.exp (G b x)) (η b) := by simpa [←he,←hE] using hi
    rw [gibbsProbabilityKernel_of_integrable κ H hH a hi,
      gibbsProbabilityKernel_of_integrable η G hG b hi',he,hE]
  · have hi' : ¬Integrable (fun x => Real.exp (G b x)) (η b) := by simpa [←he,←hE] using hi
    rw [gibbsProbabilityKernel_of_not_integrable κ H hH a hi,
      gibbsProbabilityKernel_of_not_integrable η G hG b hi',he]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedMarkProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedOneStateKernel_finite _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

section
variable {S T : Type} [MeasurableSpace S] [MeasurableSpace T]

lemma indexedMarksZip_measurable (n : ℕ) : Measurable (indexedMarksZip (S:=S) (T:=T) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact ((by fun_prop : Measurable (fun p : IndexedCascadeMarks S (n+1) × IndexedCascadeMarks T (n+1) =>
      ((p.1 i j).1,(p.2 i j).1)))).prodMk (ih.comp (by fun_prop))

lemma indexedMarksZip_vertices (n : ℕ) (a : IndexedVertex n→S) (b : IndexedVertex n→T) :
    indexedMarksZip n (indexedMarksFromVertices n a,indexedMarksFromVertices n b)=
      indexedMarksFromVertices n (fun v => (a v,b v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i j
    exact congrArg (fun x => ((a (i,j,.inl ()),b (i,j,.inl ())),x))
      (ih (fun v => a (i,j,.inr v)) (fun v => b (i,j,.inr v)))

lemma indexedMarksZip_law (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (n : ℕ) :
    ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
      (indexedCascadeMarksLaw ρ n : Measure (IndexedCascadeMarks T n))).map (indexedMarksZip n)=
        (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)) := by
  let A := Measure.infinitePi (fun _ : IndexedVertex n => (ν : Measure S))
  let B := Measure.infinitePi (fun _ : IndexedVertex n => (ρ : Measure T))
  have he : (fun p : (IndexedVertex n→S)×(IndexedVertex n→T) =>
      indexedMarksZip n (indexedMarksFromVertices n p.1,indexedMarksFromVertices n p.2))=
        indexedMarksFromVertices n ∘ (fun p v => (p.1 v,p.2 v)) := by
    funext p
    exact indexedMarksZip_vertices n p.1 p.2
  rw [← indexedMarksFromVertices_law ν n,← indexedMarksFromVertices_law ρ n,
    Measure.map_prod_map _ _ (indexedMarksFromVertices_measurable n) (indexedMarksFromVertices_measurable n),
    Measure.map_map (indexedMarksZip_measurable n)
      ((indexedMarksFromVertices_measurable n).prodMap (indexedMarksFromVertices_measurable n))]
  change (A.prod B).map (fun p => indexedMarksZip n (indexedMarksFromVertices n p.1,indexedMarksFromVertices n p.2))=_
  rw [he,← Measure.map_map (indexedMarksFromVertices_measurable n) (by fun_prop)]
  dsimp [A,B]
  rw [infinitePi_zip]
  exact indexedMarksFromVertices_law (productMarkLaw ν ρ) n

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedPathProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma pathMean_parallel (n : ℕ) (κ : Fin n → Kernel X X) (η : Fin n → Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfB : ∀ x, |f x| ≤ C) (hgB : ∀ y, |g y| ≤ D) (x : X) (y : Y) :
    pathMean n (fun i => κ i ∥ₖ η i) (fun p => f p.1*g p.2) (x,y) =
      pathMean n κ f x * pathMean n η g y := by
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hB : ∀ p : X×Y, |f p.1*g p.2| ≤ C*D := fun p => by
    simpa only [abs_mul, abs_of_nonneg hD] using
      mul_le_mul (hfB p.1) ((hgB p.2).trans (le_abs_self D)) (abs_nonneg _) hC
  induction n generalizing x y with
  | zero =>
    simp only [pathMean,pathOneKernel,Kernel.id_apply]
    rw [integral_dirac' _ _ hfg.stronglyMeasurable,
      integral_dirac' _ _ hf.stronglyMeasurable,integral_dirac' _ _ hg.stronglyMeasurable]
  | succ n ih =>
    have := hκ 0
    have := hη 0
    have hpar : ∀ i, IsMarkovKernel (κ i ∥ₖ η i) := by intro i; have := hκ i; have := hη i; infer_instance
    rw [pathMean_succ n _ hpar _ hfg (C*D) hB,
      pathMean_succ n κ hκ f hf C hfB,pathMean_succ n η hη g hg D hgB,
      Kernel.parallelComp_apply]
    simp_rw [ih _ _ (fun i => hκ i.succ) (fun i => hη i.succ)]
    exact integral_prod_mul _ _

lemma finiteCascadeShifts_add_product (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    {H : X→ℝ} {G : Y→ℝ} (hH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (i : Fin n) (p : (X×Y)×(S×T)) :
    finiteCascadeShifts (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
      (fun x => H x.1+G x.2) i p =
      finiteCascadeShifts ν step₁ n z H i (p.1.1,p.2.1)+
        finiteCascadeShifts ρ step₂ n z G i (p.1.2,p.2.2) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      simp only [finiteCascadeShifts,Fin.cases_zero]
      rw [finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n _ (fun i => hz i.succ) hH.2 hG.2,
        finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ (n+1) z hz hH hG]
      ring
    | succ i =>
      exact ih (fun i => z i.succ) (fun i => hz i.succ) hH.2 hG.2 i

lemma tiltedStateStep_parallel (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (z : ℝ) (F : X×S→ℝ) (G : Y×T→ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hGI : ∀ y, Integrable (fun t => Real.exp (z*G (y,t))) ρ)
    (hFM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν)=1)
    (hGM : ∀ y, (∫ t, Real.exp (z*G (y,t)) ∂ρ)=1) :
    tiltedStateStep (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) z
      (fun p => F (p.1.1,p.2.1)+G (p.1.2,p.2.2)) =
      tiltedStateStep ν step₁ z F ∥ₖ tiltedStateStep ρ step₂ z G := by
  have hs : Measurable (fun p : (X×Y)×(S×T) =>
      (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) := by fun_prop
  have hFG : Measurable (fun p : (X×Y)×(S×T) => F (p.1.1,p.2.1)+G (p.1.2,p.2.2)) := by fun_prop
  have hI (x : X×Y) : Integrable (fun s : S×T => Real.exp (z*(F (x.1,s.1)+G (x.2,s.2))))
      (productMarkLaw ν ρ) := by
    simp_rw [mul_add,Real.exp_add]
    exact (hFI x.1).mul_prod (hGI x.2)
  have hM (x : X×Y) : (∫ s : S×T, Real.exp (z*(F (x.1,s.1)+G (x.2,s.2)))
      ∂productMarkLaw ν ρ)=1 := by
    simp_rw [mul_add,Real.exp_add]
    change (∫ s : S×T, Real.exp (z*F (x.1,s.1))*Real.exp (z*G (x.2,s.2))
      ∂(ν : Measure S).prod (ρ : Measure T))=1
    exact (integral_prod_mul (fun s => Real.exp (z*F (x.1,s)))
      (fun t => Real.exp (z*G (x.2,t)))).trans (by rw [hFM,hGM,one_mul])
  have := tiltedStateStep_markov ν step₁ hs₁ z F hF hFI hFM
  have := tiltedStateStep_markov ρ step₂ hs₂ z G hG hGI hGM
  apply Kernel.ext
  intro x
  apply Measure.ext_of_lintegral
  intro f hf
  rw [tiltedStateStep_lintegral (productMarkLaw ν ρ) _ hs z _ hFG hI hM f hf,
    Kernel.parallelComp_apply,lintegral_prod _ hf.aemeasurable]
  have hi (a : X) := tiltedStateStep_lintegral ρ step₂ hs₂ z G hG hGI hGM
    (fun b => f (a,b)) (hf.comp (measurable_const.prodMk measurable_id)) x.2
  simp_rw [hi]
  have hm : Measurable (fun a : X => ∫⁻ t, ENNReal.ofReal (Real.exp (z*G (x.2,t)))*
      f (a,step₂ (x.2,t)) ∂ρ) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun p : X×T => ENNReal.ofReal (Real.exp (z*G (x.2,p.2)))*
      f (p.1,step₂ (x.2,p.2)))
    fun_prop
  rw [tiltedStateStep_lintegral ν step₁ hs₁ z F hF hFI hFM _ hm]
  change (∫⁻ s : S×T, ENNReal.ofReal (Real.exp (z*(F (x.1,s.1)+G (x.2,s.2))))*
    f (step₁ (x.1,s.1),step₂ (x.2,s.2)) ∂(ν : Measure S).prod (ρ : Measure T))=_
  rw [lintegral_prod]
  · apply lintegral_congr
    intro s
    rw [←lintegral_const_mul]
    · apply lintegral_congr
      intro t
      rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact mul_assoc _ _ _
    · fun_prop
  · fun_prop

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedTerminalProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma cascadeTiltedStep_parallel (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i) (H : X→ℝ) (G : Y→ℝ)
    (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z) (i : Fin n) :
    tiltedStateStep (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) (z i)
      (finiteCascadeShifts (productMarkLaw ν ρ)
        (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
          (fun x => H x.1+G x.2) i) =
      tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i) ∥ₖ
        tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i) := by
  have he := fun p => finiteCascadeShifts_add_product ν ρ step₁ step₂ n z hz hHI hGI i p
  rw [funext he]
  exact tiltedStateStep_parallel ν ρ step₁ step₂ hs₁ hs₂ (z i) _ _
    (finiteCascadeShifts_measurable ν step₁ hs₁ n z hH i)
    (finiteCascadeShifts_measurable ρ step₂ hs₂ n z hG i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step₁ n z (fun i => (hz i).ne') H hHI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ρ step₂ n z (fun i => (hz i).ne') G hGI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step₁ n z (fun i => (hz i).ne') H hHI i x).2)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ρ step₂ n z (fun i => (hz i).ne') G hGI i x).2)

lemma cascadeTiltedStep_markov (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (i : Fin n) :
    IsMarkovKernel (tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) :=
  tiltedStateStep_markov ν step hs (z i) _ (finiteCascadeShifts_measurable ν step hs n z hH i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).2)

lemma indexedTerminalEnergy_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) :
    Measurable (Function.uncurry (indexedTerminalEnergy step n H x)) :=
  hH.comp ((indexedLeafState_measurable hs n).comp
    ((measurable_const.prodMk measurable_fst.snd).prodMk measurable_snd))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalRestorationCoefficients
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexedTerminalMean_joint_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (f : X→ℝ) (hf : Measurable f) :
    Measurable (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) =>
      indexedTerminalMean step n H p.1 f p.2) := by
  let β : Kernel (X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (IndexedLeaf n) :=
    (indexedTerminalBaseKernel n).comap Prod.snd measurable_snd
  let E : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))→IndexedLeaf n→ℝ :=
    fun p l => H (indexedLeafState step n (p.1,p.2.2) l)
  have hstate : Measurable (fun p : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×IndexedLeaf n =>
      indexedLeafState step n (p.1.1,p.1.2.2) p.2) := (indexedLeafState_measurable hs n).comp
    ((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd)
  have hE : Measurable (Function.uncurry E) := hH.comp hstate
  let κ := gibbsProbabilityKernel β E
  have : IsMarkovKernel β := by dsimp [β]; infer_instance
  have : IsMarkovKernel κ := gibbsProbabilityKernel_markov β E hE
  have he (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) :
      κ p=gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H p.1) p.2 :=
    gibbsProbabilityKernel_congr_apply β E (indexedTerminalBaseKernel n)
      (indexedTerminalEnergy step n H p.1) hE
      (indexedTerminalEnergy_measurable step hs n H hH p.1) p p.2
      (by simp [β]) rfl
  have hm := (hf.comp hstate).stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)
  simpa only [he,indexedTerminalMean,Function.comp_apply] using hm.measurable

lemma indexedTerminalMean_bound (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (f : X→ℝ)
    (C : ℝ) (hb : ∀ y, |f y|≤C) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    |indexedTerminalMean step n H x f p|≤C := by
  have := gibbsProbabilityKernel_markov (indexedTerminalBaseKernel n) _
    (indexedTerminalEnergy_measurable step hs n H hH x)
  simpa only [indexedTerminalMean,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p)
      (f:=fun l => f (indexedLeafState step n (x,p.2) l))
      (ae_of_all _ fun l => by simpa only [Real.norm_eq_abs] using hb (indexedLeafState step n (x,p.2) l))

variable [Nonempty S]
lemma indexedTerminalMean_integral (ν : ProbabilityMeasure S) (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (x : X) (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ y, |f y|≤C) :
    (∫ p, indexedTerminalMean step n H x f p
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      pathMean n (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f x := by
  let μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
  let F := finiteCascadeShifts ν step n z H
  have hF := finiteCascadeShifts_measurable ν step hs n z hH
  let κ := indexedOneStateKernel step hs n F hF x
  have he : (fun p => indexedTerminalMean step n H x f p)=ᵐ[μ]
      (fun p => ∫ y, f y ∂κ p) := by
    have hi := indexed_terminal_exp_integrable_ae ν step hs n z hz hz0 hz1 H hH hI x
    have hb₀ := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
      (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae
        (indexedLeafMeasure_regular n z hz hz0 hz1)
    filter_upwards [hi,hb₀] with p hi hp
    unfold indexedTerminalMean
    rw [gibbsProbabilityKernel_of_integrable (indexedTerminalBaseKernel n) _
      (indexedTerminalEnergy_measurable step hs n H hH x) p hi]
    have hmap := indexed_terminal_oneState ν step hs n z H hH x p.1 p.2 hp hi
    have hh := integral_map (μ:=tiltLaw (indexedLeafProbability n p.1)
      (fun l => H (indexedLeafState step n (x,p.2) l)) 1)
      (measurable_of_countable (indexedLeafState step n (x,p.2))).aemeasurable hf.aestronglyMeasurable
    rw [hmap] at hh
    exact hh.symm
  rw [integral_congr_ae he]
  have hnorm := finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz0 i).ne') H hI
  have hi := path_bounded_integrable (κ ∘ₘ μ) f hf C hb
  have hcomp : (∫ y, f y ∂(κ ∘ₘ μ))=∫ p, ∫ y, f y ∂κ p ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hi ⊢
    exact Kernel.integral_comp hi
  rw [←hcomp]
  change (∫ y, f y ∂(indexedOneStateKernel step hs n F hF x ∘ₘ μ))=_
  rw [indexedOneStateLaw_eq ν step hs n z hz hz0 hz1 F hF
    (fun i y => (hnorm i y).1) (fun i y => (hnorm i y).2)]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalRestorationLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {X R S : Type} [MeasurableSpace X] [MeasurableSpace R] [MeasurableSpace S] [Nonempty S]

lemma indexedTerminalMean_root_integral (μ : ProbabilityMeasure R) (ν : ProbabilityMeasure S)
    (step : X×S→X) (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (x : R→X) (hx : Measurable x) (f : X→ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ y, |f y|≤C) :
    (∫ p, indexedTerminalMean step n H (x p.1) f p.2
      ∂(μ : Measure R).prod ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) f := by
  let V : R×(IndexedCascadeBase n×IndexedCascadeMarks S n)→ℝ :=
    fun p => indexedTerminalMean step n H (x p.1) f p.2
  have hm := (indexedTerminalMean_joint_measurable step hs n H hH f hf).comp
    ((hx.comp measurable_fst).prodMk measurable_snd)
  have hV : Measurable V := hm
  have hi : Integrable V ((μ : Measure R).prod ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) := by
    apply Integrable.of_bound hV.aestronglyMeasurable C
    exact ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs] using indexedTerminalMean_bound step hs n H hH (x p.1) f C hb p.2
  change (∫ p, V p ∂_)=_
  rw [integral_prod _ hi]
  simp only [V,indexedTerminalMean_integral ν step hs n z hz hz0 hz1 H hH hI _ f hf C hb,rootPathMean]

end
section
variable {X Y R Q S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace S] [MeasurableSpace T]

lemma rootPathMean_parallel (μ : Measure R) (σ : Measure Q) [SFinite μ] [SFinite σ]
    (x : R→X) (y : Q→Y) (n : ℕ) (κ : Fin n→Kernel X X) (η : Fin n→Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
    rootPathMean (μ.prod σ) (fun p => (x p.1,y p.2)) n (fun i => κ i ∥ₖ η i)
      (fun p => f p.1*g p.2) = rootPathMean μ x n κ f * rootPathMean σ y n η g := by
  unfold rootPathMean
  simp_rw [pathMean_parallel n κ η hκ hη f g hf hg C D hC hD hfB hgB]
  exact integral_prod_mul (fun r => pathMean n κ f (x r)) (fun q => pathMean n η g (y q))

lemma cascade_root_single_coefficients_product
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz0 : ∀ i, 0<z i)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    rootPathMean ((μ : Measure R).prod (σ : Measure Q)) (fun r => (x r.1,y r.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ) st (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ) st n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f *
      rootPathMean σ y n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g := by
  dsimp only
  simp_rw [cascadeTiltedStep_parallel ν ρ step₁ step₂ hs₁ hs₂ n z hz0 H G hH hG hHI hGI]
  exact rootPathMean_parallel μ σ x y n _ _
    (fun i => cascadeTiltedStep_markov ν step₁ hs₁ n z hz0 H hH hHI i)
    (fun i => cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i)
    f g hf hg C D hC hD hfB hgB

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_SingleRestorationLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {X R : Type} [MeasurableSpace X] [MeasurableSpace R]
lemma rootPathMean_one (μ : Measure R) [IsProbabilityMeasure μ] (x : R→X)
    (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i,IsMarkovKernel (κ i)) :
    rootPathMean μ x n κ (fun _ => 1)=1 := by
  have := pathOneKernel_markov n κ hκ
  simp [rootPathMean,pathMean]
end
section
variable {X Y R Q S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace S] [MeasurableSpace T]
  [Nonempty S] [Nonempty T]
lemma indexedTerminalMean_independent_roots
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y)
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a,|f a|≤C) (hgB : ∀ b,|g b|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p,indexedTerminalMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2)
      (fun p => f p.1*g p.2) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f *
      rootPathMean σ y n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g := by
  dsimp only
  let st : (X×Y)×(S×T)→X×Y := fun p => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  have hterm : Measurable (fun p : X×Y => H p.1+G p.2) := by fun_prop
  have hobs : Measurable (fun p : X×Y => f p.1*g p.2) := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB _) (hgB _) (abs_nonneg _) hC
  have hzmap : MeasurePreserving (indexedMarksZip (S:=S) (T:=T) n)
      ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
        (indexedCascadeMarksLaw ρ n)) (indexedCascadeMarksLaw (productMarkLaw ν ρ) n) :=
    ⟨indexedMarksZip_measurable n,indexedMarksZip_law ν ρ n⟩
  have hp := (MeasurePreserving.id ((μ : Measure R).prod (σ : Measure Q))).prod
    ((MeasurePreserving.id (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))).prod hzmap)
  let F : (R×Q)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n)→ℝ :=
    fun p => indexedTerminalMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2)
      (fun p => f p.1*g p.2) p.2
  let D₀ := (R×Q)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n)
  let tr : D₀→(X×Y)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n) :=
    fun p => ((x p.1.1,y p.1.2),p.2)
  have htr : Measurable tr :=
    (((hx.comp (measurable_fst.fst : Measurable (fun p : D₀ => p.1.1))).prodMk
      (hy.comp measurable_fst.snd)).prodMk measurable_snd)
  have hj := indexedTerminalMean_joint_measurable st hs n
    (fun p => H p.1+G p.2) hterm (fun p => f p.1*g p.2) hobs
  have hm' := hj.comp htr
  have hm : Measurable F := hm'
  have he := integral_map (μ:=((μ : Measure R).prod (σ : Measure Q)).prod
      ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
          (indexedCascadeMarksLaw ρ n)))) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  dsimp only [F,Prod.map_apply,id_eq] at he
  have hv := indexedTerminalMean_root_integral
    (productMarkLaw μ σ) (productMarkLaw ν ρ) st hs n z hz hz0 hz1 _ hterm
    (finiteCascadeFractionalIntegrable_add_product ν ρ step₁ step₂ n z hz0 hHI hGI)
    (fun p => (x p.1,y p.2)) (by fun_prop) _ hobs (C*D) hb
  have hc := cascade_root_single_coefficients_product μ σ ν ρ step₁ step₂ hs₁ hs₂ n z hz0
    H G hH hG hHI hGI x y f g hf hg C D hC hD hfB hgB
  exact he.symm.trans (hv.trans hc)

lemma indexedTerminalMean_ignore_old
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y)
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ a,|f a|≤C) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p,indexedTerminalMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2)
      (fun p => f p.1) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      rootPathMean μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f := by
  have h := indexedTerminalMean_independent_roots μ σ ν ρ step₁ step₂ hs₁ hs₂
    n z hz hz0 hz1 H G hH hG hHI hGI x y hx hy f (fun _ => 1)
    hf measurable_const C 1 hC (by norm_num) hfB (fun _ => by norm_num)
  have hm i := cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i
  simpa only [rootPathMean_one σ y n _ hm,mul_one] using h
end
variable {X Y Z R Q U S T V : Type}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace V]
  [Nonempty S] [Nonempty T] [Nonempty V]

lemma indexedTerminalMean_two_fresh_old_oai
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (τ : ProbabilityMeasure U)
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (π : ProbabilityMeasure V)
    (st₁ : X×S→X) (st₂ : Y×T→Y) (st₀ : Z×V→Z)
    (hs₁ : Measurable st₁) (hs₂ : Measurable st₂) (hs₀ : Measurable st₀)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (J : Z→ℝ) (hH : Measurable H) (hG : Measurable G) (hJ : Measurable J)
    (hHI : finiteCascadeFractionalIntegrable ν st₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ st₂ G n z)
    (hJI : finiteCascadeFractionalIntegrable π st₀ J n z)
    (x : R→X) (y : Q→Y) (v : U→Z) (hx : Measurable x) (hy : Measurable y) (hv : Measurable v)
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
    let st := fun p : ((X×Y)×Z)×((S×T)×V) =>
      ((st₁ (p.1.1.1,p.2.1.1),st₂ (p.1.1.2,p.2.1.2)),st₀ (p.1.2,p.2.2))
    (∫ p, indexedTerminalMean st n (fun p => (H p.1.1+G p.1.2)+J p.2)
      ((x p.1.1.1,y p.1.1.2),v p.1.2) (fun p => f p.1.1*g p.1.2)
      (p.2.1,indexedMarksZip n p.2.2)
      ∂(((μ : Measure R).prod (σ : Measure Q)).prod (τ : Measure U)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)).prod
            (indexedCascadeMarksLaw π n)))) =
      (rootPathMean μ x n (fun i => tiltedStateStep ν st₁ (z i)
          (finiteCascadeShifts ν st₁ n z H i)) f *
        rootPathMean σ y n (fun i => tiltedStateStep ρ st₂ (z i)
          (finiteCascadeShifts ρ st₂ n z G i)) g) := by
  let st : (X×Y)×(S×T)→X×Y := fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB _) (hgB _) (abs_nonneg _) hC
  have h := indexedTerminalMean_ignore_old (productMarkLaw μ σ) τ (productMarkLaw ν ρ) π
    st st₀ hs hs₀ n z hz hz0 hz1 (fun p => H p.1+G p.2) J (by fun_prop) hJ
    (finiteCascadeFractionalIntegrable_add_product ν ρ st₁ st₂ n z hz0 hHI hGI) hJI
    (fun p => (x p.1,y p.2)) v (by fun_prop) hv (fun p => f p.1*g p.2) hfg
    (C*D) (mul_nonneg hC hD) hb
  dsimp only [st] at h ⊢
  change _ = rootPathMean ((μ : Measure R).prod (σ : Measure Q)) (fun p => (x p.1,y p.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ)
        (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ)
          (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) at h
  rw [cascade_root_single_coefficients_product μ σ ν ρ st₁ st₂ hs₁ hs₂ n z hz0
    H G hH hG hHI hGI x y f g hf hg C D hC hD hfB hgB] at h
  exact h

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old_oai := @OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old_oai
