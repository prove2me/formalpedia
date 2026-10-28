-- Prove2me | solution 1 for OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:45:57.624637+00:00
-- url     : https://prove2.me/submissions/133592ef-a147-4ddf-99ff-c54710aa4a58

import Mathlib
import Definitions.Def_SphericalField
import Definitions.Def_OAIB3Sp000

section
-- module Solutions.OAIB3_Sph.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Intensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
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
  simp_rw [hlocal,smul_eq_mul,← measureReal_def,poissonMeasure_real_singleton]
  simpa only [integral_poissonMeasure,smul_eq_mul] using
    poisson_power_integral r (∫ x, Real.exp (-f x) ∂ν)

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_CountableLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Laplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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
  have hE : Measurable E := Measurable.of_eval fun measurableSet =>
    Measure.measurable_coe measurableSet.property
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_RandomMeasure
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma poissonRandomMeasureLaw_laplace {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂poissonRandomMeasureLaw κ =
      expNegENNReal (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-f x)) ∂κ) := by
  rw [poissonRandomMeasureLaw,countablePoissonLaw_laplace_intensity _ _ hf hf0]
  congr 2
  simp only [countablePoissonIntensity,finiteIntensityMarks_smul,sum_sfiniteSeq]

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Campbell
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_PositiveMass
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Mecke
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Gibbs_GaussianField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Gibbs_ReplicaCalculus
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma gamma_lintegral_positive_scale {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^(a-1) * Real.exp (-t*r))) =
      ENNReal.ofReal (r^(-a) * Real.Gamma a) := by
  have hi : IntegrableOn (fun t : ℝ => t^(a-1) * Real.exp (-t*r)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a-1)
      (b := r) (by linarith) (by norm_num) hr using 1
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_FractionalMoments
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_Superposition
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

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

end SphericalPerceptron

end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable

@[fun_prop] lemma measurable_fin_cons {A : Type*} [MeasurableSpace A] {n : ℕ}
    {f : A → ℝ} {g : A → Fin n → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => (Fin.cons (f a) (g a) : Fin (n+1) → ℝ)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa only [Fin.cons_succ,Function.comp_def] using (measurable_pi_apply j).comp hg

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_MarkedStable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable
section MarkedStable
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

end MarkedStable
end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Poisson_WeightedTotal
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

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

end SphericalPerceptron

end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_TotalLaw
attribute [-instance] _root_.OAI.SphericalPerceptron.stableLogIntensity_noAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
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
    congr 1
    funext x
    dsimp [F]
    ring
  rw [hT,show (fun η : Measure (ℝ×S) => Real.exp c*stablePoissonTotal
      (η.map (fun p => p.1+F p.2))) =
      (fun η : Measure ℝ => Real.exp c*stablePoissonTotal η) ∘ Measure.map (fun p : ℝ×S => p.1+F p.2) from rfl,
    ← Measure.map_map ((stablePoissonTotal_measurable.const_mul _))
      (Measure.measurable_map _ hm),he]

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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_FocusedShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Descendants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
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
  funext p
  calc
    _ = ∫⁻ d, s.indicator (fun _ => (1:ℝ≥0∞)) d ∂(markedStableCountKernel p.2).map (fun q => F (p.1,q)) :=
      (lintegral_indicator_one hs).symm
    _ = _ := lintegral_map (measurable_const.indicator hs)
      (hF.comp (measurable_const.prodMk measurable_id))

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Decorated
attribute [-instance] _root_.OAI.SphericalPerceptron.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_LogFluctuations
attribute [-instance] _root_.OAI.SphericalPerceptron.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
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

lemma fractionalLogMoment_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (b : ℝ) {f : X×S → ℝ} (hf : Measurable f) :
    Measurable (fractionalLogMoment ν b f) := by
  exact (((hf.const_mul b).exp.stronglyMeasurable.integral_prod_right').measurable.log).div_const b

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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Recursion
attribute [-instance] _root_.OAI.SphericalPerceptron.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

lemma finiteCascadeLogRecursion_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) {H : X → ℝ} (hH : Measurable H) :
    Measurable (finiteCascadeLogRecursion ν step n z H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact fractionalLogMoment_measurable ν (z 0) ((ih (fun i => z i.succ)).comp hs)

lemma finiteCascadeShifts_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) {H : X → ℝ} (hH : Measurable H) :
    ∀ i, Measurable (finiteCascadeShifts ν step n z H i) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) j) i
    exact ((finiteCascadeLogRecursion_measurable ν step hs n (fun j => z j.succ) hH).comp hs).sub
      ((finiteCascadeLogRecursion_measurable ν step hs (n+1) z hH).comp measurable_fst)

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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Gaussian_Quadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Gaussian_Fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_CoordinateBounds
attribute [-instance] _root_.OAI.SphericalPerceptron.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

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
  have hdpos := hid.symm.ae_mem_snd measurableSet_Ioi hp
  have hzpos := hiz.symm.ae_mem_snd measurableSet_Ioi hp
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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Coordinates
attribute [-instance] _root_.OAI.SphericalPerceptron.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_Concentration
attribute [-instance] _root_.OAI.SphericalPerceptron.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron

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

end SphericalPerceptron

end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Gaussian_ExponentialNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
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

lemma gaussian_integrable_norm_sq_exp (a : ℝ) :
    Integrable (fun y : E => ‖y‖^2*Real.exp (a*‖y‖)) μ := by
  have he : integrableExpSet (fun y : E => ‖y‖) μ=univ :=
    Set.eq_univ_of_forall (gaussian_integrable_exp_norm μ)
  have ht : a ∈ interior (integrableExpSet (fun y : E => ‖y‖) μ) := by simp [he]
  have h := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 2
  simpa using h

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

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_EntropicParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SphericalPerceptron

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

lemma entropicMean_param_bound
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, deriv (deriv (cgf X μ)) t ≤ K)
    {p q : ℝ} (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |entropicMean μ p X-entropicMean μ q X| ≤ K*|p-q| := by
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  have hl : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |deriv (cgf X μ) x-deriv (cgf X μ) y| ≤ K*|x-y| := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.hasDerivAt.hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs,abs_of_nonneg (cgf_second_nonneg μ hX t)]; exact hbound t ht)
      (convex_Icc (0:ℝ) 1) hy hx
  have hip : IntervalIntegrable (fun t : ℝ => deriv (cgf X μ) (p*t)) volume 0 1 := by
    exact (hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => p*t))).intervalIntegrable 0 1
  have hiq : IntervalIntegrable (fun t : ℝ => deriv (cgf X μ) (q*t)) volume 0 1 := by
    exact (hc.comp ((continuous_const.mul continuous_id) : Continuous (fun t : ℝ => q*t))).intervalIntegrable 0 1
  unfold entropicMean
  rw [← intervalIntegral.integral_sub hip hiq]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := K*|p-q|)
    (f := fun t => deriv (cgf X μ) (p*t)-deriv (cgf X μ) (q*t)) (by
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using (Set.Ioc_subset_Icc_self ht)
      have hpt : p*t ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg hp.1 ht'.1,
        (mul_le_mul hp.2 ht'.2 ht'.1 (by norm_num)).trans (by norm_num)⟩
      have hqt : q*t ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg hq.1 ht'.1,
        (mul_le_mul hq.2 ht'.2 ht'.1 (by norm_num)).trans (by norm_num)⟩
      have hh := hl _ hpt _ hqt
      rw [← sub_mul,abs_mul,abs_of_nonneg ht'.1] at hh
      apply hh.trans
      have := mul_le_mul_of_nonneg_left ht'.2 (mul_nonneg hK (abs_nonneg (p-q)))
      nlinarith)
  simpa using H

lemma cgf_second_le_of_moments
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {t c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hl : c ≤ mgf X μ t)
    (hu : (∫ ω, (X ω)^2*Real.exp (t*X ω) ∂μ) ≤ K) :
    deriv (deriv (cgf X μ)) t ≤ K/c := by
  have hh := iteratedDeriv_two_cgf (mem_interior_integrableExpSet_of_all μ hX t)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hh
  rw [hh]
  calc
    _ ≤ (∫ ω, (X ω)^2*Real.exp (t*X ω) ∂μ)/mgf X μ t := sub_le_self _ (sq_nonneg _)
    _ ≤ K/mgf X μ t := div_le_div_of_nonneg_right hu (mgf_pos (hX t)).le
    _ ≤ K/c := div_le_div_of_nonneg_left hK hc hl

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Entropic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

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

section
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

lemma gaussianEntropic_add_const {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (p σ c : ℝ) (x : E) :
    gaussianEntropic μ p σ (fun z => f z+c) x=gaussianEntropic μ p σ f x+c :=
  entropicMean_add_const μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) p c

lemma gaussianEntropicParamConstant_nonneg (L S : ℝ) :
    0 ≤ gaussianEntropicParamConstant μ L S := by
  apply div_nonneg
  · exact mul_nonneg (sq_nonneg _) (integral_nonneg fun y =>
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  · exact (mgf_pos (gaussian_integrable_exp_norm μ (-(L*S)))).le

lemma gaussianEntropic_parameter_bound {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p q σ S : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1)
    (hσ : 0 ≤ σ) (hσS : σ ≤ S) (x : E) :
    |gaussianEntropic μ p σ f x-gaussianEntropic μ q σ f x| ≤
      gaussianEntropicParamConstant μ L S*σ^2*|p-q| := by
  let X : E → ℝ := fun y => f (x+σ • y)-f x
  have hX : ∀ t : ℝ, Integrable (fun y => Real.exp (t*X y)) μ := by
    intro t
    simpa [X,sub_eq_add_neg] using all_exp_add_const μ
      (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) (-f x) t
  have hnorm (y : E) : |X y| ≤ (L:ℝ)*σ*‖y‖ := by
    have hh := hf.dist_le_mul (x+σ • y) x
    simpa only [X,Real.dist_eq,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg hσ,mul_assoc] using hh
  have hlin (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (y : E) :
      |t*X y| ≤ (L:ℝ)*S*‖y‖ := by
    rw [abs_mul,abs_of_nonneg ht.1]
    calc
      t*|X y| ≤ |X y| := mul_le_of_le_one_left (abs_nonneg _) ht.2
      _ ≤ (L:ℝ)*σ*‖y‖ := hnorm y
      _ ≤ (L:ℝ)*S*‖y‖ := by gcongr
  let c := mgf (fun y : E => ‖y‖) μ (-((L:ℝ)*S))
  have hc : 0 < c := mgf_pos (gaussian_integrable_exp_norm μ (-((L:ℝ)*S)))
  let I := ∫ y : E, ‖y‖^2*Real.exp ((L:ℝ)*S*‖y‖) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      deriv (deriv (cgf X μ)) t ≤ gaussianEntropicParamConstant μ L S*σ^2 := by
    have hl : c ≤ mgf X μ t := by
      apply integral_mono (gaussian_integrable_exp_norm μ (-((L:ℝ)*S))) (hX t)
      intro y
      apply Real.exp_le_exp.mpr
      have hh := (abs_le.mp (hlin t ht y)).1
      nlinarith
    have hu : (∫ y, (X y)^2*Real.exp (t*X y) ∂μ) ≤ (L:ℝ)^2*σ^2*I := by
      have hi := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
        (mem_interior_integrableExpSet_of_all μ hX t) 2
      calc
        _ ≤ ∫ y : E, ((L:ℝ)^2*σ^2)*(‖y‖^2*Real.exp ((L:ℝ)*S*‖y‖)) ∂μ := by
          apply integral_mono hi ((gaussian_integrable_norm_sq_exp μ ((L:ℝ)*S)).const_mul _)
          intro y
          have hs : (X y)^2 ≤ (L:ℝ)^2*σ^2*‖y‖^2 := by
            have hn := hnorm y
            have hz : 0 ≤ (L:ℝ)*σ*‖y‖ := by positivity
            simpa only [sq_abs,mul_pow] using (sq_le_sq₀ (abs_nonneg (X y)) hz).mpr hn
          have he : Real.exp (t*X y) ≤ Real.exp ((L:ℝ)*S*‖y‖) :=
            Real.exp_le_exp.mpr ((le_abs_self _).trans (hlin t ht y))
          have hh := mul_le_mul hs he (Real.exp_pos _).le (by positivity)
          convert hh using 1
          ring
        _ = _ := by rw [integral_const_mul]
    have hh := cgf_second_le_of_moments μ hX hc (by positivity) hl hu
    convert hh using 1
    dsimp [gaussianEntropicParamConstant,c,I]
    ring
  have H := entropicMean_param_bound μ hX
    (mul_nonneg (gaussianEntropicParamConstant_nonneg μ L S) (sq_nonneg σ)) hbound hp hq
  have he (a : ℝ) : entropicMean μ a X=gaussianEntropic μ a σ f x-f x := by
    simpa [X,gaussianEntropic,sub_eq_add_neg] using entropicMean_add_const μ
      (fun b => gaussian_integrable_exp_lipschitz μ hf b σ x) a (-f x)
  rw [he p,he q] at H
  convert H using 1
  congr 1
  ring

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Semigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
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

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Backward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

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

omit [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E] [IsGaussian μ] in
lemma gaussianBackward_append (l m : List (ℝ×ℝ)) (f : E → ℝ) :
    gaussianBackward μ (l++m) f=gaussianBackward μ l (gaussianBackward μ m f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append,gaussianBackward,ih]

end

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Invariance
attribute [-instance] _root_.OAI.SphericalPerceptron.instIsProbabilityMeasureElemSpinHAddNatOfNatSphereRealUnitSphereLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
section SphereInvariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma sphereIsometryMap_measurable (e : E ≃ₗᵢ[ℝ] E) : Measurable (sphereIsometryMap e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sphereIsometryMap_preimage_cone (e : E ≃ₗᵢ[ℝ] E) (s : Set (Metric.sphere (0 : E) 1)) :
    Ioo (0:ℝ) 1 • (Subtype.val '' (sphereIsometryMap e ⁻¹' s)) =
      e ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨r,hr,e u,⟨sphereIsometryMap e u,hu,rfl⟩,by simp⟩
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,he⟩
    refine ⟨r,hr,e.symm u,⟨sphereIsometryMap e.symm u,?_,rfl⟩,?_⟩
    · simpa [sphereIsometryMap] using hu
    · apply e.injective
      simpa only [map_smul,LinearIsometryEquiv.apply_symm_apply] using he

lemma sphereIsometryMap_preserving (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometryMap e) (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereIsometryMap_measurable e) hs,
    Measure.toSphere_apply' _ ((sphereIsometryMap_measurable e) hs),Measure.toSphere_apply' _ hs,
    sphereIsometryMap_preimage_cone]
  congr 1
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

end SphereInvariance

lemma unitSphereLaw_isometry_preserving {N : ℕ} (e : Spin N ≃ₗᵢ[ℝ] Spin N) :
    MeasurePreserving (sphereIsometryMap e) (unitSphereLaw N) (unitSphereLaw N) := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  simp only [unitSphereLaw,Measure.map_smul]
  rw [(sphereIsometryMap_preserving e).map_eq]

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_RadialBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma unitSphere_continuous_integrable {n : ℕ}
    {f : Metric.sphere (0 : Spin (n+1)) 1 → ℝ} (hf : Continuous f) :
    Integrable f (unitSphereLaw (n+1)) := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun u => hC u (mem_univ _))

lemma sphericalExp_even (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z (-r) = sphericalExp n z r := by
  have hemb : MeasurableEmbedding (sphereIsometryMap (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))) := by
    apply Measurable.measurableEmbedding
      (sphereIsometryMap_measurable _) _
    intro u v huv
    apply Subtype.ext
    have := congrArg Subtype.val huv
    simpa [sphereIsometryMap] using this
  have h := (unitSphereLaw_isometry_preserving (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))).integral_comp hemb
    (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (r * inner ℝ z (u:Spin (n+1))))
  simpa [sphericalExp,sphereIsometryMap] using h

lemma sphericalExp_eq_cosh (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z r =
      ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.cosh (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1) := by
  have hi (s : ℝ) : Integrable (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (s * inner ℝ z (u:Spin (n+1)))) (unitSphereLaw (n+1)) :=
    unitSphere_continuous_integrable (by fun_prop)
  simp only [Real.cosh_eq,integral_div]
  rw [integral_add (hi r) (by simpa only [neg_mul] using hi (-r))]
  simp only [← neg_mul]
  change sphericalExp n z r = (sphericalExp n z r + sphericalExp n z (-r))/2
  rw [sphericalExp_even]
  ring

lemma one_le_sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    1 ≤ sphericalExp n z r := by
  rw [sphericalExp_eq_cosh]
  calc
    (1:ℝ) = ∫ _ : Metric.sphere (0:Spin (n+1)) 1, (1:ℝ) ∂unitSphereLaw (n+1) := by simp
    _ ≤ _ := integral_mono (integrable_const _) (unitSphere_continuous_integrable (by fun_prop)) (fun u => Real.one_le_cosh _)

end SphericalPerceptron
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Bridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_AmplitudeConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_Heat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

lemma sphericalExp_le_mul (n : ℕ) (R : ℝ) (x y : Spin (n+1)) :
    sphericalExp n x R ≤ Real.exp (|R| *‖x-y‖)*sphericalExp n y R := by
  unfold sphericalExp
  rw [← integral_const_mul]
  apply integral_mono (unitSphere_continuous_integrable (by fun_prop))
    (unitSphere_continuous_integrable (by fun_prop))
  intro u
  dsimp only
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hu : ‖(u:Spin (n+1))‖=1 := by simp
  have hh := abs_real_inner_le_norm (x-y) (u:Spin (n+1))
  rw [hu,mul_one,inner_sub_left] at hh
  have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg R)
  rw [← abs_mul] at hm
  have hl := (le_abs_self (R*(inner ℝ x (u:Spin (n+1))-inner ℝ y (u:Spin (n+1))))).trans hm
  linarith

lemma logSphericalExp_lipschitz (n : ℕ) (R : ℝ) :
    LipschitzWith ⟨|R|,abs_nonneg R⟩ (logSphericalExp n R) := by
  have hle (x y : Spin (n+1)) : logSphericalExp n R x-logSphericalExp n R y ≤ |R| *‖x-y‖ := by
    have hx : 0 < sphericalExp n x R := lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n x R)
    have hy : 0 < sphericalExp n y R := lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n y R)
    have hh := Real.log_le_log hx (sphericalExp_le_mul n R x y)
    rw [Real.log_mul (Real.exp_pos _).ne' hy.ne',Real.log_exp] at hh
    change Real.log (sphericalExp n x R)-Real.log (sphericalExp n y R) ≤ _
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |logSphericalExp n R x-logSphericalExp n R y| ≤ |R| *‖x-y‖
  apply abs_le.mpr
  constructor
  · have hh := hle y x
    rw [norm_sub_rev] at hh
    linarith
  · exact hle x y

lemma integral_exp_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) (a : ℝ) : (∫ x, Real.exp (a*inner ℝ v x) ∂stdGaussian E)=
      Real.exp (a^2*‖v‖^2/2) := by
  have H := mgf_gaussianReal
    (IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)) a
  simp only [integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm,Real.coe_toNNReal (‖v‖^2) (sq_nonneg ‖v‖),zero_mul,zero_add] at H
  change (∫ x, Real.exp (a*inner ℝ v x) ∂stdGaussian E)=Real.exp (‖v‖^2*a^2/2) at H
  convert H using 1
  congr 1
  ring

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Cascade_HeatWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Entropy_StepIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Entropy_StepDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma finite_sum_successive_differences (k : ℕ) (v : Fin (k+1) → ℝ) :
    (∑ i : Fin k, (v i.succ-v i.castSucc)) = v (Fin.last k)-v 0 := by
  have h1 := Fin.sum_univ_succ v
  have h2 := Fin.sum_univ_castSucc v
  rw [Finset.sum_sub_distrib]
  linarith

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_CoupledDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

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

omit [BorelSpace E] in
lemma gaussianGrid_succ (N : ℕ) (p v : Fin (N+1) → ℝ) (f : E → ℝ) :
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
  simp only [gridVariance,List.map_cons,List.sum_cons,eq_comm,add_comm]

section
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
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Sphere_FiniteUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_UniformGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_GridGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma varianceLevels_gridVariance {k : ℕ} (l : List (Fin (k+2)×ℝ)) (i : Fin (k+1)) :
    varianceLevels (fun j => gridVariance l j.castSucc) i =
      (l.map fun c => if c.1 ≤ i.castSucc then c.2 else 0).sum/2 := by
  unfold varianceLevels
  congr 1
  have H := gridVariance_weighted_sum l (fun j => if j ≤ i.castSucc then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul] at H
  rw [Fin.sum_univ_castSucc] at H
  simpa only [Fin.castSucc_le_castSucc_iff,ite_eq_right (not_le.mpr (Fin.castSucc_lt_last i)),add_zero] using H

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_HeightPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma heightIndex_monotone {d : ℕ} (h : Fin (d+1) → ℝ) : Monotone (heightIndex h) := by
  intro s t hst
  change (Finset.univ.filter (fun r => h r < s)).card ≤ (Finset.univ.filter (fun r => h r < t)).card
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
  exact hr.trans_le hst

lemma heightIndex_le_iff {d : ℕ} (h : Fin (d+1) → ℝ) (hh : Monotone h)
    (t : ℝ) (i : Fin (d+1)) : heightIndex h t ≤ i.castSucc ↔ t ≤ h i := by
  constructor
  · intro hi
    by_contra ht
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun r => h r < t) := by
      intro r hr
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact (hh (Finset.mem_Iic.mp hr)).trans_lt (lt_of_not_ge ht)
    have H := Finset.card_le_card hsub
    rw [Fin.card_Iic] at H
    change (Finset.univ.filter (fun r => h r < t)).card ≤ i.val at hi
    omega
  · intro hi
    have hsub : Finset.univ.filter (fun r => h r < t) ⊆ Finset.Iio i := by
      intro r hr
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hr
      apply Finset.mem_Iio.mpr
      by_contra hir
      exact (not_lt_of_ge (hi.trans (hh (le_of_not_gt hir)))) hr
    have H := Finset.card_le_card hsub
    rw [Fin.card_Iio] at H
    exact H

lemma lt_heightIndex_iff {d : ℕ} (h : Fin (d+1) → ℝ) (hh : Monotone h)
    (t : ℝ) (i : Fin (d+1)) : i.castSucc < heightIndex h t ↔ h i < t := by
  simpa only [not_le] using not_congr (heightIndex_le_iff h hh t i)

lemma heightVariances_nonneg {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (j : Fin K) : 0 ≤ heightVariances z j := by
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hz (Fin.castSucc_le_succ j)))

lemma heightVariances_sum {K : ℕ} (z : Fin (K+1) → ℝ) :
    (∑ j, heightVariances z j)=2*(z (Fin.last K)-z 0) := by
  simp only [heightVariances,← Finset.mul_sum,finite_sum_successive_differences]

lemma heightVariances_prefix {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r : ℝ) (hr : r ∈ Set.range z) :
    (∑ j, if z j.succ ≤ r then heightVariances z j else 0)=2*(r-z 0) := by
  obtain ⟨a,rfl⟩ := hr
  have he (j : Fin K) : (if z j.succ ≤ z a then heightVariances z j else 0)=
      2*(min (z a) (z j.succ)-min (z a) (z j.castSucc)) := by
    by_cases hja : j.val < a.val
    · have hs : j.succ ≤ a := by simp only [Fin.le_def,Fin.val_succ]; omega
      have hc : j.castSucc ≤ a := (Fin.castSucc_le_succ j).trans hs
      simp [ite_eq_left (hz hs),min_eq_right (hz hs),min_eq_right (hz hc),heightVariances]
    · have hc : a ≤ j.castSucc := by simp only [Fin.le_def,Fin.val_castSucc]; omega
      have hs : a ≤ j.succ := hc.trans (Fin.castSucc_le_succ j)
      rw [min_eq_left (hz hc),min_eq_left (hz hs),sub_self,mul_zero]
      split_ifs with ht
      · have heq : z j.succ=z j.castSucc := le_antisymm (ht.trans (hz hc)) (hz (Fin.castSucc_le_succ j))
        simp [heightVariances,heq]
      · rfl
  simp only [he,← Finset.mul_sum]
  rw [finite_sum_successive_differences K (fun i => min (z a) (z i))]
  rw [min_eq_left (hz (Fin.le_last a)),min_eq_right (hz (Fin.zero_le a))]

lemma heightIndex_grid_prefix {d K : ℕ} (h : Fin (d+1) → ℝ) (hh : Monotone h)
    (z : Fin (K+1) → ℝ) (hz : Monotone z) (hz0 : z 0=0)
    (hm : ∀ i, h i ∈ Set.range z) (i : Fin (d+1)) :
    varianceLevels (fun j => gridVariance
      (List.ofFn fun r => (heightIndex h (z r.succ),heightVariances z r)) j.castSucc) i=h i := by
  rw [varianceLevels_gridVariance]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,heightIndex_le_iff h hh]
  rw [heightVariances_prefix z hz (h i) (hm i),hz0,sub_zero]
  ring

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_HeightWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma extendedFieldExponents_castSucc {d : ℕ} (w : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    extendedFieldExponents w i.castSucc=fieldExponents w i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [extendedFieldExponents,fieldExponents]
  · unfold extendedFieldExponents fieldExponents
    simp only [Fin.cases_succ,stepCumulative]
    apply Finset.sum_congr rfl
    intro r _
    have he : r.castSucc < i.succ.castSucc ↔ r ≤ i.castSucc := by
      simp only [Fin.lt_def,Fin.le_def,Fin.val_castSucc,Fin.val_succ]
      omega
    simp only [he]

lemma extendedFieldExponents_last {d : ℕ} (w : Fin (d+1) → ℝ) :
    extendedFieldExponents w (Fin.last (d+1))=∑ r, w r := by
  simp [extendedFieldExponents,Fin.castSucc_lt_last]

lemma extendedFieldExponents_nonneg {d : ℕ} (w : Fin (d+1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (i : Fin (d+2)) : 0 ≤ extendedFieldExponents w i := by
  apply Finset.sum_nonneg
  intro r _
  split_ifs <;> first | exact hw r | rfl

lemma extendedFieldExponents_heightIndex {d : ℕ} (w h : Fin (d+1) → ℝ) (hh : Monotone h)
    (t : ℝ) : extendedFieldExponents w (heightIndex h t)=finiteFieldCDFLeft w h t := by
  simp only [extendedFieldExponents,finiteFieldCDFLeft,lt_heightIndex_iff h hh]

lemma sphericalHeatValue_compress (n N : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (l : List (Fin N×ℝ)) (hl : l.Pairwise (fun a b => a.1 ≤ b.1))
    (hv : ∀ c ∈ l, 0 ≤ c.2) :
    sphericalHeatValue n (l.map fun c => (p c.1,Real.sqrt c.2))=
      sphericalHeatValue n (List.ofFn fun i => (p i,Real.sqrt (gridVariance l i))) := by
  unfold sphericalHeatValue
  rw [gaussianBackward_compress (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) N p hp l hl hv]
  congr 1
  rw [List.map_ofFn,List.sum_ofFn,List.map_map]
  change (l.map fun c => (Real.sqrt c.2)^2).sum/2=(∑ i, (Real.sqrt (gridVariance l i))^2)/2
  simp only [Real.sq_sqrt (gridVariance_nonneg l hv _)]
  rw [gridVariance_sum]
  congr 2
  apply List.map_congr_left
  intro c hc
  exact Real.sq_sqrt (hv c hc)

lemma sphericalHeatValue_drop_last_one (n d : ℕ) (p v : Fin (d+2) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hv : ∀ i, 0 ≤ v i) (hpl : p (Fin.last (d+1))=1) :
    sphericalHeatValue n (List.ofFn fun i => (p i,Real.sqrt (v i)))=
      sphericalHeatValue n (List.ofFn fun i : Fin (d+1) => (p i.castSucc,Real.sqrt (v i.castSucc))) := by
  unfold sphericalHeatValue
  have he := congrFun (gaussianGrid_spherical_last n d p v hp (hv _) hpl) 0
  unfold gaussianGrid at he
  rw [he]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,Real.sq_sqrt (hv _)]
  rw [Fin.sum_univ_castSucc v]
  have hn : (n+1:ℕ) ≠ (0:ℝ) := by positivity
  field_simp [hn]
  ring

lemma finiteSphericalFieldValue_height_word {d K : ℕ} (w h : Fin (d+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0)
    (z : Fin (K+1) → ℝ) (hz : Monotone z) (hz0 : z 0=0)
    (hm : ∀ i, h i ∈ Set.range z) (n : ℕ) :
    finiteSphericalFieldValue n d w h=sphericalHeatValue n
      (List.ofFn fun j => (finiteFieldCDFLeft w h (z j.succ),Real.sqrt (heightVariances z j))) := by
  let l := List.ofFn fun j => (heightIndex h (z j.succ),heightVariances z j)
  have hl : l.Pairwise (fun a b => a.1 ≤ b.1) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact heightIndex_monotone h (hz (Fin.succ_le_succ_iff.mpr hij.le))
  have hv : ∀ c ∈ l, 0 ≤ c.2 := by
    intro c hc; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    exact heightVariances_nonneg z hz j
  have he := sphericalHeatValue_compress n (d+2) (extendedFieldExponents w)
    (extendedFieldExponents_nonneg w (fun i => (hw i).le)) l hl hv
  dsimp only [l] at he
  simp only [List.map_ofFn,Function.comp_def,extendedFieldExponents_heightIndex w h hh] at he
  rw [he,sphericalHeatValue_drop_last_one n d _ _
    (extendedFieldExponents_nonneg w (fun i => (hw i).le)) (gridVariance_nonneg l hv)
    (by rw [extendedFieldExponents_last,hw1])]
  have hvf : (fun i => gridVariance l i.castSucc)=fieldVariances d h := by
    have hpref : varianceLevels (fun i => gridVariance l i.castSucc)=h := by
      funext i
      exact heightIndex_grid_prefix h hh z hz hz0 hm i
    rw [← hpref,fieldVariances_varianceLevels]
  simp only [extendedFieldExponents_castSucc]
  change finiteSphericalFieldValue n d w h=sphericalHeatValue n
    (List.ofFn fun i => (fieldExponents w i,Real.sqrt ((fun i => gridVariance l i.castSucc) i)))
  rw [hvf]
  exact finiteSphericalFieldValue_eq_heat w h hw hw1 hh hh0 n

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_HeightCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma heightIndicator_antitone (t : ℝ) : Antitone (fun r => heightIndicator r t) := by
  intro r s hrs
  dsimp only [heightIndicator]
  split_ifs with hs hr
  · rfl
  · exact (hr (hrs.trans_lt hs)).elim
  · norm_num
  · rfl

lemma heightIndicator_weighted_sum {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r : ℝ) (hr : r ∈ Set.range z) :
    (∑ j, heightVariances z j*heightIndicator r (z j.succ))=2*(z (Fin.last K)-r) := by
  have he (j : Fin K) : heightVariances z j*heightIndicator r (z j.succ)=
      heightVariances z j-(if z j.succ ≤ r then heightVariances z j else 0) := by
    unfold heightIndicator
    by_cases hj : z j.succ ≤ r
    · simp [hj,not_lt.mpr hj]
    · simp [hj,lt_of_not_ge hj]
  simp only [he,Finset.sum_sub_distrib,heightVariances_prefix z hz r hr,heightVariances_sum]
  ring

lemma heightIndicator_distance_sum {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r s : ℝ) (hr : r ∈ Set.range z) (hs : s ∈ Set.range z) :
    (∑ j, heightVariances z j*|heightIndicator r (z j.succ)-heightIndicator s (z j.succ)|)=
      2*|r-s| := by
  have H (a b : ℝ) (ha : a ∈ Set.range z) (hb : b ∈ Set.range z) (hab : a ≤ b) :
      (∑ j, heightVariances z j*|heightIndicator a (z j.succ)-heightIndicator b (z j.succ)|)=
        2*|a-b| := by
    simp only [abs_of_nonneg (sub_nonneg.mpr (heightIndicator_antitone _ hab)),mul_sub,
      Finset.sum_sub_distrib,heightIndicator_weighted_sum z hz a ha,heightIndicator_weighted_sum z hz b hb]
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  rcases le_total r s with hrs | hsr
  · exact H r s hr hs hrs
  · simpa only [abs_sub_comm] using H s r hs hr hsr

lemma finiteFieldCDFLeft_coupling_sub {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j) (t : ℝ) :
    finiteFieldCDFLeft w h t-finiteFieldCDFLeft v g t=
      ∑ a, c a*(heightIndicator (h a.1) t-heightIndicator (g a.2) t) := by
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [coupling_sum_fst c w (fun i => heightIndicator (h i) t) hr,
    coupling_sum_snd c v (fun j => heightIndicator (g j) t) hc]
  simp only [finiteFieldCDFLeft,heightIndicator,mul_ite,mul_one,mul_zero]

lemma finiteFieldCDFLeft_coupling_abs {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j) (t : ℝ) :
    |finiteFieldCDFLeft w h t-finiteFieldCDFLeft v g t| ≤
      ∑ a, c a*|heightIndicator (h a.1) t-heightIndicator (g a.2) t| := by
  rw [finiteFieldCDFLeft_coupling_sub w h v g c hr hc t]
  simpa only [abs_mul,abs_of_nonneg (hcn _)] using
    Finset.abs_sum_le_sum_abs (fun a => c a*(heightIndicator (h a.1) t-heightIndicator (g a.2) t)) Finset.univ

lemma finiteFieldCDFLeft_partition_cost {d e K : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j)
    (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (hm : ∀ i, h i ∈ Set.range z) (gm : ∀ j, g j ∈ Set.range z) :
    (∑ j, heightVariances z j*|finiteFieldCDFLeft w h (z j.succ)-finiteFieldCDFLeft v g (z j.succ)|) ≤
      2*(∑ a, c a*|h a.1-g a.2|) := by
  calc
    _ ≤ ∑ j, heightVariances z j*(∑ a, c a*
        |heightIndicator (h a.1) (z j.succ)-heightIndicator (g a.2) (z j.succ)|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (finiteFieldCDFLeft_coupling_abs w h v g c hcn hr hc _)
        (heightVariances_nonneg z hz j)
    _ = ∑ a, c a*(∑ j, heightVariances z j*
        |heightIndicator (h a.1) (z j.succ)-heightIndicator (g a.2) (z j.succ)|) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [heightIndicator_distance_sum z hz _ _ (hm _) (gm _),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

lemma exists_common_height_partition {I J : Type*} [Fintype I] [Fintype J]
    (h : I → ℝ) (g : J → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hh : ∀ i, h i ∈ Icc (0:ℝ) H) (hg : ∀ j, g j ∈ Icc (0:ℝ) H) :
    ∃ (K : ℕ) (z : Fin (K+1) → ℝ), Monotone z ∧ z 0=0 ∧ z (Fin.last K)=H ∧
      (∀ i, h i ∈ Set.range z) ∧ (∀ j, g j ∈ Set.range z) := by
  classical
  let S : Finset ℝ := insert 0 (insert H (Finset.univ.image h ∪ Finset.univ.image g))
  have hs0 : (0:ℝ) ∈ S := by simp [S]
  have hsH : H ∈ S := by simp [S]
  have hsb : ∀ x ∈ S, x ∈ Icc (0:ℝ) H := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hx
    rcases hx with rfl | rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · exact ⟨le_rfl,hH⟩
    · exact ⟨hH,le_rfl⟩
    · exact hh i
    · exact hg j
  obtain ⟨K,hK⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨0,hs0⟩)
  let e := S.orderIsoOfFin hK
  let z : Fin (K+1) → ℝ := fun i => e i
  have hz : Monotone z := fun i j hij => e.monotone hij
  have hm (x : ℝ) (hx : x ∈ S) : x ∈ Set.range z := by
    exact ⟨e.symm ⟨x,hx⟩,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩
  have hz0 : z 0=0 := by
    obtain ⟨i,hi⟩ := hm 0 hs0
    apply le_antisymm
    · rw [← hi]; exact hz (Fin.zero_le i)
    · exact (hsb (z 0) (e 0).2).1
  have hzH : z (Fin.last K)=H := by
    obtain ⟨i,hi⟩ := hm H hsH
    apply le_antisymm
    · exact (hsb (z (Fin.last K)) (e (Fin.last K)).2).2
    · rw [← hi]; exact hz (Fin.le_last i)
  exact ⟨K,z,hz,hz0,hzH,(fun i => hm (h i) (by simp [S])),(fun j => hm (g j) (by simp [S]))⟩

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Heat_WordStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]
lemma gaussianBackward_label_parameter_bound {I : Type*} {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (I×ℝ)) (a b : I → ℝ) {S : ℝ}
    (ha : ∀ c ∈ l, a c.1 ∈ Icc (0:ℝ) 1) (hb : ∀ c ∈ l, b c.1 ∈ Icc (0:ℝ) 1)
    (hσ : ∀ c ∈ l, c.2 ∈ Icc (0:ℝ) S) : ∀ x,
    |gaussianBackward μ (l.map fun c => (a c.1,c.2)) f x-
      gaussianBackward μ (l.map fun c => (b c.1,c.2)) f x| ≤
      gaussianEntropicParamConstant μ L S*(l.map fun c => c.2^2*|a c.1-b c.1|).sum := by
  induction l with
  | nil => intro x; simp [gaussianBackward]
  | cons c l ih =>
    have ha' := fun d hd => ha d (List.mem_cons_of_mem c hd)
    have hb' := fun d hd => hb d (List.mem_cons_of_mem c hd)
    have hσ' := fun d hd => hσ d (List.mem_cons_of_mem c hd)
    have hla : LipschitzWith L (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (ha' e he).1
    have hlb : LipschitzWith L (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (hb' e he).1
    intro x
    simp only [List.map_cons,List.sum_cons,gaussianBackward]
    have H1 := gaussianEntropic_parameter_bound μ hla (ha c List.mem_cons_self)
      (hb c List.mem_cons_self) (hσ c List.mem_cons_self).1 (hσ c List.mem_cons_self).2 x
    have H2 := entropicMean_bounded_difference μ
      (fun t => gaussian_integrable_exp_lipschitz μ hla t c.2 x)
      (fun t => gaussian_integrable_exp_lipschitz μ hlb t c.2 x) (hb c List.mem_cons_self).1
      (ae_of_all _ fun y => ih ha' hb' hσ' (x+c.2 • y))
    have HT := abs_sub_le (gaussianEntropic μ (a c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x)
      (gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x)
      (gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) x)
    dsimp [entropicMean] at H2
    change |gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x-
      gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) x| ≤ _ at H2
    nlinarith

lemma gaussianBackward_ofFn_parameter_bound {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (a b σ : Fin N → ℝ) {S : ℝ}
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (0:ℝ) 1)
    (hσ : ∀ i, σ i ∈ Icc (0:ℝ) S) (x : E) :
    |gaussianBackward μ (List.ofFn fun i => (a i,σ i)) f x-
      gaussianBackward μ (List.ofFn fun i => (b i,σ i)) f x| ≤
      gaussianEntropicParamConstant μ L S*(∑ i, (σ i)^2*|a i-b i|) := by
  have ha' : ∀ c ∈ List.ofFn (fun i => (i,σ i)), a c.1 ∈ Icc (0:ℝ) 1 := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact ha i
  have hb' : ∀ c ∈ List.ofFn (fun i => (i,σ i)), b c.1 ∈ Icc (0:ℝ) 1 := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hb i
  have hσ' : ∀ c ∈ List.ofFn (fun i => (i,σ i)), c.2 ∈ Icc (0:ℝ) S := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hσ i
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def] using
    gaussianBackward_label_parameter_bound μ hf (List.ofFn fun i => (i,σ i)) a b ha' hb' hσ' x

end
end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma finiteFieldCDFLeft_mem {d : ℕ} (w h : Fin (d+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (t : ℝ) :
    finiteFieldCDFLeft w h t ∈ Icc (0:ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hw i | rfl
  · rw [← hw1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | exact le_rfl | exact hw i

lemma sphericalHeatValue_parameter_bound (n N : ℕ) (a b σ : Fin N → ℝ) (S : ℝ)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (0:ℝ) 1)
    (hσ : ∀ i, σ i ∈ Icc (0:ℝ) S) :
    |sphericalHeatValue n (List.ofFn fun i => (a i,σ i))-
      sphericalHeatValue n (List.ofFn fun i => (b i,σ i))| ≤
      gaussianEntropicParamConstant (stdGaussian (Spin (n+1))) |Real.sqrt (n+1:ℕ)| S *
        (∑ i, (σ i)^2*|a i-b i|)/(n+1:ℕ) := by
  have H := gaussianBackward_ofFn_parameter_bound (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) N a b σ ha hb hσ 0
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  have Hd := div_le_div_of_nonneg_right H hn.le
  have hs (x y c : ℝ) : |(x/(n+1:ℕ)-c)-(y/(n+1:ℕ)-c)|=|x-y|/(n+1:ℕ) := by
    rw [show (x/(n+1:ℕ)-c)-(y/(n+1:ℕ)-c)=(x-y)/(n+1:ℕ) by ring]
    rw [abs_div,abs_of_pos hn]
  simp only [sphericalHeatValue,List.map_ofFn,List.sum_ofFn,Function.comp_def,hs]
  convert Hd using 1
  all_goals try rfl

theorem finiteSphericalFieldValue_coupling_bound {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1)
    (hv : ∀ j, 0 < v j) (hv1 : ∑ j, v j=1)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) (hg : Monotone g) (hg0 : 0 ≤ g 0)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j)
    (H : ℝ) (hH : 0 ≤ H) (hhH : h (Fin.last d) ≤ H) (hgH : g (Fin.last e) ≤ H) (n : ℕ) :
    |finiteSphericalFieldValue n d w h-finiteSphericalFieldValue n e v g| ≤
      sphericalContinuityConstant n H*(∑ a, c a*|h a.1-g a.2|) := by
  have hhb : ∀ i, h i ∈ Icc (0:ℝ) H := fun i =>
    ⟨hh0.trans (hh (Fin.zero_le i)),(hh (Fin.le_last i)).trans hhH⟩
  have hgb : ∀ i, g i ∈ Icc (0:ℝ) H := fun i =>
    ⟨hg0.trans (hg (Fin.zero_le i)),(hg (Fin.le_last i)).trans hgH⟩
  obtain ⟨K,z,hz,hz0,hzH,hm,gm⟩ := exists_common_height_partition h g H hH hhb hgb
  rw [finiteSphericalFieldValue_height_word w h hw hw1 hh hh0 z hz hz0 hm n,
    finiteSphericalFieldValue_height_word v g hv hv1 hg hg0 z hz hz0 gm n]
  have hσ : ∀ j, Real.sqrt (heightVariances z j) ∈ Icc (0:ℝ) (Real.sqrt (2*H)) := by
    intro j
    refine ⟨Real.sqrt_nonneg _,Real.sqrt_le_sqrt ?_⟩
    have Hsum := heightVariances_sum z
    rw [hz0,hzH,sub_zero] at Hsum
    rw [← Hsum]
    exact Finset.single_le_sum (fun i _ => heightVariances_nonneg z hz i) (Finset.mem_univ j)
  have hp := sphericalHeatValue_parameter_bound n K _ _ _ (Real.sqrt (2*H))
    (fun j => finiteFieldCDFLeft_mem w h (fun i => (hw i).le) hw1 (z j.succ))
    (fun j => finiteFieldCDFLeft_mem v g (fun i => (hv i).le) hv1 (z j.succ)) hσ
  simp only [Real.sq_sqrt (heightVariances_nonneg z hz _)] at hp
  have hcst := gaussianEntropicParamConstant_nonneg (stdGaussian (Spin (n+1)))
    |Real.sqrt (n+1:ℕ)| (Real.sqrt (2*H))
  have hcost := finiteFieldCDFLeft_partition_cost w h v g c hcn hr hc z hz hm gm
  calc
    _ ≤ _ := hp
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hcst) (by positivity)
    _ = _ := by unfold sphericalContinuityConstant; ring

end SphericalPerceptron
end
end

end OAI
end

section
-- module Solutions.OAIB3_Sph.SphericalField_Fields_FiniteModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma FiniteFieldModel.coupling_nonneg {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (a : Fin (M.depth+1)×Fin (N.depth+1)) : 0 ≤ M.coupling N a := measureReal_nonneg

lemma FiniteFieldModel.coupling_fst {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (i : Fin (M.depth+1)) : ∑ j, M.coupling N (i,j)=M.weight i := by
  classical
  have h := integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => if a.1=i then 1 else 0)
  have he := integral_finite_label M.label M.measurable_label (fun a => if a=i then 1 else 0)
  simp only [FiniteFieldModel.coupling,FiniteFieldModel.weight] at *
  simp only [Fintype.sum_prod_type,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h he
  rw [Finset.sum_comm] at h
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h.symm.trans he

lemma FiniteFieldModel.coupling_snd {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (j : Fin (N.depth+1)) : ∑ i, M.coupling N (i,j)=N.weight j := by
  classical
  have h := integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => if a.2=j then 1 else 0)
  have he := integral_finite_label N.label N.measurable_label (fun a => if a=j then 1 else 0)
  simp only [FiniteFieldModel.coupling,FiniteFieldModel.weight] at *
  simp only [Fintype.sum_prod_type,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h he
  exact h.symm.trans he

lemma FiniteFieldModel.coupling_cost {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g) :
    (∑ a, M.coupling N a*|M.value a.1-N.value a.2|)=∫ u, |f u-g u| ∂timeLaw := by
  unfold FiniteFieldModel.coupling
  rw [← integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => |M.value a.1-N.value a.2|)]
  apply integral_congr_ae
  filter_upwards [M.agrees,N.agrees] with u hu hv
  rw [hu,hv]

lemma FiniteFieldModel.pressure_bound_oai {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    {H : ℝ} (hH : 0 ≤ H) (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H)
    (hg : ∀ᵐ u ∂timeLaw, g u ∈ Icc (0:ℝ) H) (n : ℕ) :
    |M.pressure n-N.pressure n| ≤ sphericalContinuityConstant n H*(∫ u, |f u-g u| ∂timeLaw) := by
  have h := finiteSphericalFieldValue_coupling_bound M.weight M.value N.weight N.value (M.coupling N)
    M.weight_pos M.weight_sum N.weight_pos N.weight_sum M.monotone_value (M.values_mem hf 0).1
    N.monotone_value (N.values_mem hg 0).1 (M.coupling_nonneg N) (M.coupling_fst N) (M.coupling_snd N)
    H hH (M.values_mem hf _).2 (N.values_mem hg _).2 n
  rwa [M.coupling_cost N] at h

end SphericalPerceptron
end
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound_oai := @OAI.SphericalPerceptron.FiniteFieldModel.pressure_bound_oai
