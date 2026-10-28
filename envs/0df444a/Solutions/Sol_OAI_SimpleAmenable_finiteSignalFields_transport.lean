-- Prove2me | solution 1 for OAI.SimpleAmenable.finiteSignalFields_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:47:35.103482+00:00
-- url     : https://prove2.me/submissions/72c15b07-acd9-4863-87d3-47119923c4bb

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_finiteAffineNoiseLaw_close
import Theorems.Thm_OAI_SimpleAmenable_flagMatrixDifference_dyadic_energy
import Theorems.Thm_OAI_SimpleAmenable_sourceFlagMatrix_inverse_signal

section
-- module Solutions.OAIQ065_SA.Compat
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_DyadicArithmetic
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceDyadicArithmetic
open Classical Filter
open scoped Topology

theorem sourceDyadicN_one_le (n : ℕ) : 1 ≤ sourceDyadicN n := by
  unfold sourceDyadicN
  exact one_le_pow₀ (by norm_num)

theorem sourceDyadicIndices_card (n : ℕ) : (sourceDyadicIndices n).card=n+1 := by
  simp only [sourceDyadicIndices,Nat.card_Icc]
  omega

theorem sourceDyadic_log (n : ℕ) : Real.log (sourceDyadicN n)=(4*Real.log 2)*(n:ℝ) := by
  rw [sourceDyadicN,Real.log_pow]
  push_cast
  ring

theorem sourceDyadicWeight_square (n : ℕ) :
    (sourceDyadicWeight n)^2=(4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ) := by
  have hb : 0 ≤ 4*Real.log 2 := by positivity
  unfold sourceDyadicWeight
  rw [sourceDyadic_log,← Real.rpow_mul_natCast (mul_nonneg hb (Nat.cast_nonneg n))]
  norm_num
  rw [Real.mul_rpow hb (Nat.cast_nonneg n)]

theorem sourceDyadicWeight_energy_bound {n : ℕ} (hn : 1 ≤ n) :
    ((sourceDyadicIndices n).card:ℝ)*(sourceDyadicWeight n)^2 ≤ 2*(4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-1/2:ℝ) := by
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [sourceDyadicIndices_card,Nat.cast_add,Nat.cast_one,sourceDyadicWeight_square]
  have hc : 0 ≤ (4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ) := by positivity
  have he : (n:ℝ)*(n:ℝ)^(-3/2:ℝ)=(n:ℝ)^(-1/2:ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (n:ℝ)]
    rw [← Real.rpow_add hn₀]
    norm_num
  calc
    _ ≤ (2*(n:ℝ))*((4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hc
    _ = _ := by rw [show (2*(n:ℝ))*((4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ))=
        (2*(4*Real.log 2)^(-3/2:ℝ))*((n:ℝ)*(n:ℝ)^(-3/2:ℝ)) by ring,he]

theorem sourceDyadicWeight_energy_tendsto :
    Tendsto (fun n => ((sourceDyadicIndices n).card:ℝ)*(sourceDyadicWeight n)^2) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(-1/2:ℝ)) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (show (0:ℝ) < 1/2 by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
    rfl
  have ht' := ht.const_mul (2*(4*Real.log 2)^(-3/2:ℝ))
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))) _ ht'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sourceDyadicWeight_energy_bound hn

theorem sourceDyadic_fine_eventually (R : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠn : ℕ in atTop,∀i∈sourceDyadicIndices n,R ≤ κ/((2:ℝ)^i/sourceDyadicN n) := by
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 4 by norm_num)).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop R] with n hn i hi
  have hi' : i ≤ 2*n := (Finset.mem_Icc.mp hi).2
  have hp : (2:ℝ)^i ≤ (2:ℝ)^(2*n) := pow_le_pow_right₀ (by norm_num) hi'
  have he : κ/((2:ℝ)^(2*n)/sourceDyadicN n)=κ*(4:ℝ)^n := by
    unfold sourceDyadicN
    have hN : (2:ℝ)^(4*n)=((2:ℝ)^(2*n))^2 := by rw [← pow_mul]; congr 1; omega
    have h4 : (4:ℝ)^n=(2:ℝ)^(2*n) := by rw [pow_mul]; norm_num
    rw [hN,h4]
    field_simp
  calc
    R ≤ κ*(4:ℝ)^n := hn
    _ = κ/((2:ℝ)^(2*n)/sourceDyadicN n) := he.symm
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left hκ.le (div_pos (by positivity) (sourceDyadicN_pos n))
      exact div_le_div_of_nonneg_right hp (sourceDyadicN_pos n).le

end SourceDyadicArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ObservableDistance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ObservableDistance
open Classical MeasureTheory Set

theorem boundedObservable_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (hb : ∀x,f x∈Icc (0:ℝ) 1) : Integrable f μ := by
  apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2

theorem ObservableClose.mono {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {ε δ : ℝ} (h : ObservableClose μ ν ε) (he : ε ≤ δ) :
    ObservableClose μ ν δ := fun f hf hb => (h f hf hb).trans he

theorem ObservableClose.map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} {ε : ℝ} (h : ObservableClose μ ν ε) {g : X → Y} (hg : Measurable g) :
    ObservableClose (μ.map g) (ν.map g) ε := by
  intro f hf hb
  rw [integral_map hg.aemeasurable hf.aestronglyMeasurable,
    integral_map hg.aemeasurable hf.aestronglyMeasurable]
  exact h (f ∘ g) (hf.comp hg) (fun x => hb (g x))

theorem ObservableClose.prod_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] {ε : ℝ} (h : ObservableClose μ ν ε) :
    ObservableClose (μ.prod ρ) (ν.prod ρ) ε := by
  intro f hf hb
  have hiμ := boundedObservable_integrable (μ.prod ρ) hf hb
  have hiν := boundedObservable_integrable (ν.prod ρ) hf hb
  rw [integral_prod f hiμ,integral_prod f hiν]
  apply h (fun x => ∫y,f (x,y) ∂ρ)
  · have hh : StronglyMeasurable (Function.uncurry (fun (x : X) (y : Y) => f (x,y))) :=
      hf.stronglyMeasurable
    exact hh.integral_prod_right.measurable
  · intro x
    refine ⟨integral_nonneg (fun y => (hb (x,y)).1),?_⟩
    have hi := boundedObservable_integrable ρ (hf.comp (measurable_const.prodMk measurable_id))
      (fun y => hb (x,y))
    calc
      _ ≤ ∫_ : Y,(1:ℝ) ∂ρ := integral_mono hi (integrable_const 1) (fun y => (hb (x,y)).2)
      _ = 1 := by simp

end ObservableDistance

section InfiniteSplit
open Classical MeasureTheory Set

theorem infinitePi_split {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : ι → Prop) :
    ((Measure.infinitePi (fun _ : Subtype p => μ)).prod
      (Measure.infinitePi (fun _ : Subtype (fun i => ¬p i) => μ))).map
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p).symm=
      Measure.infinitePi (fun _ : ι => μ) := by
  apply Measure.eq_infinitePi
  intro s t ht
  let e := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p).symm
  rw [Measure.map_apply e.measurable (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have he (x : (Subtype p → X) × (Subtype (fun i => ¬p i) → X)) (i : ι) :
      e x i=(if h : p i then x.1 ⟨i,h⟩ else x.2 ⟨i,h⟩) := rfl
  have hpre : (e : _ → _) ⁻¹' ((s : Set ι).pi t)=
      ((s.subtype p : Set (Subtype p)).pi (fun i => t i.val)) ×ˢ
      ((s.subtype (fun i => ¬p i) : Set (Subtype (fun i => ¬p i))).pi (fun i => t i.val)) := by
    ext x
    simp only [mem_preimage,mem_pi,Finset.mem_coe,mem_prod,Finset.mem_subtype]
    constructor
    · intro h
      constructor
      · intro i hi
        simpa only [he,dite_eq_left i.property] using h i.val hi
      · intro i hi
        simpa only [he,dite_eq_right i.property] using h i.val hi
    · rintro ⟨h₁,h₂⟩ i hi
      by_cases hp : p i
      · simpa only [he,dite_eq_left hp] using h₁ ⟨i,hp⟩ hi
      · simpa only [he,dite_eq_right hp] using h₂ ⟨i,hp⟩ hi
  rw [hpre,Measure.prod_prod,Measure.infinitePi_pi (fun _ : Subtype p => μ) (fun i _ => ht i.val),
    Measure.infinitePi_pi (fun _ : Subtype (fun i => ¬p i) => μ) (fun i _ => ht i.val)]
  rw [Finset.prod_subtype_eq_prod_filter (s:=s) (p:=p) (fun i => μ (t i)),
    Finset.prod_subtype_eq_prod_filter (s:=s) (p:=fun i => ¬p i) (fun i => μ (t i))]
  exact Finset.prod_filter_mul_prod_filter_not s p (fun i => μ (t i))

end InfiniteSplit

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TentMatrixPositivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TentMatrixPositivity
open Classical MeasureTheory

theorem integral_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → Matrix ι ι ℝ) (hA : ∀ᵐ ω∂μ,(A ω).PosSemidef)
    (hi : ∀i j,Integrable (fun ω => A ω i j) μ) :
    Matrix.PosSemidef (fun i j => ∫ω,A ω i j ∂μ) := by
  refine ⟨?_,fun x => ?_⟩
  · ext i j
    change star (∫ω,A ω j i ∂μ)=∫ω,A ω i j ∂μ
    simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [hA] with ω hω
    have he := congrFun (congrFun hω.isHermitian i) j
    simpa using he
  · have hi' (i j : ι) : Integrable (fun ω => x i*A ω i j*x j) μ :=
      ((hi i j).const_mul _).mul_const _
    have he : (∫ω,x.sum (fun i xi => x.sum (fun j xj => star xi*A ω i j*xj)) ∂μ)=
        x.sum (fun i xi => x.sum (fun j xj => star xi*(∫ω,A ω i j ∂μ)*xj)) := by
      simp only [star_trivial,Finsupp.sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi' i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi' i j)]
      simp only [integral_mul_const,integral_const_mul]
    rw [← he]
    apply integral_nonneg_of_ae
    filter_upwards [hA] with ω hω
    exact hω.2 x

theorem intervalMark_mul (x y : ℝ) :
    (fun t => intervalMark x t*intervalMark y t)=
      (Set.Icc (max x y) (min (x+1) (y+1))).indicator (fun _ => (1:ℝ)) := by
  funext t
  have hm : t∈Set.Icc (max x y) (min (x+1) (y+1)) ↔
      t∈Set.Icc x (x+1) ∧ t∈Set.Icc y (y+1) := by
    simp only [Set.mem_Icc,max_le_iff,le_min_iff]
    tauto
  by_cases hx : t∈Set.Icc x (x+1) <;> by_cases hy : t∈Set.Icc y (y+1) <;>
    simp [intervalMark,Set.indicator,hm,hx,hy]

theorem intervalMark_mul_integrable (x y : ℝ) :
    Integrable (fun t => intervalMark x t*intervalMark y t) := by
  rw [intervalMark_mul]
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

theorem tent_eq_intervalMark_integral (x y : ℝ) :
    max (1-|x-y|) 0=∫t,intervalMark x t*intervalMark y t := by
  rw [intervalMark_mul,integral_indicator_const 1 measurableSet_Icc]
  simp only [smul_eq_mul,mul_one,Real.volume_real_Icc]
  congr 1
  rcases le_total x y with h|h
  · rw [max_eq_right h,min_eq_left (by linarith),abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h,min_eq_right (by linarith),abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem real_rankOne_posSemidef {ι : Type*} (a : ι → ℝ) :
    Matrix.PosSemidef (fun i j => a i*a j) := by
  refine ⟨?_,fun x => ?_⟩
  · ext i j
    change a j*a i=a i*a j
    exact mul_comm _ _
  · calc
      0≤(x.sum (fun i xi => xi*a i))^2 := sq_nonneg _
      _=x.sum (fun i xi => x.sum (fun j xj => star xi*(a i*a j)*xj)) := by
        simp only [pow_two,Finsupp.sum,Finset.sum_mul,Finset.mul_sum,star_trivial]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem tentMatrix_posSemidef {ι : Type*} (x : ι → ℝ) :
    Matrix.PosSemidef (fun i j => max (1-|x i-x j|) 0) := by
  have hp (t : ℝ) : Matrix.PosSemidef (fun i j => intervalMark (x i) t*intervalMark (x j) t) :=
    real_rankOne_posSemidef _
  have h := integral_posSemidef volume
    (fun t i j => intervalMark (x i) t*intervalMark (x j) t)
    (Filter.Eventually.of_forall hp) (fun i j => intervalMark_mul_integrable (x i) (x j))
  simpa only [← tent_eq_intervalMark_integral] using h

theorem planeTentMatrix_posSemidef {ι : Type*} (x : ι → ℝ×ℝ) (s : ℝ) :
    Matrix.PosSemidef (fun i j => max (1-|(x i).1/s-(x j).1/s|) 0 *
      max (1-|(x i).2/s-(x j).2/s|) 0) := by
  exact (tentMatrix_posSemidef (fun i => (x i).1/s)).hadamard
    (tentMatrix_posSemidef (fun i => (x i).2/s))

end TentMatrixPositivity

section FlagSeparatorMatrices
open Classical MeasureTheory

theorem measurableSet_flagChamber_eq {a : ℕ} {v : ℝ×ℝ} (z w : SquareFlag a v) :
    MeasurableSet {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w} := by
  have he : {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w}=
      ⋂l : Fin 4 × CutRing, {t | flagChamber t z l=flagChamber t w l} := by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact funext_iff
  rw [he]
  apply MeasurableSet.iInter
  intro l
  by_cases hz : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ z <;>
    by_cases hw : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ w
  · simp only [flagChamber,hz,hw,decide_true,Set.ofPred_true]
    exact MeasurableSet.univ
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simp only [flagChamber,hz,hw,decide_false,ite_self,Set.ofPred_true]
    exact MeasurableSet.univ

theorem equalityMatrix_posSemidef {ι κ : Type*} (f : ι → κ) :
    Matrix.PosSemidef (fun i j => if f i=f j then (1:ℝ) else 0) := by
  have h := (Matrix.PosSemidef.one (n := κ) (R := ℝ)).submatrix f
  have he : (1 : Matrix κ κ ℝ).submatrix f f=(fun i j => if f i=f j then 1 else 0) := by
    funext i j
    exact Matrix.one_apply (α := ℝ) (n := κ) (i := f i) (j := f j)
  rw [he] at h
  exact h

theorem separatorMatrix_integrand_integrable {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ] (z w : SquareFlag a v) :
    Integrable (fun t => if flagChamber t z=flagChamber t w then (1:ℝ) else 0) μ := by
  exact (integrable_indicator_iff (measurableSet_flagChamber_eq z w)).mpr integrableOn_const

theorem separatorMatrix_posSemidef {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ] :
    Matrix.PosSemidef (separatorMatrix (a:=a) (v:=v) μ) := by
  apply integral_posSemidef
  · exact Filter.Eventually.of_forall fun t => equalityMatrix_posSemidef (flagChamber t)
  · exact separatorMatrix_integrand_integrable μ

theorem thresholdLaw_isProbability {s κ : ℝ} (hs : 0 < s) (hκ : 0<κ) :
    IsProbabilityMeasure (thresholdLaw s κ) := by
  have hlt : κ/s<2*κ/s := by exact (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (κ/s) (2*κ/s))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hlt))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  unfold thresholdLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteOrthogonalEnergy
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SmoothNoise
open Classical MeasureTheory
open scoped ContDiff

theorem rawNoiseMass_pos : 0 < rawNoiseMass := by
  have hc : Continuous (fun x : ℝ => (rawNoiseBump x)^2) := rawNoiseBump.continuous.pow 2
  have hs : HasCompactSupport (fun x : ℝ => (rawNoiseBump x)^2) := by
    convert! rawNoiseBump.hasCompactSupport.mul_right (f':=rawNoiseBump) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [pow_two,Pi.mul_apply]
  apply integral_pos_of_integrable_nonneg_nonzero (x:=(0:ℝ)) hc (hc.integrable_of_hasCompactSupport hs)
    (fun _ => sq_nonneg _)
  have hh : rawNoiseBump (0 : ℝ)=1 := rawNoiseBump.one_of_mem_closedBall (by
    simp [rawNoiseBump])
  simp [hh]

theorem smoothNoiseRoot_contDiff : ContDiff ℝ ∞ smoothNoiseRoot :=
  rawNoiseBump.contDiff.div_const _

theorem smoothNoiseRoot_compact : HasCompactSupport smoothNoiseRoot := by
  convert! rawNoiseBump.hasCompactSupport.mul_right (f':=fun _ => (Real.sqrt rawNoiseMass)⁻¹) using 1
  all_goals try with_reducible_and_instances rfl

theorem smoothNoiseRoot_normalized : (∫x : ℝ,smoothNoiseRoot x^2)=1 := by
  simp only [smoothNoiseRoot,div_pow]
  rw [integral_div,Real.sq_sqrt rawNoiseMass_pos.le]
  change rawNoiseMass/rawNoiseMass=1
  exact div_self rawNoiseMass_pos.ne'

end SmoothNoise

section NoiseCenteredEnergy
open Classical MeasureTheory

theorem noiseEnergy_nonneg (f : ℝ → ℝ) (i : NoiseFactor) : 0≤noiseEnergy f i :=
  integral_nonneg (fun _ => sq_nonneg _)

end NoiseCenteredEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineNoiseEnergy
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineNoiseEnergy
open Classical MeasureTheory

theorem affineNoiseEnergyConstant_nonneg (f : ℝ → ℝ) : 0≤affineNoiseEnergyConstant f := by
  unfold affineNoiseEnergyConstant
  have := noiseEnergy_nonneg f .diagonal
  have := noiseEnergy_nonneg f .score
  have := noiseEnergy_nonneg f .position
  positivity

end AffineNoiseEnergy

section ActualNoiseLaw
open Classical MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal

instance smoothNoiseLaw_probability : IsProbabilityMeasure smoothNoiseLaw := by
  constructor
  rw [smoothNoiseLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hi : Integrable (fun x : ℝ => smoothNoiseRoot x^2) := by
    have hc := smoothNoiseRoot_contDiff.continuous.pow 2
    apply hc.integrable_of_hasCompactSupport
    convert! smoothNoiseRoot_compact.mul_right (f':=smoothNoiseRoot) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.mul_apply,pow_two]
  change (∫⁻x : ℝ,ENNReal.ofReal (smoothNoiseRoot x^2))=1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _)),
    smoothNoiseRoot_normalized,ENNReal.ofReal_one]

instance independentSmoothNoiseLaw_probability (ι : Type*) :
    IsProbabilityMeasure (independentSmoothNoiseLaw ι) := by
  unfold independentSmoothNoiseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end ActualNoiseLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagAveragingMatrices
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagAveragingMatrices
open Classical MeasureTheory

theorem planeTent_posSemidef {ι : Type*} (s : ℝ) (x : ι → ℝ×ℝ) :
    Matrix.PosSemidef (fun i j => planeTent s (x i) (x j)) := by
  simpa only [planeTent,sub_div] using planeTentMatrix_posSemidef x s

theorem flagAveragingMatrix_posSemidef {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N)
    (hr : 0 < r) (hκ : 0 < κ) :
    (flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ N r η κ).PosSemidef := by
  classical
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  have hcut := (real_rankOne_posSemidef (fun z : FlagSite a m D v => χ (scaledSiteConjugate N z))).smul
    (show 0 ≤ (ρ*(r*η)^2)⁻¹ from inv_nonneg.mpr (mul_nonneg hρ.le (sq_nonneg _)))
  have hsep := (separatorMatrix_posSemidef (a:=a) (v:=v) (thresholdLaw (r/N) κ)).submatrix
    (fun z : FlagSite a m D v => z.val.2)
  have htrack := equalityMatrix_posSemidef (fun z : FlagSite a m D v => z.val.1)
  let M : Matrix (FlagSite a m D v) (FlagSite a m D v) ℝ :=
    Matrix.hadamard (Matrix.hadamard (Matrix.hadamard (Matrix.hadamard
      ((ρ*(r*η)^2)⁻¹ • (fun (z w : FlagSite a m D v) =>
        χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)))
      (fun z w => planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)))
      (fun z w => planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w)))
      (Matrix.submatrix (separatorMatrix (a:=a) (v:=v) (thresholdLaw (r/N) κ))
        (fun z : FlagSite a m D v => z.val.2) (fun z : FlagSite a m D v => z.val.2)))
      (fun z w => @ite ℝ (z.val.1=w.val.1) (Classical.propDecidable _) 1 0)
  have h : M.PosSemidef :=
    (((hcut.hadamard (planeTent_posSemidef (r/N) flagSiteOrdinary)).hadamard
      (planeTent_posSemidef (N*η) flagSiteConjugate)).hadamard hsep).hadamard htrack
  have he : flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ N r η κ = M := by
    ext z w
    dsimp only [flagAveragingMatrix, M, Matrix.hadamard, Matrix.submatrix, Matrix.of, Equiv.refl, DFunLike.coe, EquivLike.toFunLike, Equiv.instEquivLike, EquivLike.coe, Matrix, id]
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [he]
  exact h

theorem flagAveragingMatrix_cutoff_left {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : χ (scaledSiteConjugate N z)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hz]

theorem flagAveragingMatrix_cutoff_right {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hw : χ (scaledSiteConjugate N w)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hw]

end FlagAveragingMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagSignalEnergy
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagSignalEnergy
open Classical

theorem flagMeanSignal_outside {a m D : ℕ} {v : ℝ×ℝ}
    (θ : (ℝ×ℝ) → ℝ) {q K N : ℝ} (hN : 0<N)
    (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (z : FlagSite a m D v)
    (hz : z∉flagSiteBox (N*K)) : flagMeanSignal θ N z=q := by
  apply hcompact
  by_contra hh
  have hh' : ‖scaledSiteConjugate N z‖<K := lt_of_not_ge hh
  have h₁ := norm_fst_le (scaledSiteConjugate N z)
  have h₂ := norm_snd_le (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at h₁ h₂
  apply hz
  constructor
  · have h := (div_lt_iff₀ hN).mp (h₁.trans_lt hh'); nlinarith
  · have h := (div_lt_iff₀ hN).mp (h₂.trans_lt hh'); nlinarith

end FlagSignalEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalGoodRows
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SignalActiveBox
open Classical

theorem flagAveragingMatrix_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {L N : ℝ} (hL : 0<L) (hN : 0<N)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) (ρ r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : z∉flagBoxFinset hD (mul_pos hN hL) ∨ w∉flagBoxFinset hD (mul_pos hN hL)) :
    flagAveragingMatrix χ ρ N r η κ z w=0 := by
  rcases hz with hz | hw
  · exact flagAveragingMatrix_cutoff_left χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc z (by simpa only [mem_flagBoxFinset] using hz))
  · exact flagAveragingMatrix_cutoff_right χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc w (by simpa only [mem_flagBoxFinset] using hw))

end SignalActiveBox

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonApproxIdentity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteResolvent
open Classical Matrix

theorem finiteL2Norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ finiteL2Norm x := norm_nonneg _

end FiniteResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CompactSignalEnergy
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SourceSignalScales
open Classical Filter
open scoped Topology

theorem sourceDyadicWeight_nonneg (n : ℕ) : 0 ≤ sourceDyadicWeight n :=
  Real.rpow_nonneg (Real.log_nonneg (sourceDyadicN_one_le n)) _

end SourceSignalScales

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CovarianceLimit
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceCovarianceLimit
open Classical Filter
open scoped Topology

theorem sourceFlagMatrix_covariance {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|))
    (T : ℕ → Finset (FlagSite a m D v × FlagSite a m D v)) :
    Tendsto (fun n => ∑p∈T n,(sourceFlagMatrix χ ρ η κ n p.1 p.2-
      sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g p.1) (flagSiteAction hD g p.2))^2)
      atTop (nhds 0) := by
  obtain ⟨R,C,hR,hC,he⟩ := flagMatrixDifference_dyadic_energy (v:=v) hD g χ hχ
    hK hcompact hL hρ hη hκ hLip
  have ht := sourceDyadicWeight_energy_tendsto.const_mul (4*C)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) _ ht
  filter_upwards [sourceDyadic_fine_eventually R hκ] with n hn
  have h := he (sourceDyadicN n) (sourceDyadicN_one_le n) (sourceDyadicIndices n) hn
    (sourceDyadicWeight n) (T n)
  simpa only [sourceFlagMatrix,flagMatrixDifference,Finset.sum_sub_distrib,mul_sub,mul_assoc] using h

end SourceCovarianceLimit

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseContinuity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section CovarianceResolvent
open Classical Matrix

theorem matrixHSNorm_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    0≤ matrixHSNorm A := Real.sqrt_nonneg _

end CovarianceResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_HellingerDistance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteAffineLaw
open Classical MeasureTheory Matrix Set
open scoped ENNReal

instance finiteAffineNoiseLaw_probability {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) : IsProbabilityMeasure (finiteAffineNoiseLaw A a) := by
  unfold finiteAffineNoiseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FiniteAffineLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteLawDistance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteField
open Classical Matrix MeasureTheory

theorem finiteCoefficientField_measurable {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) : Measurable (finiteCoefficientField J a B) := by
  apply Measurable.of_eval
  intro z
  exact (measurable_const.add (measurable_pi_apply z)).add
    (Finset.measurable_sum _ (fun w _ => measurable_const.mul (measurable_pi_apply w)))

theorem joinedNoiseField_measurable {ι : Type*} (J : Finset ι) (q : ℝ) :
    Measurable (joinedNoiseField J q) := by
  apply Measurable.of_eval
  intro z
  by_cases hz : z∈J
  · simpa only [joinedNoiseField,dite_eq_left hz,Function.comp_def] using
      (measurable_pi_apply (⟨z,hz⟩ : J)).comp measurable_fst
  · simp only [joinedNoiseField,dite_eq_right hz]
    fun_prop

theorem finiteCoefficientField_law {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (q : ℝ)
    (ha : ∀z,z∉J → a z=q) (hB : ∀z,z∉J → ∀w,B z w=0) :
    (independentSmoothNoiseLaw ι).map (finiteCoefficientField J a B)=
      ((finiteAffineNoiseLaw (1+(B.submatrix (fun z : J => z.val) (fun z : J => z.val)))
        (fun z : J => a z)).prod (independentSmoothNoiseLaw {z : ι // z∉J})).map
          (joinedNoiseField J q) := by
  let e := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun z => z∈J)).symm
  have hsplit : (independentSmoothNoiseLaw ι)=
      ((independentSmoothNoiseLaw J).prod (independentSmoothNoiseLaw {z : ι // z∉J})).map e := by
    convert! (infinitePi_split smoothNoiseLaw (fun z => z∈J)).symm using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    apply MeasurableEquiv.ext
    funext x
    funext z
    by_cases hz : z∈J <;> simp [e,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,hz]
  rw [hsplit,Measure.map_map (finiteCoefficientField_measurable J a B) e.measurable]
  let A : Matrix J J ℝ := 1+B.submatrix (fun z : J => z.val) (fun z : J => z.val)
  let f : (J → ℝ) → (J → ℝ) := fun x => (fun z : J => a z)+A*ᵥx
  have hf : Measurable f := by fun_prop
  change _=((independentSmoothNoiseLaw J).map f |>.prod
    (independentSmoothNoiseLaw {z : ι // z∉J})).map (joinedNoiseField J q)
  have hid : (independentSmoothNoiseLaw {z : ι // z∉J}).map id=
      independentSmoothNoiseLaw {z : ι // z∉J} := Measure.map_id
  conv_rhs => rw [← hid]
  rw [Measure.map_prod_map _ _ hf measurable_id,
    Measure.map_map (joinedNoiseField_measurable J q) (hf.prodMap measurable_id)]
  congr 1
  ext x z
  have he (w : ι) : e x w=(if hw : w∈J then x.1 ⟨w,hw⟩ else x.2 ⟨w,hw⟩) := rfl
  have hs : (∑w : J,B z w*x.1 w)=∑w∈J,B z w*e x w := by
    rw [← Finset.sum_coe_sort J (fun w => B z w*e x w)]
    apply Finset.sum_congr rfl
    intro w _
    rw [he,dite_eq_left w.property]
  by_cases hz : z∈J
  · change a z+e x z+(∑w∈J,B z w*e x w)=joinedNoiseField J q (f x.1,x.2) z
    simp only [joinedNoiseField,dite_eq_left hz,f,A,Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply]
    change a z+e x z+(∑w∈J,B z w*e x w)=a z+(x.1 ⟨z,hz⟩+∑w : J,B z w*x.1 w)
    rw [hs,he,dite_eq_left hz,add_assoc]
  · simp only [Function.comp_apply,finiteCoefficientField,joinedNoiseField,dite_eq_right hz,
      Prod.map_snd,id_eq,he,ha z hz,hB z hz,zero_mul,Finset.sum_const_zero,add_zero]

end FiniteField

section WholeFieldDistance
open Classical Matrix MeasureTheory

theorem finiteCoefficientField_close {ι : Type*} (J : Finset ι)
    (a b : ι → ℝ) (B C : Matrix ι ι ℝ) (q : ℝ)
    (ha : ∀z,z∉J → a z=q) (hb : ∀z,z∉J → b z=q)
    (hBr : ∀z,z∉J → ∀w,B z w=0) (hCr : ∀z,z∉J → ∀w,C z w=0)
    (hB : B.PosSemidef) (hC : C.PosSemidef) :
    ObservableClose
      ((independentSmoothNoiseLaw ι).map (finiteCoefficientField J a B))
      ((independentSmoothNoiseLaw ι).map (finiteCoefficientField J b C))
      (smoothNoiseTransportError (B.submatrix (fun z : J => z.val) (fun z : J => z.val))
        (C.submatrix (fun z : J => z.val) (fun z : J => z.val))
        (fun z : J => b z-a z)) := by
  rw [finiteCoefficientField_law J a B q ha hBr,finiteCoefficientField_law J b C q hb hCr]
  have hh := finiteAffineNoiseLaw_close
    (B.submatrix (fun z : J => z.val) (fun z : J => z.val))
    (C.submatrix (fun z : J => z.val) (fun z : J => z.val))
    (hB.submatrix _) (hC.submatrix _) (fun z : J => a z) (fun z : J => b z-a z)
  have he : (fun z : J => a z)+(fun z : J => b z-a z)=(fun z : J => b z) := by ext z; simp
  rw [he] at hh
  convert! (hh.prod_right (independentSmoothNoiseLaw {z : ι // z∉J})).map
    (joinedNoiseField_measurable J q) using 1 <;> congr!

theorem smoothNoiseTransportConstant_pos : 0 < smoothNoiseTransportConstant := by
  unfold smoothNoiseTransportConstant
  positivity

theorem smoothNoiseTransportError_le {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) :
    smoothNoiseTransportError B C h ≤ smoothNoiseTransportConstant*
      (matrixHSNorm (C-B)+(1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh)) := by
  let d := matrixHSNorm (C-B)
  let v := (1+d)*finiteL2Norm ((1+B)⁻¹*ᵥh)
  have hd : 0≤d := matrixHSNorm_nonneg _
  have hv : 0≤v := mul_nonneg (by linarith) (finiteL2Norm_nonneg _)
  have hC := affineNoiseEnergyConstant_nonneg smoothNoiseRoot
  have hs : Real.sqrt (d^2+v^2) ≤ d+v := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  unfold smoothNoiseTransportError
  rw [Real.sqrt_mul hC]
  change 2*(Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot)*Real.sqrt (d^2+v^2))≤_
  calc
    _ ≤ (2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot))*(d+v) := by
      nlinarith [Real.sqrt_nonneg (affineNoiseEnergyConstant smoothNoiseRoot)]
    _ ≤ _ := by
      unfold smoothNoiseTransportConstant
      change _ ≤ (2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot)+1)*(d+v)
      nlinarith

end WholeFieldDistance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldHS
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceFieldHS
open Classical Filter Matrix
open scoped Topology

theorem sourceFlagMatrix_HS_tendsto {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|))
    (T : ℕ → Finset (FlagSite a m D v)) :
    Tendsto (fun n => matrixHSNorm (Matrix.of (fun (z w : T n) =>
      sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val)-
        sourceFlagMatrix χ ρ η κ n z.val w.val))) atTop (nhds 0) := by
  have hh := (sourceFlagMatrix_covariance hD g⁻¹ χ hχ hK hcompact hL hρ hη hκ hLip
    (fun n => (T n).product (T n))).sqrt
  rw [Real.sqrt_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  unfold matrixHSNorm
  congr 1
  change (∑z : T n,∑w : T n,(sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g⁻¹ z.val)
    (flagSiteAction hD g⁻¹ w.val)-sourceFlagMatrix χ ρ η κ n z.val w.val)^2)=_
  let f : FlagSite a m D v × FlagSite a m D v → ℝ := fun p =>
    (sourceFlagMatrix χ ρ η κ n p.1 p.2-sourceFlagMatrix χ ρ η κ n
      (flagSiteAction hD g⁻¹ p.1) (flagSiteAction hD g⁻¹ p.2))^2
  symm
  calc
    _ = ∑z∈T n,∑w∈T n,f (z,w) := by
      convert! Finset.sum_product (T n) (T n) f using 1
      all_goals try with_reducible_and_instances rfl
    _ = ∑z : T n,∑w : T n,f (z.val,w.val) := by
      rw [← Finset.sum_coe_sort (T n)]
      apply Finset.sum_congr rfl
      intro z _
      exact (Finset.sum_coe_sort (T n) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      exact sub_sq_comm _ _

end SourceFieldHS

section SmallTransportParameters
open Classical

theorem smallTransportParameters {M C₁ C₂ ε : ℝ} (hM : 0<M)
    (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) (hε : 0<ε) :
    ∃η κ δ d : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ 0<δ ∧ 0<d ∧
      ∀x y : ℝ,0≤x → x≤d → 0≤y → y≤C₁*η+C₂*Real.sqrt κ+δ →
        M*(x+(1+x)*y)<ε := by
  let t := ε/(8*M*(C₁+C₂+1))
  let d := min 1 (ε/(4*M))
  have ht : 0<t := by dsimp [t]; positivity
  have hd : 0<d := lt_min zero_lt_one (by positivity)
  refine ⟨min 1 t,t^2,t,d,lt_min zero_lt_one ht,min_le_left _ _,sq_pos_of_pos ht,ht,hd,?_⟩
  intro x y hx hxd hy hybound
  have hdx : x≤1 := hxd.trans (min_le_left _ _)
  have hdx' : x≤ε/(4*M) := hxd.trans (min_le_right _ _)
  have hmx : M*x≤ε/4 := by
    have hh := (le_div_iff₀ (show 0<4*M by positivity)).mp hdx'
    linarith
  have ht' : (C₁+C₂+1)*t=ε/(8*M) := by
    dsimp [t]
    field_simp
  have hy' : y≤ε/(8*M) := by
    rw [Real.sqrt_sq ht.le] at hybound
    calc
      y ≤ C₁*min 1 t+C₂*t+t := hybound
      _ ≤ C₁*t+C₂*t+t := by
        have hh := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) t) hC₁
        linarith
      _ = ε/(8*M) := by rw [← ht']; ring
  have hmy : M*y≤ε/8 := by
    have hh := (le_div_iff₀ (show 0<8*M by positivity)).mp hy'
    linarith
  have hprod : (1+x)*y≤2*y := mul_le_mul_of_nonneg_right (by linarith) hy
  have hf := mul_le_mul_of_nonneg_left hprod hM.le
  nlinarith

end SmallTransportParameters

section FiniteFieldCovariance
open Classical Matrix MeasureTheory

theorem fieldReindex_measurable {ι : Type*} (e : ι ≃ ι) : Measurable (fieldReindex e) :=
  Measurable.of_eval (fun z => measurable_pi_apply (e.symm z))

theorem independentSmoothNoiseLaw_reindex {ι : Type*} (e : ι ≃ ι) :
    (independentSmoothNoiseLaw ι).map (fieldReindex e)=independentSmoothNoiseLaw ι := by
  convert! Measure.infinitePi_map_piCongrLeft (fun _ : ι => smoothNoiseLaw) e using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x z
  simpa only [Equiv.apply_symm_apply,fieldReindex] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : ι => ℝ) e x (e.symm z)).symm

theorem finiteCoefficientField_enlarge {ι : Type*} (J T : Finset ι) (hJT : J⊆T)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (hcol : ∀z w,w∉J → B z w=0) :
    finiteCoefficientField T a B=finiteCoefficientField J a B := by
  ext x z
  unfold finiteCoefficientField
  congr 1
  exact (Finset.sum_subset hJT (fun w _ hw => by rw [hcol z w hw,zero_mul])).symm

theorem finiteCoefficientField_covariance {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (e : ι ≃ ι) :
    ((independentSmoothNoiseLaw ι).map (finiteCoefficientField J a B)).map (fieldReindex e)=
      (independentSmoothNoiseLaw ι).map
        (finiteCoefficientField (J.image e) (fun z => a (e.symm z))
          (fun z w => B (e.symm z) (e.symm w))) := by
  rw [Measure.map_map (fieldReindex_measurable e) (finiteCoefficientField_measurable J a B)]
  have he : fieldReindex e ∘ finiteCoefficientField J a B=
      finiteCoefficientField (J.image e) (fun z => a (e.symm z))
        (fun z w => B (e.symm z) (e.symm w)) ∘ fieldReindex e := by
    ext x z
    simp only [Function.comp_apply,fieldReindex,finiteCoefficientField]
    rw [Finset.sum_image]
    · simp only [Equiv.symm_apply_apply]
    · intro i _ j _ hh
      exact e.injective hh
  rw [he]
  have hh := Measure.map_map
    (finiteCoefficientField_measurable (J.image e) (fun z => a (e.symm z))
      (fun z w => B (e.symm z) (e.symm w))) (fieldReindex_measurable e)
      (μ:=independentSmoothNoiseLaw ι)
  rw [independentSmoothNoiseLaw_reindex] at hh
  exact hh.symm

end FiniteFieldCovariance

section SourceFieldLaw
open Classical Matrix MeasureTheory Filter
open scoped Topology

theorem sourceFlagMatrix_posSemidef {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) {ρ η κ : ℝ} (hρ : 0<ρ) (hκ : 0<κ) (n : ℕ) :
    (Matrix.of (sourceFlagMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ η κ n)).PosSemidef := by
  have hh := (Matrix.posSemidef_sum (sourceDyadicIndices n) (fun i _ =>
    flagAveragingMatrix_posSemidef (a:=a) (m:=m) (D:=D) (v:=v) (η:=η) χ hρ
      (sourceDyadicN_pos n) (show 0<(2:ℝ)^i by positivity) hκ)).smul (sourceDyadicWeight_nonneg n)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext z w
  simp only [Matrix.of_apply,sourceFlagMatrix,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]

theorem sourceFlagMatrix_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (hχc : ∀x,L≤‖x‖ → χ x=0)
    (ρ η κ : ℝ) (n : ℕ) (z w : FlagSite a m D v)
    (hz : z∉flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL) ∨
      w∉flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)) :
    sourceFlagMatrix χ ρ η κ n z w=0 := by
  unfold sourceFlagMatrix
  suffices (∑i∈sourceDyadicIndices n,flagAveragingMatrix χ ρ (sourceDyadicN n) ((2:ℝ)^i) η κ z w)=0 by rw [this,mul_zero]
  apply Finset.sum_eq_zero
  intro i _
  exact flagAveragingMatrix_box_support hD χ hL (sourceDyadicN_pos n) hχc _ _ _ _ z w hz

instance sourceSmoothFieldLaw_probability {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceSmoothFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n) := by
  unfold sourceSmoothFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (finiteCoefficientField_measurable _ _ _).aemeasurable

theorem sourceSmoothFieldLaw_as_common {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (ρ η κ : ℝ) (n : ℕ) :
    sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n=
      (independentSmoothNoiseLaw (FlagSite a m D v)).map
        (finiteCoefficientField (sourceCommonSites hD g hL n)
          (flagMeanSignal θ (sourceDyadicN n)) (Matrix.of (sourceFlagMatrix χ ρ η κ n))) := by
  unfold sourceSmoothFieldLaw
  congr 1
  symm
  apply finiteCoefficientField_enlarge
  · exact Finset.subset_union_left
  · intro z w hw
    exact sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n z w (Or.inr hw)

theorem sourceSmoothFieldLaw_transported {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (ρ η κ : ℝ) (n : ℕ) :
    (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map (fieldReindex (flagSitePermutation hD g))=
      (independentSmoothNoiseLaw (FlagSite a m D v)).map
        (finiteCoefficientField (sourceCommonSites hD g hL n)
          (fun z => flagMeanSignal θ (sourceDyadicN n) (flagSiteAction hD g⁻¹ z))
          (Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g⁻¹ z) (flagSiteAction hD g⁻¹ w)))) := by
  unfold sourceSmoothFieldLaw
  rw [finiteCoefficientField_covariance]
  congr 1
  symm
  apply finiteCoefficientField_enlarge
  · exact Finset.subset_union_right
  · intro z w hw
    apply sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n _ _
    right
    intro hm
    apply hw
    exact Finset.mem_image.mpr ⟨(flagSitePermutation hD g).symm w,hm,
      (flagSitePermutation hD g).apply_symm_apply w⟩

end SourceFieldLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_ThresholdField
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ThresholdField
open Classical MeasureTheory Set

theorem thresholdField_measurable {ι : Type*} : Measurable (@thresholdField ι) := by
  apply Measurable.of_eval
  intro z
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply z))
    measurable_const measurable_const

end ThresholdField

section SourceFieldClose
open Classical Matrix MeasureTheory

theorem sourceSmoothFieldLaw_close {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L ρ η κ : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (q : ℝ) (hθc : ∀x,L≤‖x‖ → θ x=q)
    (hρ : 0<ρ) (hκ : 0<κ) (n : ℕ) :
    let T := sourceCommonSites (v:=v) hD g hL n
    let B : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n z.val w.val)
    let C : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n
      (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val))
    ObservableClose (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n)
      ((sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map (fieldReindex (flagSitePermutation hD g)))
      (smoothNoiseTransportError B C (fun z : T => flagSignalDifference hD g θ (sourceDyadicN n) z.val)) := by
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos (sourceDyadicN_pos n) hL)
  let T := sourceCommonSites (v:=v) hD g hL n
  let e := flagSitePermutation (v:=v) hD g
  have hout (z : FlagSite a m D v) (hz : z∉T) : z∉J :=
    fun hh => hz (Finset.mem_union_left _ hh)
  have hinv (z : FlagSite a m D v) (hz : z∉T) : e.symm z∉J := by
    intro hh
    apply hz
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.symm z,hh,e.apply_symm_apply z⟩)
  have hmean (z : FlagSite a m D v) (hz : z∉J) : flagMeanSignal θ (sourceDyadicN n) z=q :=
    flagMeanSignal_outside θ (sourceDyadicN_pos n) hθc z (by simpa only [J,mem_flagBoxFinset] using hz)
  have hrow (z : FlagSite a m D v) (hz : z∉J) (w : FlagSite a m D v) :
      sourceFlagMatrix χ ρ η κ n z w=0 :=
    sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n z w (Or.inl hz)
  have hpsd := sourceFlagMatrix_posSemidef (a:=a) (m:=m) (D:=D) (v:=v) (η:=η) χ hρ hκ n
  rw [sourceSmoothFieldLaw_transported hD g θ χ hL hχc,
    sourceSmoothFieldLaw_as_common hD g θ χ hL hχc]
  convert! finiteCoefficientField_close T (flagMeanSignal θ (sourceDyadicN n))
    (fun z => flagMeanSignal θ (sourceDyadicN n) (e.symm z))
    (Matrix.of (sourceFlagMatrix χ ρ η κ n))
    ((Matrix.of (sourceFlagMatrix χ ρ η κ n)).submatrix e.symm e.symm) q
    (fun z hz => hmean z (hout z hz))
    (fun z hz => hmean (e.symm z) (hinv z hz))
    (fun z hz w => hrow z (hout z hz) w)
    (fun z hz w => hrow (e.symm z) (hinv z hz) (e.symm w))
    hpsd (hpsd.submatrix e.symm) using 1
  all_goals try with_reducible_and_instances rfl

end SourceFieldClose

section SourceBitField
open Classical MeasureTheory Filter Set
open scoped Topology

instance sourceBitFieldLaw_probability {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceBitFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n) := by
  unfold sourceBitFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map thresholdField_measurable.aemeasurable

end SourceBitField

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldSignalData
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FieldSignalData
open Classical Set
open scoped ContDiff

namespace FieldSignalData

instance realLaw_probability (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.IsProbabilityMeasure (S.realLaw (a:=a) (m:=m) (v:=v) hD η κ n) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure (sourceSmoothFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n))

instance bitLaw_probability (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.IsProbabilityMeasure (S.bitLaw (a:=a) (m:=m) (v:=v) hD η κ n) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure (sourceBitFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n))

end FieldSignalData
end FieldSignalData

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BitReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BitReindex
open Classical MeasureTheory

theorem bitReindex_measurable {ι : Type*} (e : ι ≃ ι) : Measurable (bitReindex e) :=
  Measurable.of_eval (fun z => measurable_pi_apply (e.symm z))

theorem thresholdField_transport {ι : Type*} (μ : Measure (ι → ℝ)) (e : ι ≃ ι) :
    (μ.map (fieldReindex e)).map thresholdField=
      (μ.map thresholdField).map (bitReindex e) := by
  rw [Measure.map_map thresholdField_measurable (fieldReindex_measurable e),
    Measure.map_map (bitReindex_measurable e) thresholdField_measurable]
  rfl

theorem ObservableClose.threshold_transport {ι : Type*} (μ : Measure (ι → ℝ))
    (e : ι ≃ ι) {ε : ℝ} (h : ObservableClose μ (μ.map (fieldReindex e)) ε) :
    ObservableClose (μ.map thresholdField) ((μ.map thresholdField).map (bitReindex e)) ε := by
  have hh := h.map thresholdField_measurable
  rw [thresholdField_transport] at hh
  exact hh

end BitReindex

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_TransportEstimate
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceTransportEstimate
open Classical Matrix MeasureTheory
attribute [local irreducible] sourceCommonSites flagBoxFinset

theorem smoothNoiseTransportError_le_decidable {ι : Type*} [Fintype ι] [H : DecidableEq ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) :
    smoothNoiseTransportError B C h ≤ smoothNoiseTransportConstant*
      (matrixHSNorm (C-B)+(1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh)) := by
  have he : H=Classical.decEq ι := Subsingleton.elim _ _
  cases he
  exact smoothNoiseTransportError_le B C h

theorem smoothNoiseTransportError_of_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) {d b : ℝ} (hd : 0≤d)
    (hh : matrixHSNorm (C-B)≤d) (hi : finiteL2Norm ((1+B)⁻¹*ᵥh)≤b) :
    smoothNoiseTransportError B C h≤ smoothNoiseTransportConstant*(d+(1+d)*b) := by
  apply (smoothNoiseTransportError_le_decidable B C h).trans
  apply mul_le_mul_of_nonneg_left _ smoothNoiseTransportConstant_pos.le
  exact add_le_add hh (mul_le_mul (add_le_add le_rfl hh) hi (finiteL2Norm_nonneg _)
    (add_nonneg zero_le_one hd))

theorem sourceSmoothFieldLaw_transportEstimate {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L ρ η κ : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (q : ℝ) (hθc : ∀x,L≤‖x‖ → θ x=q)
    (hρ : 0<ρ) (hκ : 0<κ) (n : ℕ) (d b : ℝ) (hd : 0≤d) :
    let T := sourceCommonSites (v:=v) hD g hL n
    let B : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n z.val w.val)
    let C : Matrix T T ℝ := Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n
      (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val))
    let h : T → ℝ := fun z => flagSignalDifference hD g θ (sourceDyadicN n) z.val
    matrixHSNorm (C-B) ≤ d → finiteL2Norm ((1+B)⁻¹*ᵥh) ≤ b →
    ObservableClose (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n)
      ((sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map
        (fieldReindex (flagSitePermutation hD g)))
      (smoothNoiseTransportConstant*(d+(1+d)*b)) := by
  intro T B C h hh hi
  have hc := sourceSmoothFieldLaw_close (v:=v) (η:=η) hD g θ χ hL hχc q hθc hρ hκ n
  exact hc.mono (smoothNoiseTransportError_of_bounds B C h hd hh hi)

end SourceTransportEstimate

section SourceTransportConstants
open Classical Matrix MeasureTheory Filter
open scoped Topology

theorem sourceSmoothFieldLaw_transport_constants {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L Λ : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0)
    (hΛ : 0≤Λ) (hLip : ∀x y,|χ x-χ y| ≤ Λ*(|x.1-y.1|+|x.2-y.2|)) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀δ d : ℝ,0<δ → 0<d → ∀ᶠn : ℕ in atTop,
      ObservableClose (sourceSmoothFieldLaw (v:=v) hD (fun x => q+ψ x) χ hL ((D:ℝ)^4/5) η κ n)
        ((sourceSmoothFieldLaw (v:=v) hD (fun x => q+ψ x) χ hL ((D:ℝ)^4/5) η κ n).map
          (fieldReindex (flagSitePermutation hD g)))
        (smoothNoiseTransportConstant*(d+(1+d)*(C₁*η+C₂*Real.sqrt κ+δ))) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hinv⟩ := sourceFlagMatrix_inverse_signal (v:=v) hD g ψ χ hψ hsψ q K L hL hKL hcompact hχ hχ₁ hχc
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro η hη hη₁ κ hκ δ d hδ hd
  have hD' : (0:ℝ)<D := by exact_mod_cast hD
  have hρ : 0<(D:ℝ)^4/5 := by positivity
  let T := sourceCommonSites (v:=v) hD g hL
  let B (n : ℕ) : Matrix (T n) (T n) ℝ := Matrix.of (fun z w =>
    sourceFlagMatrix χ ((D:ℝ)^4/5) η κ n z.val w.val)
  let C (n : ℕ) : Matrix (T n) (T n) ℝ := Matrix.of (fun z w =>
    sourceFlagMatrix χ ((D:ℝ)^4/5) η κ n (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val))
  let h (n : ℕ) : T n → ℝ := fun z => flagSignalDifference hD g (fun x => q+ψ x) (sourceDyadicN n) z.val
  have hhs : Tendsto (fun n => matrixHSNorm (C n-B n)) atTop (nhds 0) := by
    convert! sourceFlagMatrix_HS_tendsto hD g χ hχ hL hχc hΛ hρ hη hκ hLip T using 1
    all_goals try with_reducible_and_instances rfl
  filter_upwards [hinv η hη hη₁ κ hκ δ hδ,hhs.eventually_lt_const hd] with n hn hdn
  have hi : finiteL2Norm ((1+B n)⁻¹*ᵥh n)≤C₁*η+C₂*Real.sqrt κ+δ := by
    exact hn (T n) Finset.subset_union_left
  have hθc : ∀x,L≤‖x‖ → q+ψ x=q := by
    intro x hx
    rw [hcompact x (by linarith only [hx,hKL]),add_zero]
  exact sourceSmoothFieldLaw_transportEstimate (v:=v) (η:=η) hD g (fun x => q+ψ x) χ
    hL hχc q hθc hρ hκ n d (C₁*η+C₂*Real.sqrt κ+δ) hd.le hdn.le hi

end SourceTransportConstants

section SignalTransport
open Classical MeasureTheory Filter
open scoped Topology
namespace FieldSignalData

theorem realLaw_transport_constants (S : FieldSignalData)
    {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) (g : polygonFullGroup a m) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀δ d : ℝ,0<δ → 0<d → ∀ᶠn : ℕ in atTop,
      ObservableClose (S.realLaw (v:=v) hD η κ n)
        ((S.realLaw (v:=v) hD η κ n).map (fieldReindex (flagSitePermutation hD g)))
        (smoothNoiseTransportConstant*(d+(1+d)*(C₁*η+C₂*Real.sqrt κ+δ))) :=
  sourceSmoothFieldLaw_transport_constants hD g S.ψ S.χ S.smooth S.compact S.q S.K S.L S.Λ
    S.L_pos S.gap S.ψ_zero S.χ_range S.χ_one S.χ_zero S.Λ_nonneg S.χ_lipschitz

theorem bitLaw_transport_constants (S : FieldSignalData)
    {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D) (g : polygonFullGroup a m) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀δ d : ℝ,0<δ → 0<d → ∀ᶠn : ℕ in atTop,
      ObservableClose (S.bitLaw (v:=v) hD η κ n)
        ((S.bitLaw (v:=v) hD η κ n).map (bitReindex (flagSitePermutation hD g)))
        (smoothNoiseTransportConstant*(d+(1+d)*(C₁*η+C₂*Real.sqrt κ+δ))) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h⟩ := S.realLaw_transport_constants (v:=v) hD g
  refine ⟨C₁,C₂,hC₁,hC₂,fun η hη hη₁ κ hκ δ d hδ hd => ?_⟩
  filter_upwards [h η hη hη₁ κ hκ δ d hδ hd] with n hn
  exact hn.threshold_transport _ _

end FieldSignalData
end SignalTransport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_JointBitField
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section JointBitField
open Classical MeasureTheory Filter
open scoped Topology

instance jointBitFieldLaw_probability {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n) := by
  unfold jointBitFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem finiteSignalFields_transport_oai {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (F : Finset (polygonFullGroup a m))
    {ε : ℝ} (hε : 0<ε) :
    ∃η κ : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ ∀ᶠn : ℕ in atTop,∀g∈F,∀j,
      ObservableClose ((S j).bitLaw (v:=v j) hD η κ n)
        (((S j).bitLaw (v:=v j) hD η κ n).map (bitReindex (flagSitePermutation hD g))) ε := by
  choose C₁ C₂ hC₁ hC₂ ht using
    (fun i : Fin k×F => (S i.1).bitLaw_transport_constants (v:=v i.1) hD i.2.val)
  let A := ∑i,C₁ i
  let B := ∑i,C₂ i
  have hA : 0≤A := Finset.sum_nonneg (fun i _ => hC₁ i)
  have hB : 0≤B := Finset.sum_nonneg (fun i _ => hC₂ i)
  obtain ⟨η,κ,δ,d,hη,hη₁,hκ,hδ,hd,hsmall⟩ :=
    smallTransportParameters smoothNoiseTransportConstant_pos hA hB hε
  refine ⟨η,κ,hη,hη₁,hκ,?_⟩
  have hh : ∀ᶠn : ℕ in atTop,∀i : Fin k×F,
      ObservableClose ((S i.1).bitLaw (v:=v i.1) hD η κ n)
        (((S i.1).bitLaw (v:=v i.1) hD η κ n).map (bitReindex (flagSitePermutation hD i.2.val))) ε := by
    apply eventually_all.mpr
    intro i
    filter_upwards [ht i η hη hη₁ κ hκ δ d hδ hd] with n hn
    apply hn.mono
    have hi₁ : C₁ i≤A := Finset.single_le_sum (fun t _ => hC₁ t) (Finset.mem_univ i)
    have hi₂ : C₂ i≤B := Finset.single_le_sum (fun t _ => hC₂ t) (Finset.mem_univ i)
    have he : C₁ i*η+C₂ i*Real.sqrt κ+δ≤A*η+B*Real.sqrt κ+δ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hi₁ hη.le)
        (mul_le_mul_of_nonneg_right hi₂ (Real.sqrt_nonneg κ))) le_rfl
    exact (hsmall d (C₁ i*η+C₂ i*Real.sqrt κ+δ) hd.le le_rfl (add_nonneg (add_nonneg (mul_nonneg (hC₁ i) hη.le)
      (mul_nonneg (hC₂ i) (Real.sqrt_nonneg κ))) hδ.le) he).le
  filter_upwards [hh] with n hn g hg j
  exact hn (j,⟨g,hg⟩)

end JointBitField

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.finiteSignalFields_transport_oai := @OAI.SimpleAmenable.finiteSignalFields_transport_oai
