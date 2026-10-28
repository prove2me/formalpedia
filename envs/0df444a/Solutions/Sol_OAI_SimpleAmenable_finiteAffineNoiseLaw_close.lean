-- Prove2me | solution 1 for OAI.SimpleAmenable.finiteAffineNoiseLaw_close
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:49:16.102316+00:00
-- url     : https://prove2.me/submissions/ef420d03-e86b-46e2-b0b3-2604e422d767

import Mathlib
import Definitions.Def_OAIQ65Sa001
import Definitions.Def_OAIQ65Sa002
import Theorems.Thm_OAI_SimpleAmenable_noiseInterpolationDerivative_energy

section
-- module Solutions.OAIQ065_SA.Compat
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseTensor
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section NoiseTensor
open Classical MeasureTheory

theorem noiseTensor_inner {ι : Type*} [Fintype ι] (u v : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,noiseTensor u x*noiseTensor v x ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i,∫t : ℝ,u i t*v i t := by
  simp only [noiseTensor,← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i x => u i x*v i x)

theorem noiseTensor_integrable_inner {ι : Type*} [Fintype ι] (u v : ι → ℝ → ℝ)
    (h : ∀i,Integrable (fun t : ℝ => u i t*v i t)) :
    Integrable (fun x : ι → ℝ => noiseTensor u x*noiseTensor v x) (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  simpa only [noiseTensor,← Finset.prod_mul_distrib] using Integrable.fintype_prod h

theorem noiseTensor_energy {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,noiseTensor u x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i,∫t : ℝ,u i t^2 := by
  simpa only [pow_two] using noiseTensor_inner u u

end NoiseTensor

section NoiseMoments
open Classical MeasureTheory

theorem noiseFactor_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (i : NoiseFactor) :
    Continuous (noiseFactor f i) := by
  have hc := hf.continuous
  have hd := hf.continuous_deriv le_rfl
  cases i <;> dsimp [noiseFactor] <;> fun_prop

theorem noiseFactor_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (i : NoiseFactor) :
    HasCompactSupport (noiseFactor f i) := by
  cases i
  · exact hf
  · exact hf.deriv
  · exact hf.mul_left
  · have hh : HasCompactSupport (fun x => f x/2) := by
      convert! (hf.mul_right (f':=fun _ => (2:ℝ)⁻¹)) using 1
      all_goals try with_reducible_and_instances rfl
    exact hf.deriv.mul_left.add hh

theorem noiseFactor_integrable_product {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (i j : NoiseFactor) :
    Integrable (fun x => noiseFactor f i x*noiseFactor f j x) :=
  ((noiseFactor_continuous hf i).mul (noiseFactor_continuous hf j)).integrable_of_hasCompactSupport
    (noiseFactor_compact hc i).mul_right

end NoiseMoments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteOrthogonalEnergy
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

theorem smoothNoiseRoot_even : Function.Even smoothNoiseRoot := by
  intro x
  simp only [smoothNoiseRoot,rawNoiseBump.neg]

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

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineNoiseEnergy
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

theorem noise_centered_integrable_product {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s t : Finset ι) (p q : ι → NoiseFactor) :
    Integrable (fun x : ι → ℝ =>
      centeredNoiseTensor f s (fun i => noiseFactor f (p i)) x*
      centeredNoiseTensor f t (fun i => noiseFactor f (q i)) x)
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  apply noiseTensor_integrable_inner
  intro i
  split_ifs
  · exact noiseFactor_integrable_product hf hc _ _
  · exact noiseFactor_integrable_product hf hc (p i) .base
  · exact noiseFactor_integrable_product hf hc .base (q i)
  · exact noiseFactor_integrable_product hf hc .base .base

theorem integrable_sum_product {I J X : Type*} [Fintype I] [Fintype J] [MeasurableSpace X]
    (μ : Measure X) (f : I → X → ℝ) (g : J → X → ℝ)
    (h : ∀i j,Integrable (fun x => f i x*g j x) μ) :
    Integrable (fun x => (∑i,f i x)*(∑j,g j x)) μ := by
  simp only [Finset.sum_mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => h i j))

theorem noise_sum_integrable_product {ι I J : Type*} [Fintype ι] [Fintype I] [Fintype J]
  {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s : I → Finset ι) (t : J → Finset ι) (p : I → ι → NoiseFactor)
    (q : J → ι → NoiseFactor) (u : I → ℝ) (w : J → ℝ) :
    Integrable (fun x : ι → ℝ =>
      (∑i,u i*centeredNoiseTensor f (s i) (fun j => noiseFactor f (p i j)) x)*
      (∑i,w i*centeredNoiseTensor f (t i) (fun j => noiseFactor f (q i j)) x))
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  apply integrable_sum_product
  intro i j
  apply ((noise_centered_integrable_product hf hc (s i) (t j) (p i) (q j)).const_mul (u i*w j)).congr
  filter_upwards with x
  ring

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_MatrixDensityCalculus
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section MatrixDensityCalculus
open Classical Matrix

theorem matrix_hasDerivAt_det {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hunit : IsUnit (A t).det) :
    HasDerivAt (fun s => (A s).det) ((A t).det*Matrix.trace (A'*(A t)⁻¹)) t := by
  let M := A t
  let L := A'*M⁻¹
  have hmul : L*M=A' := by
    rw [mul_assoc,Matrix.nonsing_inv_mul _ hunit,mul_one]
  have hrow (i : ι) : A' i=∑j,L i j • M j := by
    ext k
    rw [← hmul]
    simp only [Matrix.mul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hd := (determinantMultilinear.hasFDerivAt (A t)).comp_hasDerivAt t hA
  have he : determinantMultilinear.linearDeriv (A t) A'=M.det*Matrix.trace L := by
    have hlin : determinantMultilinear.linearDeriv (A t) A'=
        ∑i,determinantMultilinear (Function.update (A t) i (A' i)) := by
      convert! ContinuousMultilinearMap.linearDeriv_apply determinantMultilinear
        (fun i j => A t i j) (fun i j => A' i j) using 1
      all_goals try with_reducible_and_instances rfl
    rw [hlin]
    calc
      _ = ∑i,(M.updateRow i (∑j,L i j • M j)).det := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hrow i]
        rfl
      _ = ∑i,L i i*M.det := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.det_updateRow_sum,smul_eq_mul]
      _ = M.det*Matrix.trace L := by
        simp only [Matrix.trace,Matrix.diag,Finset.mul_sum,mul_comm]
  rw [he] at hd
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl

end MatrixDensityCalculus

section AffineNoiseIdentity
open Classical Matrix

theorem singletonNoise_eq {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (q : NoiseFactor) (i : ι) (x : ι → ℝ) :
    singletonNoise f q i x=noiseFactor f q (x i)*∏j∈Finset.univ.erase i,f (x j) := by
  unfold singletonNoise centeredNoiseTensor noiseTensor
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (if j∈({i} : Finset ι) then
    (fun _ => noiseFactor f q) j else f) (x j)) (Finset.mem_univ i)]
  simp only [Finset.mem_singleton]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem singletonNoise_score {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (i : ι) (x : ι → ℝ) :
    singletonNoise f .score i x=noiseGradientCoordinate f i x := by
  rw [singletonNoise_eq]
  rfl

theorem singletonNoise_diagonal {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (i : ι) (x : ι → ℝ) :
    singletonNoise f .diagonal i x=
      x i*noiseGradientCoordinate f i x+noiseTensor (fun _ : ι => f) x/2 := by
  rw [singletonNoise_eq]
  unfold noiseFactor noiseGradientCoordinate noiseTensor
  rw [← Finset.mul_prod_erase Finset.univ (fun j => f (x j)) (Finset.mem_univ i)]
  ring

theorem pairNoise_gradient {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (p : NoisePair ι) (x : ι → ℝ) :
    pairNoise f p x=x p.val.2*noiseGradientCoordinate f p.val.1 x := by
  rw [← singletonNoise_score]
  unfold pairNoise singletonNoise centeredNoiseTensor noiseTensor
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p.val.2),
    ← Finset.mul_prod_erase Finset.univ (fun i => (if i∈({p.val.1} : Finset ι) then
      (fun _ => noiseFactor f .score) i else f) (x i)) (Finset.mem_univ p.val.2)]
  simp only [Finset.mem_insert,Finset.mem_singleton,or_true,ite_true,
    ite_eq_right (Ne.symm p.property),noiseFactor]
  have hp : (∏i∈Finset.univ.erase p.val.2,
      (if i∈({p.val.1,p.val.2} : Finset ι) then
        (fun i => noiseFactor f (if i=p.val.1 then .score else .position)) i else f) (x i))=
      ∏i∈Finset.univ.erase p.val.2,(if i=p.val.1 then deriv f else f) (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne := (Finset.mem_erase.mp hi).1
    by_cases he : i=p.val.1
    · simp [he,noiseFactor]
    · simp [he,hne]
  simp only [Finset.mem_insert,Finset.mem_singleton,noiseFactor] at hp
  rw [hp]
  ring

theorem affineNoiseGenerator_eq {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (L : Matrix ι ι ℝ) (v x : ι → ℝ) :
    affineNoiseGenerator f L v x=
      (∑i,((L*ᵥx) i+v i)*noiseGradientCoordinate f i x)+
      Matrix.trace L*noiseTensor (fun _ : ι => f) x/2 := by
  have hsplit : (∑i,L i i*x i*noiseGradientCoordinate f i x)+
      (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=
      ∑i,∑j,L i j*x j*noiseGradientCoordinate f i x := by
    have ho : (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=
      ∑i,∑j,if i≠j then L i j*x j*noiseGradientCoordinate f i x else 0 := by
      change (∑p : {p : ι×ι // p.1≠p.2},L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=_
      rw [← Finset.sum_subtype (Finset.univ.filter (fun p : ι×ι => p.1≠p.2)) (by simp)
        (fun p : ι×ι => L p.1 p.2*x p.2*noiseGradientCoordinate f p.1 x),Finset.sum_filter,
        Fintype.sum_prod_type]
    rw [ho,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (∑j,if i=j then L i j*x j*noiseGradientCoordinate f i x else 0)+
          (∑j,if i≠j then L i j*x j*noiseGradientCoordinate f i x else 0) := by simp
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp_all
  simp_rw [affineNoiseGenerator,singletonNoise_diagonal,singletonNoise_score,pairNoise_gradient]
  simp only [mul_add,Finset.sum_add_distrib]
  have ht : (∑i,L i i*(noiseTensor (fun _ : ι => f) x/2))=
      Matrix.trace L*noiseTensor (fun _ : ι => f) x/2 := by
    rw [← Finset.sum_mul]
    simp only [Matrix.trace,Matrix.diag]
    ring
  rw [ht]
  have hh : (∑p : NoisePair ι,L p.val.1 p.val.2*(x p.val.2*noiseGradientCoordinate f p.val.1 x))=
      ∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x := by
    simp only [mul_assoc]
  rw [hh]
  simp only [← mul_assoc] at hsplit ⊢
  rw [show (∑i,L i i*x i*noiseGradientCoordinate f i x)+
      Matrix.trace L*noiseTensor (fun _ : ι => f) x/2+
      (∑i,v i*noiseGradientCoordinate f i x)+
      (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x)=
      ((∑i,L i i*x i*noiseGradientCoordinate f i x)+
      (∑p : NoisePair ι,L p.val.1 p.val.2*x p.val.2*noiseGradientCoordinate f p.val.1 x))+
      (∑i,v i*noiseGradientCoordinate f i x)+Matrix.trace L*noiseTensor (fun _ : ι => f) x/2 by ring,
      hsplit]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,add_mul,Finset.sum_add_distrib]

theorem noiseTensor_hasDerivAt {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Differentiable ℝ f) {x : ℝ → ι → ℝ} {x' : ι → ℝ} {t : ℝ}
    (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => noiseTensor (fun _ : ι => f) (x s))
      (∑i,x' i*noiseGradientCoordinate f i (x t)) t := by
  have h (i : ι) := ((hf (x t i)).hasDerivAt).comp t ((hasDerivAt_pi.mp hx) i)
  convert! HasDerivAt.fun_finsetProd (fun i (_ : i∈Finset.univ) => h i) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  simp only [noiseGradientCoordinate,smul_eq_mul,Function.comp_apply]
  ring

end AffineNoiseIdentity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_MatrixInverseCalculus
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section MatrixInverseCalculus
open Classical Matrix Filter
open scoped Topology Matrix.Norms.Elementwise

theorem matrix_differentiableAt_det {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {t : ℝ} (hA : DifferentiableAt ℝ A t) :
    DifferentiableAt ℝ (fun s => (A s).det) t := by
  convert! (determinantMultilinear.hasFDerivAt (A t)).differentiableAt.comp t hA using 1
  all_goals try with_reducible_and_instances rfl

theorem matrix_differentiableAt_inverse {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {t : ℝ} (hA : DifferentiableAt ℝ A t)
    (hunit : IsUnit (A t).det) : DifferentiableAt ℝ (fun s => (A s)⁻¹) t := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have hAj : DifferentiableAt ℝ (fun s => (A s).adjugate i j) t := by
    simp only [Matrix.adjugate_apply]
    apply matrix_differentiableAt_det
    apply differentiableAt_pi.mpr
    intro k
    apply differentiableAt_pi.mpr
    intro l
    by_cases hk : k=j
    · subst k
      simpa only [Matrix.updateRow_self] using differentiableAt_const ((Pi.single i (1 : ℝ) : ι → ℝ) l)
    · simpa only [Matrix.updateRow_ne hk] using
        (differentiableAt_pi.mp (differentiableAt_pi.mp hA k) l)
  have hd := (matrix_differentiableAt_det hA).inv hunit.ne_zero
  convert! hd.mul hAj using 1
  all_goals try with_reducible_and_instances rfl
  ext s
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.inv_apply]

theorem matrix_hasDerivAt_mul {ι : Type*} [Fintype ι]
    {A B : ℝ → Matrix ι ι ℝ} {A' B' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s*B s) (A'*B t+A t*B') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h (k : ι) := ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i)) k).mul
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k)) j)
  convert! HasDerivAt.fun_sum (fun k (_ : k∈Finset.univ) => h k) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Matrix.add_apply,Matrix.mul_apply,Finset.sum_add_distrib]

theorem matrix_hasDerivAt_inverse {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hunit : IsUnit (A t).det) :
    HasDerivAt (fun s => (A s)⁻¹) (-(A t)⁻¹*A'*(A t)⁻¹) t := by
  have hd : HasDerivAt (fun s => (A s)⁻¹) (deriv (fun s => (A s)⁻¹) t) t := by
    apply DifferentiableAt.hasDerivAt
    convert! matrix_differentiableAt_inverse hA.differentiableAt hunit using 1
    all_goals try with_reducible_and_instances rfl
  let D := deriv (fun s => (A s)⁻¹) t
  have he : ∀ᶠs in 𝓝 t,A s*(A s)⁻¹=1 := by
    have hn := (matrix_differentiableAt_det hA.differentiableAt).continuousAt.eventually_ne hunit.ne_zero
    filter_upwards [hn] with s hs
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs)
  have hp := matrix_hasDerivAt_mul hA hd
  have hz : A'*(A t)⁻¹+A t*D=0 := by
    exact (hp.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)).unique (hasDerivAt_const t (1 : Matrix ι ι ℝ))
  have hm := congrArg (fun M : Matrix ι ι ℝ => (A t)⁻¹*M) hz
  have heq : D=-(A t)⁻¹*A'*(A t)⁻¹ := by
    simp only [Matrix.mul_add,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hunit,
      one_mul,mul_zero] at hm
    rw [neg_mul,neg_mul]
    exact eq_neg_of_add_eq_zero_right hm
  rw [← heq]
  exact hd

theorem matrix_hasDerivAt_mulVec {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {x : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {x' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => A s*ᵥx s) (A'*ᵥx t+A t*ᵥx') t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h (j : ι) := ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i)) j).mul
    ((hasDerivAt_pi.mp hx) j)
  convert! HasDerivAt.fun_sum (fun j (_ : j∈Finset.univ) => h j) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Pi.add_apply,Matrix.mulVec,dotProduct,Finset.sum_add_distrib]

end MatrixInverseCalculus

section AffineVolume
open Classical Matrix MeasureTheory
open scoped ENNReal

theorem matrixAffineEquiv_apply {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a x : ι → ℝ) (hA : IsUnit A.det) :
    matrixAffineEquiv A a hA x=a+A*ᵥx := by
  change a+Matrix.toLin (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι) A x=_
  rw [Matrix.toLin_eq_toLin',Matrix.toLin'_apply]

theorem matrixAffineEquiv_symm_apply {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a y : ι → ℝ) (hA : IsUnit A.det) :
    (matrixAffineEquiv A a hA).symm y=A⁻¹*ᵥ(y-a) := by
  apply (matrixAffineEquiv A a hA).injective
  rw [MeasurableEquiv.apply_symm_apply,matrixAffineEquiv_apply,
    Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hA,Matrix.one_mulVec]
  abel

theorem map_matrix_affine_volume {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    Measure.map (fun x => a+A*ᵥx) (volume : Measure (ι → ℝ))=
      ENNReal.ofReal |A.det⁻¹| • volume := by
  change Measure.map ((fun y => a+y) ∘ (Matrix.toLin' A)) volume=_
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    Real.map_matrix_volume_pi_eq_smul_volume_pi hA.ne_zero,
    Measure.map_smul,map_add_left_eq_self]

theorem integral_matrix_affine {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) (f : (ι → ℝ) → ℝ) :
    (∫x,f (a+A*ᵥx))=|A.det⁻¹| *(∫y,f y) := by
  have h := integral_map_equiv (μ := (volume : Measure (ι → ℝ)))
    (matrixAffineEquiv A a hA) f
  rw [show (matrixAffineEquiv A a hA : (ι → ℝ) → (ι → ℝ))=
    (fun x => a+A*ᵥx) from funext (fun x => matrixAffineEquiv_apply A a x hA),map_matrix_affine_volume A a hA,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul] at h
  exact h.symm

theorem integral_matrix_affine_inverse {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) (f : (ι → ℝ) → ℝ) :
    (∫y,f (A⁻¹*ᵥ(y-a)))=|A.det| *(∫x,f x) := by
  have h := integral_matrix_affine A⁻¹ (-(A⁻¹*ᵥa))
    (isUnit_iff_ne_zero.mpr (by rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; exact inv_ne_zero hA.ne_zero)) f
  convert! h using 1
  · congr 1
    ext y
    rw [Matrix.mulVec_sub]
    simp only [sub_eq_add_neg,add_comm]
  · rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,inv_inv]

end AffineVolume

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineDensityDerivative
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section AffineDensityDerivative
open Classical Matrix
open scoped Matrix.Norms.Elementwise

theorem inverse_affine_hasDerivAt {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {a : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {a' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (ha : HasDerivAt a a' t)
    (hunit : IsUnit (A t).det) (y : ι → ℝ) :
    HasDerivAt (fun s => (A s)⁻¹*ᵥ(y-a s))
      (-(((A t)⁻¹*A')*ᵥ((A t)⁻¹*ᵥ(y-a t))+(A t)⁻¹*ᵥa')) t := by
  have h := matrix_hasDerivAt_mulVec (matrix_hasDerivAt_inverse hA hunit)
    ((hasDerivAt_const t y).sub ha)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_sub,Matrix.mulVec_neg,Matrix.neg_mulVec,Matrix.mulVec_mulVec,
    neg_mul,neg_add_rev]
  abel

theorem inverse_sqrt_det_hasDerivAt {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hpos : 0<(A t).det) :
    HasDerivAt (fun s => (Real.sqrt (A s).det)⁻¹)
      (-(Real.sqrt (A t).det)⁻¹*Matrix.trace ((A t)⁻¹*A')/2) t := by
  have hd := matrix_hasDerivAt_det hA (isUnit_iff_ne_zero.mpr hpos.ne')
  have hs := (hd.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl
  rw [Matrix.trace_mul_comm A' (A t)⁻¹]
  have hh := Real.sq_sqrt hpos.le
  field_simp
  rw [hh]
  ring

theorem affineNoiseRoot_hasDerivAt {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {A : ℝ → Matrix ι ι ℝ} {a : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {a' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (ha : HasDerivAt a a' t)
    (hpos : 0<(A t).det) (y : ι → ℝ) :
    HasDerivAt (fun s => affineNoiseRoot f (A s) (a s) y)
      (-affineNoiseGenerator f ((A t)⁻¹*A') ((A t)⁻¹*ᵥa')
        ((A t)⁻¹*ᵥ(y-a t))/Real.sqrt (A t).det) t := by
  have hx := inverse_affine_hasDerivAt hA ha (isUnit_iff_ne_zero.mpr hpos.ne') y
  have hF := noiseTensor_hasDerivAt hf hx
  have hh := hF.mul (inverse_sqrt_det_hasDerivAt hA hpos)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [affineNoiseGenerator_eq]
  simp only [Pi.neg_apply,Pi.add_apply,neg_mul,Finset.sum_neg_distrib]
  ring

end AffineDensityDerivative

section AffineDensityEnergy
open Classical Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem affineNoiseRoot_normalized {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : (∫x : ℝ,f x^2)=1)
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hpos : 0<A.det) :
    (∫y : ι → ℝ,affineNoiseRoot f A a y^2)=1 := by
  simp only [affineNoiseRoot,div_pow,Real.sq_sqrt hpos.le]
  rw [integral_div,integral_matrix_affine_inverse A a
    (isUnit_iff_ne_zero.mpr hpos.ne') (fun x => noiseTensor (fun _ : ι => f) x^2)]
  have ht : (∫x : ι → ℝ,noiseTensor (fun _ : ι => f) x^2)=1 := by
    rw [show (volume : Measure (ι → ℝ))=Measure.pi (fun _ : ι => (volume : Measure ℝ)) from rfl,
      noiseTensor_energy]
    simp only [hf,Finset.prod_const_one]
  rw [ht,mul_one,abs_of_pos hpos,div_self hpos.ne']

end AffineDensityEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AffineIntegrability
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section AffineIntegrability
open Classical MeasureTheory Matrix

theorem integrable_matrix_affine {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (fun x => f (a+A*ᵥx)) := by
  have hm : Integrable f (Measure.map (matrixAffineEquiv A a hA) volume) := by
    rw [show (matrixAffineEquiv A a hA : (ι → ℝ) → (ι → ℝ))=
      (fun x => a+A*ᵥx) from funext (fun x => matrixAffineEquiv_apply A a x hA),
      map_matrix_affine_volume A a hA]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  convert! (integrable_map_equiv (matrixAffineEquiv A a hA) f).mp hm using 1
  all_goals try with_reducible_and_instances rfl

theorem integrable_matrix_affine_inverse {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (fun y => f (A⁻¹*ᵥ(y-a))) := by
  have h := integrable_matrix_affine A⁻¹ (-(A⁻¹*ᵥa))
    (isUnit_iff_ne_zero.mpr (by
      rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
      exact inv_ne_zero hA.ne_zero)) hf
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  rw [Matrix.mulVec_sub]
  simp only [sub_eq_add_neg,add_comm]

theorem affineNoiseRoot_integrable_square {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    Integrable (fun y : ι → ℝ => affineNoiseRoot f A a y^2) := by
  have ht : Integrable (fun x : ι → ℝ => noiseTensor (fun _ : ι => f) x^2) := by
    convert! noiseTensor_integrable_inner (fun _ : ι => f)
      (fun _ : ι => f) (fun _ => ((hf.mul hf).integrable_of_hasCompactSupport
        (hc.mul_right (f' := f)))) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [pow_two]
  simpa only [affineNoiseRoot,div_pow] using
    (integrable_matrix_affine_inverse A a hA ht).div_const ((Real.sqrt A.det)^2)

end AffineIntegrability

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ObservableDistance
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

theorem ObservableClose.mono {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {ε δ : ℝ} (h : ObservableClose μ ν ε) (he : ε ≤ δ) :
    ObservableClose μ ν δ := fun f hf hb => (h f hf hb).trans he

theorem ObservableClose.symm {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {ε : ℝ} (h : ObservableClose μ ν ε) :
    ObservableClose ν μ ε := by
  intro f hf hb
  rw [abs_sub_comm]
  exact h f hf hb

theorem observableClose_of_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p q : X → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hp₀ : ∀x,0 ≤ p x) (hq₀ : ∀x,0 ≤ q x)
    (hip : Integrable p μ) (hiq : Integrable q μ) :
    ObservableClose (μ.withDensity (fun x => ENNReal.ofReal (p x)))
      (μ.withDensity (fun x => ENNReal.ofReal (q x))) (∫x,|p x-q x| ∂μ) := by
  intro f hf hb
  have hb' : ∀ᵐx ∂μ,‖f x‖ ≤ (1:ℝ) := ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2)
  have hipf := hip.mul_bdd hf.aestronglyMeasurable hb'
  have hiqf := hiq.mul_bdd hf.aestronglyMeasurable hb'
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp₀ _),ENNReal.toReal_ofReal (hq₀ _),smul_eq_mul]
  rw [← integral_sub hipf hiqf]
  calc
    _ ≤ ∫x,|p x*f x-q x*f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono (hipf.sub hiqf).abs (hip.sub hiq).abs
      intro x
      change |p x*f x-q x*f x| ≤ |p x-q x|
      rw [← sub_mul,abs_mul,abs_of_nonneg (hb x).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb x).2

end ObservableDistance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonApproxIdentity
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem one_add_psd_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) : IsUnit (1+B).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.one.add_posSemidef hB).isUnit

end FiniteResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseContinuity
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section NoiseContinuity
open Classical Matrix MeasureTheory

@[fun_prop] theorem affineNoiseGenerator_continuous_comp {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {L : X → Matrix ι ι ℝ} {v x : X → ι → ℝ}
    (hL : Continuous L) (hv : Continuous v) (hx : Continuous x) :
    Continuous (fun z => affineNoiseGenerator f (L z) (v z) (x z)) := by
  simp only [affineNoiseGenerator_eq]
  have hF := (noiseTensor_continuous hf.continuous).comp hx
  have hg (i : ι) := (noiseGradientCoordinate_continuous hf i).comp hx
  unfold Matrix.trace Matrix.diag Matrix.mulVec dotProduct
  fun_prop

attribute [local instance] OAI.SimpleAmenable.instMeasurableSpaceMatrixReal_solutions
local instance instBorelSpaceMatrixRealOfFintype_solutions {ι : Type*} [Fintype ι] : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

theorem matrix_inverse_measurable {ι : Type*} [Fintype ι]
    {X : Type*} [MeasurableSpace X] {A : X → Matrix ι ι ℝ}
    (hA : Measurable A) : Measurable (fun x => (A x)⁻¹) := by
  have hd := continuous_id.matrix_det.measurable.comp hA
  have ha := continuous_id.matrix_adjugate.measurable.comp hA
  simp only [Matrix.inv_def,Ring.inverse_eq_inv]
  exact hd.inv.smul ha

theorem matrix_inverse_continuousAt {ι : Type*} [Fintype ι]
    {X : Type*} [TopologicalSpace X] {A : X → Matrix ι ι ℝ} {x : X}
    (hA : ContinuousAt A x) (hn : (A x).det≠0) : ContinuousAt (fun y => (A y)⁻¹) x := by
  apply (continuousAt_matrix_inv (A x) ?_).comp hA
  convert! (continuousAt_inv₀ hn) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact Ring.inverse_eq_inv x

end NoiseContinuity

section CovarianceResolvent
open Classical Matrix

theorem covarianceSegment_posSemidef {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) : (covarianceSegment B C t).PosSemidef :=
  (hB.smul (sub_nonneg.mpr ht.2)).add (hC.smul ht.1)

theorem covarianceSegment_affine {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (t : ℝ) : 1+covarianceSegment B C t=(1+B)+t • (C-B) := by
  unfold covarianceSegment
  module

end CovarianceResolvent

section RootPathEnergy
open Classical MeasureTheory Set

theorem square_integral_le_integral_square {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ) :
    (∫x,f x ∂μ)^2≤∫x,f x^2 ∂μ := by
  let c := ∫x,f x ∂μ
  have hz : 0≤∫x,(f x)^2-2*c*f x+c^2 ∂μ := by
    apply integral_nonneg
    intro x
    change (0:ℝ)≤f x^2-2*c*f x+c^2
    nlinarith [sq_nonneg (f x-c)]
  have hs : Integrable (fun x => f x^2-2*c*f x) μ := hf2.sub (hf.const_mul (2*c))
  rw [integral_add hs (integrable_const _),integral_sub hf2 (hf.const_mul (2*c)),
    integral_const_mul,integral_const] at hz
  simp only [probReal_univ,one_smul] at hz
  change 0≤(∫x,f x^2 ∂μ)-2*c*c+c^2 at hz
  change c^2≤∫x,f x^2 ∂μ
  nlinarith

theorem unitInterval_probability : IsProbabilityMeasure
    ((volume : Measure ℝ).restrict (Ioc 0 1)) := by
  constructor
  simp

theorem rootPath_energy_distance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (R D : ℝ → X → ℝ) (C : ℝ)
    (hDmeas : Measurable (Function.uncurry D))
    (hderiv : ∀t∈Icc (0:ℝ) 1,∀x,HasDerivAt (fun s => R s x) (D t x) t)
    (hDcont : ∀x,ContinuousOn (fun t => D t x) (Icc (0:ℝ) 1))
    (hDint : ∀t∈Icc (0:ℝ) 1,Integrable (fun x => D t x^2) μ)
    (henergy : ∀t∈Icc (0:ℝ) 1,(∫x,D t x^2 ∂μ)≤C)
    (hRint : Integrable (fun x => (R 1 x-R 0 x)^2) μ) :
    (∫x,(R 1 x-R 0 x)^2 ∂μ)≤C := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 1)
  let : IsProbabilityMeasure ν := unitInterval_probability
  have ht : ∀ᵐt∂ν,t∈Icc (0:ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨ht.1.le,ht.2⟩
  have hmeas : AEStronglyMeasurable (fun p : ℝ×X => D p.1 p.2^2) (ν.prod μ) :=
    (hDmeas.pow_const 2).aestronglyMeasurable
  have heint : Integrable (fun t => ∫x,D t x^2 ∂μ) ν := by
    apply (integrable_const C).mono' hmeas.integral_prod_right'
    filter_upwards [ht] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact henergy t ht
  have hj : Integrable (fun p : ℝ×X => D p.1 p.2^2) (ν.prod μ) := by
    apply (integrable_prod_iff hmeas).mpr
    constructor
    · filter_upwards [ht] with t ht
      exact hDint t ht
    · simpa only [Real.norm_eq_abs,abs_sq] using heint
  have hpoint (x : X) : (R 1 x-R 0 x)^2≤∫t,D t x^2 ∂ν := by
    have hd : IntervalIntegrable (fun t => D t x) volume 0 1 :=
      (hDcont x).intervalIntegrable_of_Icc (by norm_num)
    have hd2 : IntervalIntegrable (fun t => D t x^2) volume 0 1 :=
      ((hDcont x).pow 2).intervalIntegrable_of_Icc (by norm_num)
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht) x) hd
    have hc := square_integral_le_integral_square ν hd.1 hd2.1
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hf
    rw [← hf]
    exact hc
  calc
    _ ≤ ∫x,∫t,D t x^2 ∂ν ∂μ := integral_mono hRint hj.integral_prod_right hpoint
    _ = ∫t,∫x,D t x^2 ∂μ ∂ν := (integral_integral_swap hj).symm
    _ ≤ ∫_t,C ∂ν := integral_mono_ae heint (integrable_const _) (by
      filter_upwards [ht] with t ht
      exact henergy t ht)
    _ = C := by simp

end RootPathEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineGeneratorIntegrability
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section AffineGeneratorIntegrability
open Classical MeasureTheory Matrix

theorem affineNoiseGenerator_integrable_square {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (L : Matrix ι ι ℝ) (v : ι → ℝ) :
    Integrable (fun x : ι → ℝ => affineNoiseGenerator f L v x^2) := by
  let a : (ι → ℝ) → ℝ := fun x => ∑i,L i i*singletonNoise f .diagonal i x
  let b : (ι → ℝ) → ℝ := fun x => ∑i,v i*singletonNoise f .score i x
  let c : (ι → ℝ) → ℝ := fun x => ∑p : NoisePair ι,L p.val.1 p.val.2*pairNoise f p x
  have h : ∀u∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),
      ∀w∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),Integrable (fun x => u x*w x)
        (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    intro u hu w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hw
    rcases hu with rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl <;>
      dsimp only [a,b,c,singletonNoise,pairNoise] <;> apply noise_sum_integrable_product hf hc
  have haa := h a (by simp) a (by simp)
  have hbb := h b (by simp) b (by simp)
  have hcc := h c (by simp) c (by simp)
  have hab := h a (by simp) b (by simp)
  have hac := h a (by simp) c (by simp)
  have hbc := h b (by simp) c (by simp)
  convert! ((((haa.add hbb).add hcc).add (hab.const_mul 2)).add
    ((hac.const_mul 2).add (hbc.const_mul 2))).congr (Filter.Eventually.of_forall (fun x => ?_)) using 1
  all_goals try with_reducible_and_instances rfl
  change a x*a x+b x*b x+c x*c x+2*(a x*b x)+(2*(a x*c x)+2*(b x*c x))=
    (a x+b x+c x)^2
  ring

theorem affineNoiseRootDerivative_integrable_square {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A L : Matrix ι ι ℝ) (a v : ι → ℝ) (hA : IsUnit A.det) :
    Integrable (fun y => (-affineNoiseGenerator f L v (A⁻¹*ᵥ(y-a))/Real.sqrt A.det)^2) := by
  simpa only [div_pow,neg_sq] using
    (integrable_matrix_affine_inverse A a hA (affineNoiseGenerator_integrable_square hf hc L v)).div_const
      ((Real.sqrt A.det)^2)

end AffineGeneratorIntegrability

section NoiseInterpolation
open Classical Matrix MeasureTheory Set
open scoped Matrix.Norms.Elementwise

theorem covarianceSegment_hasDerivAt {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s => 1+covarianceSegment B C s) (C-B) t := by
  simp_rw [covarianceSegment_affine]
  convert! (hasDerivAt_const t (1+B)).add ((hasDerivAt_id t).smul_const (C-B)) using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem noiseInterpolation_hasDerivAt {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (B C : Matrix ι ι ℝ)
    (hB : B.PosSemidef) (hC : C.PosSemidef) (a h y : ι → ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivAt (fun s => noiseInterpolationRoot f B C a h s y)
      (noiseInterpolationDerivative f B C a h t y) t := by
  have hp := (Matrix.PosDef.one.add_posSemidef (covarianceSegment_posSemidef B C hB hC ht)).det_pos
  exact affineNoiseRoot_hasDerivAt (hf.differentiable (by norm_num))
    (covarianceSegment_hasDerivAt B C t)
    (by convert! (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const h) using 1
        simp) hp y

attribute [local instance] OAI.SimpleAmenable.instMeasurableSpaceMatrixReal_solutions_1
local instance instBorelSpaceMatrixRealOfFintype_solutions_1 {ι : Type*} [Fintype ι] : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

theorem noiseInterpolationDerivative_measurable {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (B C : Matrix ι ι ℝ) (a h : ι → ℝ) :
    Measurable (Function.uncurry (noiseInterpolationDerivative f B C a h)) := by
  let T : (ℝ×(ι → ℝ)) → Matrix ι ι ℝ := fun p => 1+covarianceSegment B C p.1
  have hT : Continuous T := by unfold T covarianceSegment; fun_prop
  have hi := matrix_inverse_measurable hT.measurable
  have hg : Continuous (fun p : (Matrix ι ι ℝ)×(ι → ℝ)×(ι → ℝ) =>
      affineNoiseGenerator f p.1 p.2.1 p.2.2) :=
    affineNoiseGenerator_continuous_comp hf continuous_fst
      continuous_snd.fst continuous_snd.snd
  have hx : Measurable (fun p : ℝ×(ι → ℝ) => p.2-(a+p.1 • h)) := by fun_prop
  have hij (i j : ι) : Measurable (fun p => (T p)⁻¹ i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hi)
  have hL : Measurable (fun p => (T p)⁻¹*(C-B)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ (fun k _ => (hij i k).mul_const _)
  have hv : Measurable (fun p => (T p)⁻¹*ᵥh) := by
    apply Measurable.of_eval
    intro i
    simp only [Matrix.mulVec,dotProduct]
    exact Finset.measurable_sum _ (fun k _ => (hij i k).mul_const _)
  have hxx : Measurable (fun p => (T p)⁻¹*ᵥ(p.2-(a+p.1 • h))) := by
    apply Measurable.of_eval
    intro i
    simp only [Matrix.mulVec,dotProduct]
    exact Finset.measurable_sum _ (fun k _ => (hij i k).mul ((measurable_pi_apply k).comp hx))
  exact (hg.measurable.comp (hL.prodMk (hv.prodMk hxx))).neg.div
    (hT.matrix_det.measurable.sqrt)

theorem noiseInterpolationDerivative_continuousOn {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (B C : Matrix ι ι ℝ)
    (hB : B.PosSemidef) (hC : C.PosSemidef) (a h y : ι → ℝ) :
    ContinuousOn (fun t => noiseInterpolationDerivative f B C a h t y) (Icc (0:ℝ) 1) := by
  intro t ht
  let T : ℝ → Matrix ι ι ℝ := fun s => 1+covarianceSegment B C s
  have hT : Continuous T := by unfold T covarianceSegment; fun_prop
  have hp : 0<(T t).det :=
    (Matrix.PosDef.one.add_posSemidef (covarianceSegment_posSemidef B C hB hC ht)).det_pos
  have hi := matrix_inverse_continuousAt hT.continuousAt hp.ne'
  have hg : Continuous (fun p : (Matrix ι ι ℝ)×(ι → ℝ)×(ι → ℝ) =>
      affineNoiseGenerator f p.1 p.2.1 p.2.2) :=
    affineNoiseGenerator_continuous_comp hf continuous_fst
      continuous_snd.fst continuous_snd.snd
  have hL : ContinuousAt (fun s => (T s)⁻¹*(C-B)) t := by fun_prop
  have hv : ContinuousAt (fun s => (T s)⁻¹*ᵥh) t := by
    fun_prop
  have hx : ContinuousAt (fun s => (T s)⁻¹*ᵥ(y-(a+s • h))) t := by
    fun_prop
  exact ((hg.continuousAt.comp (hL.prodMk (hv.prodMk hx))).neg.div
    hT.matrix_det.continuousAt.sqrt (Real.sqrt_ne_zero'.mpr hp)).continuousWithinAt

end NoiseInterpolation

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_HellingerDistance
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section HellingerDistance
open Classical MeasureTheory

theorem integral_abs_mul_le_sqrt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫x,|f x| *|g x| ∂μ)≤ Real.sqrt (∫x,f x^2 ∂μ)*Real.sqrt (∫x,g x^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (by
    apply Real.holderConjugate_iff.mpr
    norm_num : (2:ℝ).HolderConjugate 2)
    (by simpa using hf) (by simpa using hg)
  norm_num only [ENNReal.ofReal_ofNat,Real.norm_eq_abs,Real.rpow_ofNat,abs_sq,
    one_div,← Real.sqrt_eq_rpow] at h
  simpa only [sq_abs] using h

theorem density_L1_le_twice_root_distance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {R S : X → ℝ} (hR : MemLp R 2 μ) (hS : MemLp S 2 μ)
    (hnR : (∫x,R x^2 ∂μ)=1) (hnS : (∫x,S x^2 ∂μ)=1) :
    (∫x,|R x^2-S x^2| ∂μ)≤2*Real.sqrt (∫x,(R x-S x)^2 ∂μ) := by
  have hab := integral_abs_mul_le_sqrt μ (hR.sub hS) (hR.add hS)
  have heq (x : X) : |R x^2-S x^2|=|R x-S x| *|R x+S x| := by
    rw [← abs_mul]
    congr 1
    ring
  simp only [Pi.sub_apply,Pi.add_apply] at hab
  have hi : (∫x,(R x+S x)^2 ∂μ)≤4 := by
    calc
      _ ≤ ∫x,2*(R x^2+S x^2) ∂μ := integral_mono (hR.add hS).integrable_sq
        ((hR.integrable_sq.add hS.integrable_sq).const_mul 2)
        (fun x => by
          change (R x+S x)^2≤2*(R x^2+S x^2)
          nlinarith [sq_nonneg (R x-S x)])
      _ = 4 := by
        rw [integral_const_mul,integral_add hR.integrable_sq hS.integrable_sq,hnR,hnS]
        norm_num
  simp_rw [heq]
  apply hab.trans
  have hh : Real.sqrt (∫x,(R x+S x)^2 ∂μ)≤2 := by
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num at *; exact hi⟩
  nlinarith [Real.sqrt_nonneg (∫x,(R x-S x)^2 ∂μ)]

end HellingerDistance

section AffineDensityDistance
open Classical Matrix MeasureTheory Set

theorem affineNoiseRoot_memLp {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    MemLp (affineNoiseRoot f A a) 2 (volume : Measure (ι → ℝ)) := by
  apply (memLp_two_iff_integrable_sq (affineNoiseRoot_continuous hf A a).aestronglyMeasurable).mpr
  exact affineNoiseRoot_integrable_square hf hc A a hA

theorem affineNoiseRoot_square_distance {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
    (∫y : ι → ℝ,(affineNoiseRoot f (1+C) (a+h) y-affineNoiseRoot f (1+B) a y)^2)≤
      affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
        ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2) := by
  have hR (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      MemLp (noiseInterpolationRoot f B C a h t) 2 (volume : Measure (ι → ℝ)) :=
    affineNoiseRoot_memLp hf.continuous hc _ _
      (one_add_psd_isUnit_det _ (covarianceSegment_posSemidef B C hB hC ht))
  have H := rootPath_energy_distance (volume : Measure (ι → ℝ))
    (noiseInterpolationRoot f B C a h) (noiseInterpolationDerivative f B C a h)
    (affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
      ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2))
    (noiseInterpolationDerivative_measurable hf B C a h)
    (fun t ht y => noiseInterpolation_hasDerivAt hf B C hB hC a h y ht)
    (fun y => noiseInterpolationDerivative_continuousOn hf B C hB hC a h y)
    (fun t ht => affineNoiseRootDerivative_integrable_square hf hc _ _ _ _
      (one_add_psd_isUnit_det _ (covarianceSegment_posSemidef B C hB hC ht)))
    (fun t ht => noiseInterpolationDerivative_energy hf hc hn he B C hB hC a h ht)
    ((hR 1 (by norm_num)).sub (hR 0 (by norm_num))).integrable_sq
  simpa only [noiseInterpolationRoot,covarianceSegment,sub_self,zero_smul,add_zero,
    zero_add,one_smul,sub_zero] using H

theorem affineNoiseDensity_L1_distance {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
    (∫y : ι → ℝ,|affineNoiseRoot f (1+C) (a+h) y^2-affineNoiseRoot f (1+B) a y^2|)≤
      2*Real.sqrt (affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
        ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2)) := by
  have H := density_L1_le_twice_root_distance (volume : Measure (ι → ℝ))
    (affineNoiseRoot_memLp hf.continuous hc (1+C) (a+h) (one_add_psd_isUnit_det C hC))
    (affineNoiseRoot_memLp hf.continuous hc (1+B) a (one_add_psd_isUnit_det B hB))
    (affineNoiseRoot_normalized hn (1+C) (a+h) (Matrix.PosDef.one.add_posSemidef hC).det_pos)
    (affineNoiseRoot_normalized hn (1+B) a (Matrix.PosDef.one.add_posSemidef hB).det_pos)
  exact H.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (affineNoiseRoot_square_distance hf hc hn he B C hB hC a h)) (by norm_num))

end AffineDensityDistance

section FiniteAffineLaw
open Classical MeasureTheory Matrix Set
open scoped ENNReal

theorem measurableEquiv_map_withDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e=(μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply,MeasurableEquiv.symm_apply_apply] using
    (setLIntegral_map (μ := μ) hs (hf.comp e.symm.measurable) e.measurable).symm

theorem smoothNoiseLaw_pi_density (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => smoothNoiseLaw)=
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)) := by
  have hi : Integrable (fun x : ℝ => smoothNoiseRoot x^2) := by
    have hh := noiseFactor_integrable_product
      (smoothNoiseRoot_contDiff.of_le (by norm_num)) smoothNoiseRoot_compact .base .base
    simpa only [noiseFactor,pow_two] using hh
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻x,ENNReal.ofReal (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)
    ∂((Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (univ.pi s)))=_
  rw [Measure.restrict_pi_pi]
  have hint : Integrable (fun x : ι → ℝ => noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)
      (Measure.pi (fun i => (volume : Measure ℝ).restrict (s i))) := by
    simpa only [noiseTensor,← Finset.prod_pow] using Integrable.fintype_prod (fun i => hi.restrict (s := s i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => sq_nonneg _))]
  have he : (∫x : ι → ℝ,noiseTensor (fun _ : ι => smoothNoiseRoot) x^2
      ∂Measure.pi (fun i => (volume : Measure ℝ).restrict (s i)))=
      ∏i,∫t : ℝ,smoothNoiseRoot t^2 ∂(volume.restrict (s i)) := by
    simp only [noiseTensor,← Finset.prod_pow]
    convert! integral_fintype_prod_eq_prod
      (μ := fun i => (volume : Measure ℝ).restrict (s i))
      (fun (_ : ι) (x : ℝ) => smoothNoiseRoot x^2) using 1
    all_goals try with_reducible_and_instances rfl
  rw [he,ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [smoothNoiseLaw,withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi.restrict (s := s i)) (ae_of_all _ (fun _ => sq_nonneg _))

theorem independentSmoothNoiseLaw_finite_density (ι : Type*) [Fintype ι] :
    independentSmoothNoiseLaw ι=(volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)) := by
  rw [independentSmoothNoiseLaw,Measure.infinitePi_eq_pi,smoothNoiseLaw_pi_density]

instance finiteAffineNoiseLaw_probability {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) : IsProbabilityMeasure (finiteAffineNoiseLaw A a) := by
  unfold finiteAffineNoiseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem finiteAffineNoiseLaw_density {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hpos : 0<A.det) :
    finiteAffineNoiseLaw A a=(volume : Measure (ι → ℝ)).withDensity
      (fun y => ENNReal.ofReal (affineNoiseRoot smoothNoiseRoot A a y^2)) := by
  let hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hpos.ne'
  let e := matrixAffineEquiv A a hA
  have hf : Measurable (fun x : ι → ℝ => ENNReal.ofReal
      (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)) :=
    ((noiseTensor_continuous smoothNoiseRoot_contDiff.continuous).pow 2).measurable.ennreal_ofReal
  unfold finiteAffineNoiseLaw
  rw [independentSmoothNoiseLaw_finite_density]
  rw [show (fun x => a+A*ᵥx)=(e : (ι → ℝ) → (ι → ℝ)) from
    (funext (fun x => matrixAffineEquiv_apply A a x hA)).symm,
    measurableEquiv_map_withDensity _ e hf]
  have hm : Measure.map e volume=ENNReal.ofReal |A.det⁻¹| • volume := by
    rw [show (e : (ι → ℝ) → (ι → ℝ))=(fun x => a+A*ᵥx) from
      funext (fun x => matrixAffineEquiv_apply A a x hA),map_matrix_affine_volume A a hA]
  rw [hm,withDensity_smul_measure]
  have hr := withDensity_smul (μ := (volume : Measure (ι → ℝ)))
    (ENNReal.ofReal |A.det⁻¹|) (hf.comp e.symm.measurable)
  trans volume.withDensity
    (ENNReal.ofReal |A.det⁻¹| • (fun y => ENNReal.ofReal
      (noiseTensor (fun _ : ι => smoothNoiseRoot) (e.symm y)^2)))
  · convert! hr.symm using 1
    all_goals try with_reducible_and_instances rfl
  congr 1
  ext y
  simp only [Pi.smul_apply,smul_eq_mul,matrixAffineEquiv_symm_apply,e,
    affineNoiseRoot,div_pow,Real.sq_sqrt hpos.le]
  rw [abs_of_pos (inv_pos.mpr hpos),← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
  congr 1
  ring

end FiniteAffineLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteLawDistance
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FiniteLawDistance
open Classical Matrix MeasureTheory

theorem finiteAffineNoiseLaw_close_oai {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
    ObservableClose (finiteAffineNoiseLaw (1+B) a) (finiteAffineNoiseLaw (1+C) (a+h))
      (smoothNoiseTransportError B C h) := by
  rw [finiteAffineNoiseLaw_density _ _ (Matrix.PosDef.one.add_posSemidef hB).det_pos,
    finiteAffineNoiseLaw_density _ _ (Matrix.PosDef.one.add_posSemidef hC).det_pos]
  have hf : ContDiff ℝ 1 smoothNoiseRoot := smoothNoiseRoot_contDiff.of_le (by norm_num)
  have hp := affineNoiseRoot_continuous smoothNoiseRoot_contDiff.continuous (1+B) a
  have hq := affineNoiseRoot_continuous smoothNoiseRoot_contDiff.continuous (1+C) (a+h)
  have hh := (observableClose_of_density (volume : Measure (ι → ℝ))
    (hq.pow 2).measurable (hp.pow 2).measurable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (affineNoiseRoot_integrable_square smoothNoiseRoot_contDiff.continuous smoothNoiseRoot_compact
      _ _ (one_add_psd_isUnit_det C hC))
    (affineNoiseRoot_integrable_square smoothNoiseRoot_contDiff.continuous smoothNoiseRoot_compact
      _ _ (one_add_psd_isUnit_det B hB))).symm
  apply hh.mono
  exact affineNoiseDensity_L1_distance hf smoothNoiseRoot_compact
    smoothNoiseRoot_normalized smoothNoiseRoot_even B C hB hC a h

end FiniteLawDistance

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.finiteAffineNoiseLaw_close_oai.{u_1} := @OAI.SimpleAmenable.finiteAffineNoiseLaw_close_oai.{u_1}
