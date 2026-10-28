-- Prove2me | solution 1 for OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:40:14.802658+00:00
-- url     : https://prove2.me/submissions/63a2d623-458d-49d7-a84e-58ff46e89b04

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_BarrierMenu_sampledPartition_arrow

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

end SourceDyadicArithmetic

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

theorem ObservableClose.event {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ℝ} (h : ObservableClose μ ν ε) {s : Set X} (hs : MeasurableSet s) :
    |μ.real s-ν.real s| ≤ ε := by
  have hh := h (s.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hs) (by
    intro x
    by_cases hx : x∈s <;> simp [hx])
  simpa only [integral_indicator hs,integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ] using hh

end ObservableDistance

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

theorem smoothNoiseRoot_zero {x : ℝ} (hx : 1≤|x|) : smoothNoiseRoot x=0 := by
  rw [smoothNoiseRoot]
  have hh : rawNoiseBump x=0 := rawNoiseBump.zero_of_le_dist (by
    simpa only [rawNoiseBump,Real.dist_eq,sub_zero] using hx)
  rw [hh,zero_div]

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

section ActualNoiseLaw
open Classical MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal

theorem smoothNoiseDensity_measurable : Measurable smoothNoiseDensity :=
  (smoothNoiseRoot_contDiff.continuous.pow 2).measurable.ennreal_ofReal

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

theorem smoothNoiseLaw_bounded : ∀ᵐx ∂smoothNoiseLaw,x∈Set.Icc (-1:ℝ) 1 := by
  rw [smoothNoiseLaw,ae_withDensity_iff smoothNoiseDensity_measurable]
  filter_upwards with x hx
  by_contra h
  have hh : 1≤|x| := by
    have hn : ¬ |x|≤1 := by simpa only [abs_le,Set.mem_Icc] using h
    exact (lt_of_not_ge hn).le
  have hz := smoothNoiseRoot_zero hh
  exact hx (by simp [smoothNoiseDensity,hz])

instance independentSmoothNoiseLaw_probability (ι : Type*) :
    IsProbabilityMeasure (independentSmoothNoiseLaw ι) := by
  unfold independentSmoothNoiseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem independentSmoothNoiseLaw_map (ι : Type*) (i : ι) :
    (independentSmoothNoiseLaw ι).map (fun x => x i)=smoothNoiseLaw :=
  Measure.infinitePi_map_eval _ i

theorem independentSmoothNoiseLaw_bounded (ι : Type*) (i : ι) :
    ∀ᵐx ∂independentSmoothNoiseLaw ι,x i∈Set.Icc (-1:ℝ) 1 := by
  have hh := smoothNoiseLaw_bounded
  rw [← independentSmoothNoiseLaw_map ι i] at hh
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable (by measurability)).mp hh

end ActualNoiseLaw

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

end FiniteField

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldHS
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

section SourceFieldLaw
open Classical Matrix MeasureTheory Filter
open scoped Topology

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

end SourceFieldLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_ThresholdField
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
section ThresholdField
open Classical MeasureTheory Set

theorem thresholdField_measurable {ι : Type*} : Measurable (@thresholdField ι) := by
  apply Measurable.of_eval
  intro z
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply z))
    measurable_const measurable_const

theorem signalSuccess_measurable {ι : Type*} [Countable ι] (a : ι → ℝ) :
    MeasurableSet {b : ι → Bool | signalSuccess a b} := by
  unfold signalSuccess
  measurability

end ThresholdField

section SourceBitField
open Classical MeasureTheory Filter Set
open scoped Topology

instance sourceBitFieldLaw_probability {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceBitFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n) := by
  unfold sourceBitFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map thresholdField_measurable.aemeasurable

theorem finiteBitWindow_finite {ι : Type*} (J : Finset ι) :
    Set.Finite {b : ι → Bool | ∀z,z∉J → b z=false} := by
  apply (Set.finite_range (extendFiniteBits J)).subset
  intro b hb
  refine ⟨fun z => b z.val,?_⟩
  funext z
  by_cases hz : z∈J
  · simp only [extendFiniteBits,dite_eq_left hz]
  · simp only [extendFiniteBits,dite_eq_right hz,hb z hz]

theorem sourceBitFieldLaw_finite_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (hθc : ∀x,L≤‖x‖ → θ x=-3)
    (ρ η κ : ℝ) (n : ℕ) :
    ∃S : Finset (FlagSite a m D v → Bool),
      ∀ᵐb ∂sourceBitFieldLaw (v:=v) hD θ χ hL ρ η κ n,b∈S := by
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos (sourceDyadicN_pos n) hL)
  refine ⟨(finiteBitWindow_finite J).toFinset,?_⟩
  have hw : MeasurableSet {b : FlagSite a m D v → Bool | ∀z,z∉J → b z=false} := by measurability
  simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  unfold sourceBitFieldLaw sourceSmoothFieldLaw
  rw [ae_map_iff thresholdField_measurable.aemeasurable hw]
  have hw' : MeasurableSet {x : FlagSite a m D v → ℝ | ∀z,z∉J → thresholdField x z=false} :=
    thresholdField_measurable hw
  rw [ae_map_iff (finiteCoefficientField_measurable _ _ _).aemeasurable hw']
  have hb : ∀ᵐx ∂independentSmoothNoiseLaw (FlagSite a m D v),∀z,x z∈Icc (-1:ℝ) 1 :=
    ae_all_iff.mpr (independentSmoothNoiseLaw_bounded _)
  filter_upwards [hb] with x hx
  intro z hz
  have ha : flagMeanSignal θ (sourceDyadicN n) z=-3 :=
    flagMeanSignal_outside θ (sourceDyadicN_pos n) hθc z (by simpa only [J,mem_flagBoxFinset] using hz)
  have hB (w : FlagSite a m D v) := sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n z w (Or.inl hz)
  have hh : ¬0<finiteCoefficientField J (flagMeanSignal θ (sourceDyadicN n))
      (Matrix.of (sourceFlagMatrix χ ρ η κ n)) x z := by
    simp only [finiteCoefficientField,ha,Matrix.of_apply,hB,zero_mul,Finset.sum_const_zero,add_zero]
    linarith [(hx z).2]
  exact ite_eq_right hh

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

end BitReindex

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

theorem jointBitReindex_measurable {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (hD : 0<D) (g : polygonFullGroup a m) : Measurable (jointBitReindex v hD g) :=
  Measurable.of_eval (fun j => (bitReindex_measurable _).comp (measurable_pi_apply j))

end JointBitField

section JointFieldSuccess
open Classical MeasureTheory Filter Set
open scoped Topology

theorem jointFieldSuccess_measurable {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (n : ℕ) :
    MeasurableSet {b : ∀j,FlagSite a m D (v j) → Bool | jointFieldSuccess v S n b} := by
  simp only [jointFieldSuccess,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurable_pi_apply (X:=fun j : Fin k => FlagSite a m D (v j) → Bool) j) (signalSuccess_measurable
    (flagMeanSignal (S j).signal (sourceDyadicN n) : FlagSite a m D (v j) → ℝ))

theorem jointBitFieldLaw_finite_support {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hq : ∀j,(S j).q=-3) (hD : 0<D)
    (η κ : ℝ) (n : ℕ) :
    ∃T : Finset (∀j,FlagSite a m D (v j) → Bool),
      ∀ᵐb ∂jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n,b∈T := by
  let μ (j : Fin k) := (S j).bitLaw (a:=a) (m:=m) (v:=v j) hD η κ n
  have hc (j : Fin k) : ∀x,(S j).L≤‖x‖ → (S j).signal x=-3 := by
    intro x hx
    have hzero := (S j).ψ_zero x (by linarith [(S j).gap])
    simp only [FieldSignalData.signal,hzero,hq j,add_zero]
  choose T hT using (fun j => sourceBitFieldLaw_finite_support (a:=a) (m:=m) (v:=v j)
    hD (S j).signal (S j).χ (S j).L_pos (S j).χ_zero (hc j) ((D:ℝ)^4/5) η κ n)
  have hf : Set.Finite (Set.univ.pi (fun j => (T j : Set (FlagSite a m D (v j) → Bool)))) :=
    Set.Finite.pi (fun j => (T j).finite_toSet)
  refine ⟨hf.toFinset,?_⟩
  simp only [Set.Finite.mem_toFinset,Set.mem_pi,Set.mem_univ,true_implies,Finset.mem_coe]
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval μ j).quasiMeasurePreserving.ae (hT j)

end JointFieldSuccess

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierFiniteMenu
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

section EightBarrierFields
open Classical MeasureTheory Filter Set
open scoped Topology

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem eight_q (j : Fin (4+4)) : (S.eight j).q = -3 := by
  induction j using Fin.addCases with
  | left j => simpa only [eight,Fin.addCases_left] using S.first_q
  | right j => simpa only [eight,Fin.addCases_right] using S.second_q j

end BarrierSignalSystem

end EightBarrierFields

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_UniformShapeMatchings
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
section UniformShapeMatchings
open Classical Set

theorem partitionBaseline_related {a m : ℕ} (P : TrackPolygonPartition a m) :
    ∃g : polygonFullGroup a m,PartitionArrow (partitionBaseline P) P g :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (partitionShapeSetoid a m) P))

theorem partitionBaseline_eq {a m : ℕ} {P Q : TrackPolygonPartition a m} {g : polygonFullGroup a m}
    (hg : PartitionArrow P Q g) : partitionBaseline P=partitionBaseline Q :=
  congrArg Quotient.out (Quotient.sound (s:=partitionShapeSetoid a m) ⟨g,hg⟩)

theorem matchingSupport_nonempty {a m : ℕ} (P : TrackPolygonPartition a m) : (matchingSupport P).Nonempty := by
  obtain ⟨g,hg⟩ := partitionBaseline_related P
  exact ⟨g,(mem_matchingSupport P g).mpr hg⟩

theorem matchingSupport_transport {a m : ℕ} {P Q : TrackPolygonPartition a m} {g : polygonFullGroup a m}
    (hg : PartitionArrow P Q g) : matchingSupport Q=(matchingSupport P).image (fun x => g*x) := by
  have hb := partitionBaseline_eq hg
  ext h
  simp only [Finset.mem_image,mem_matchingSupport]
  constructor
  · intro hh
    refine ⟨g⁻¹*h,?_,by group⟩
    have h := hg.inv.mul hh
    rwa [←hb] at h
  · rintro ⟨x,hx,rfl⟩
    have h := hg.mul hx
    rwa [hb] at h

theorem matchingAverage_range {a m : ℕ} (P : TrackPolygonPartition a m)
    {f : polygonFullGroup a m → ℝ} (hf : ∀x,f x∈Icc (0:ℝ) 1) : matchingAverage P f∈Icc (0:ℝ) 1 := by
  have hc : (0:ℝ)<(matchingSupport P).card := by exact_mod_cast (matchingSupport_nonempty P).card_pos
  refine ⟨div_nonneg (Finset.sum_nonneg (fun x _ => (hf x).1)) hc.le,?_⟩
  apply (div_le_one hc).mpr
  calc
    (∑x∈matchingSupport P,f x) ≤ ∑_x∈matchingSupport P,(1:ℝ) := Finset.sum_le_sum (fun x _ => (hf x).2)
    _ = _ := by simp

theorem matchingAverage_transport {a m : ℕ} {P Q : TrackPolygonPartition a m} {g : polygonFullGroup a m}
    (hg : PartitionArrow P Q g) (f : polygonFullGroup a m → ℝ) :
    matchingAverage Q f=matchingAverage P (fun x => f (g*x)) := by
  unfold matchingAverage
  rw [matchingSupport_transport hg,Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h),Finset.sum_image]
  intro _ _ _ _ equality
  exact mul_left_cancel equality

end UniformShapeMatchings

section FiniteSupportedLaws
open Classical MeasureTheory Set

theorem finset_indicator_measurable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : Finset X) (f : X → ℝ) : Measurable ((T : Set X).indicator f) := by
  apply measurable_zero.measurable_of_countable_ne
  apply T.finite_toSet.countable.mono
  intro x hx
  by_contra hn
  exact hx (by simp [hn])

theorem integrable_of_finite_support {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T) (f : X → ℝ) :
    Integrable f μ := by
  have hi : Integrable ((T : Set X).indicator f) μ := by
    have he : (T : Set X).indicator f=fun x => ∑z∈T,({z} : Set X).indicator (fun _ => f z) x := by
      funext x
      by_cases hx : x∈T
      · simp only [Set.indicator_of_mem hx]
        symm
        rw [Finset.sum_eq_single x]
        · simp
        · intro _ _ distinct
          simp [Set.indicator_of_notMem,Ne.symm distinct]
        · exact fun hn => (hn hx).elim
      · simp only [Set.indicator_of_notMem hx]
        symm
        apply Finset.sum_eq_zero
        intro z hz
        have hz' : x≠z := fun h => hx (h.symm ▸ hz)
        simp [hz']
    rw [he]
    apply integrable_finsetSum
    intro point _
    exact (integrable_const (f point)).indicator (measurableSet_singleton point)
  apply hi.congr
  filter_upwards [hT] with x hx
  simp [hx]

theorem ObservableClose.finiteSupport {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ ν : Measure X} (T U : Finset X) (hT : ∀ᵐx ∂μ,x∈T) (hU : ∀ᵐx ∂ν,x∈U)
    {ε : ℝ} (h : ObservableClose μ ν ε) (f : X → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) :
    |(∫x,f x ∂μ)-(∫x,f x ∂ν)| ≤ ε := by
  let V := T∪U
  let f' := (V : Set X).indicator f
  have heμ : f'=ᵐ[μ] f := by
    filter_upwards [hT] with x hx
    exact Set.indicator_of_mem (Finset.mem_union_left U hx) f
  have heν : f'=ᵐ[ν] f := by
    filter_upwards [hU] with x hx
    exact Set.indicator_of_mem (Finset.mem_union_right T hx) f
  have hh := h f' (finset_indicator_measurable V f) (by
    intro x
    by_cases hx : x∈V
    · simpa only [f',Set.indicator_of_mem hx] using hf x
    · simp [f',hx])
  rwa [integral_congr_ae heμ,integral_congr_ae heν] at hh

theorem integral_difference_le_failure {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T)
    (f g : X → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) (hg : ∀x,g x∈Icc (0:ℝ) 1)
    (E : Set X) (hE : MeasurableSet E) (he : ∀x,x∉E → f x=g x) :
    |(∫x,f x ∂μ)-(∫x,g x ∂μ)| ≤ μ.real E := by
  have hif := integrable_of_finite_support μ T hT f
  have hig := integrable_of_finite_support μ T hT g
  rw [←integral_sub hif hig]
  calc
    _ ≤ ∫x,|f x-g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫x,E.indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply integral_mono (hif.sub hig).abs ((integrable_const 1).indicator hE)
      intro x
      by_cases hx : x∈E
      · rw [Set.indicator_of_mem hx]
        change |f x-g x| ≤ 1
        exact abs_le.mpr ⟨by linarith [(hf x).1,(hg x).2],by linarith [(hg x).1,(hf x).2]⟩
      · simp [Set.indicator_of_notMem hx,he x hx]
    _ = μ.real E := by simp [integral_indicator hE,Measure.real]

end FiniteSupportedLaws

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_SuccessfulLawCovariance
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
section SuccessfulLawCovariance
open Classical MeasureTheory Set

theorem successful_law_covariance {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T)
    (t : X → X) (ht : Measurable t) (S : Set X) (hS : MeasurableSet S)
    {ε : ℝ} (hc : ObservableClose μ (μ.map t) ε)
    (f g : X → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) (hg : ∀x,g x∈Icc (0:ℝ) 1)
    (he : ∀x,x∈S → t x∈S → f (t x)=g x) :
    |(∫x,f x ∂μ)-(∫x,g x ∂μ)| ≤ 2*μ.real Sᶜ+2*ε := by
  let ν := μ.map t
  let : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let U := T.image t
  have hU : ∀ᵐx ∂ν,x∈U := by
    apply (ae_map_iff ht.aemeasurable U.measurableSet).mpr
    filter_upwards [hT] with x hx
    exact Finset.mem_image_of_mem t hx
  have hic := hc.finiteSupport T U hT hU f hf
  have hmap : (∫x,f x ∂ν)=∫x,f (t x) ∂μ :=
    integral_map ht.aemeasurable (integrable_of_finite_support ν U hU f).aestronglyMeasurable
  rw [hmap] at hic
  let E := Sᶜ ∪ t ⁻¹' Sᶜ
  have hE : MeasurableSet E := hS.compl.union (ht hS.compl)
  have hd := integral_difference_le_failure μ T hT (fun x => f (t x)) g
    (fun x => hf (t x)) hg E hE (by
      intro x hx
      have hx' : x∈S ∧ t x∈S := by simpa [E] using hx
      exact he x hx'.1 hx'.2)
  have hb := hc.event hS.compl
  have hreal : ν.real Sᶜ=μ.real (t ⁻¹' Sᶜ) := map_measureReal_apply ht hS.compl
  have hbound : μ.real E ≤ 2*μ.real Sᶜ+ε := by
    have hu : μ.real E ≤ μ.real Sᶜ+μ.real (t ⁻¹' Sᶜ) :=
      measureReal_union_le (μ:=μ) Sᶜ (t ⁻¹' Sᶜ)
    have ht' := (abs_le.mp hb).1
    change -ε ≤ μ.real Sᶜ-ν.real Sᶜ at ht'
    rw [hreal] at ht'
    linarith
  have htri := abs_sub_le (∫x,f x ∂μ) (∫x,f (t x) ∂μ) (∫x,g x ∂μ)
  linarith

end SuccessfulLawCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonMatchingLaw
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
section PolygonMatchingLaw
open Classical MeasureTheory Filter Set
open scoped Topology

namespace BarrierMenu
variable {a m : ℕ} {ha : 0 < a} {F : Finset (polygonFullGroup a m)} (M : BarrierMenu a m ha F)

theorem matching_expectation_covariance_oai {η κ : ℝ} {n : ℕ}
    (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    (g : polygonFullGroup a m) (hg : g∈F) {δ : ℝ}
    (hc : ObservableClose (jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha)
      M.signals.eight (commonVertexDenominator_pos ha) η κ n)
      ((jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
        (commonVertexDenominator_pos ha) η κ n).map (barrierBitsTransport g)) δ)
    (f : polygonFullGroup a m → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) :
    let μ := jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
      (commonVertexDenominator_pos ha) η κ n
    |(∫b,matchingAverage (M.signals.sampledPartition n b) f ∂μ)-
      (∫b,matchingAverage (M.signals.sampledPartition n b) (fun x => f (g*x)) ∂μ)| ≤
      2*μ.real {b | ¬jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b}+2*δ := by
  dsimp only
  obtain ⟨T,hT⟩ := jointBitFieldLaw_finite_support (a:=a) (m:=m) (barrierEightDirections ha)
    M.signals.eight M.signals.eight_q (commonVertexDenominator_pos ha) η κ n
  apply successful_law_covariance _ T hT (barrierBitsTransport g)
    (jointBitReindex_measurable _ _ g)
    {b | jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b}
    (jointFieldSuccess_measurable _ _ n) hc
    (fun b => matchingAverage (M.signals.sampledPartition n b) f)
    (fun b => matchingAverage (M.signals.sampledPartition n b) (fun x => f (g*x)))
    (fun b => matchingAverage_range _ hf)
    (fun b => matchingAverage_range _ (fun x => hf (g*x)))
  intro b hb hb'
  exact matchingAverage_transport (M.sampledPartition_arrow (sourceDyadicN_one_le n) hQ hB g hg b hb hb') f

end BarrierMenu

end PolygonMatchingLaw

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance_oai := @OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance_oai
