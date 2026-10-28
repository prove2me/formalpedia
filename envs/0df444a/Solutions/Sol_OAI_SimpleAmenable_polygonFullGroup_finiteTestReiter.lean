-- Prove2me | solution 1 for OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:50:38.579546+00:00
-- url     : https://prove2.me/submissions/3def4dde-fe3f-4f92-8b78-7b62a7f753d9

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_BarrierMenu_matching_expectation_covariance
import Theorems.Thm_OAI_SimpleAmenable_finiteSignalFields_transport
import Theorems.Thm_OAI_SimpleAmenable_jointBitFieldLaw_success

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentAnchors
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

section LineIntersectionBounds

theorem real_two_lines_distance_bound (A B C E c d : ℝ) (h : A*E-C*B ≠ 0)
    (z p : ℝ × ℝ) (hz : A*z.1+B*z.2=c) (hz' : C*z.1+E*z.2=d)
    (δ : ℝ) (hδ : 0≤δ)
    (hp : |c-(A*p.1+B*p.2)| ≤ δ) (hp' : |d-(C*p.1+E*p.2)| ≤ δ) :
    dist z p ≤ ((|A| + |B| + |C| + |E|)/|A*E-C*B|)*δ := by
  have hd : 0 < |A*E-C*B| := abs_pos.mpr h
  have hx : (A*E-C*B)*(z.1-p.1)=E*(c-(A*p.1+B*p.2))-B*(d-(C*p.1+E*p.2)) := by
    linear_combination E*hz-B*hz'
  have hy : (A*E-C*B)*(z.2-p.2)=A*(d-(C*p.1+E*p.2))-C*(c-(A*p.1+B*p.2)) := by
    linear_combination A*hz'-C*hz
  have hx' : |A*E-C*B| * |z.1-p.1| ≤ (|E| + |B|)*δ := by
    rw [← abs_mul,hx]
    calc
      _ ≤ |E*(c-(A*p.1+B*p.2))| + |B*(d-(C*p.1+E*p.2))| := abs_sub _ _
      _ ≤ |E| * δ+|B| * δ := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hp' (abs_nonneg _))
      _ = _ := by ring
  have hy' : |A*E-C*B| * |z.2-p.2| ≤ (|A| + |C|)*δ := by
    rw [← abs_mul,hy]
    calc
      _ ≤ |A*(d-(C*p.1+E*p.2))| + |C*(c-(A*p.1+B*p.2))| := abs_sub _ _
      _ ≤ |A| * δ+|C| * δ := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hp' (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
      _ = _ := by ring
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff]
  rw [div_mul_eq_mul_div]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [abs_nonneg A,abs_nonneg C]
  · apply (le_div_iff₀ hd).mpr
    nlinarith [abs_nonneg B,abs_nonneg E]

end LineIntersectionBounds

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FullGroupAffineData
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section FlagAffineControl
open Classical

theorem squareArrangement_finite_range {a : ℕ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) : (Set.range f).Finite := by
  obtain ⟨S,hS⟩ := hf
  let p (k : Set.range f) : GenericSquare a := k.property.choose
  have hp (k : Set.range f) : f (p k)=k.val := k.property.choose_spec
  let q (k : Set.range f) : S → Bool := fun l => squareSign l.val (p k)
  have hq : Function.Injective q := by
    intro k j h
    apply Subtype.ext
    rw [← hp k,← hp j]
    exact hS (p k) (p j) (fun l hl => congrFun h ⟨l,hl⟩)
  have : Finite (Set.range f) := Finite.of_injective q hq
  exact Set.toFinite _

end FlagAffineControl

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

theorem sourceDyadic_radius_eventually (A : ℝ) :
    ∀ᶠn : ℕ in atTop,A ≤ (2:ℝ)^n :=
  (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 by norm_num)).eventually_ge_atTop A

end SourceSignalScales

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

theorem exists_fieldSignalData (ψ : (ℝ×ℝ) → ℝ) (hs : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (q : ℝ) :
    ∃S : FieldSignalData,S.ψ=ψ ∧ S.q=q := by
  obtain ⟨K,hK,hzero⟩ := hc.exists_pos_le_norm
  let χ : ContDiffBump (0 : ℝ×ℝ) := ⟨K+2,K+3,by linarith,by linarith⟩
  obtain ⟨Λ,hΛ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport (χ.contDiff : ContDiff ℝ 1 (χ : (ℝ×ℝ) → ℝ)) (by simp)
  refine ⟨⟨ψ,χ,hs,hc,q,K,K+3,Λ,by linarith,by linarith,hzero,
    fun x => ⟨χ.nonneg,χ.le_one⟩,?_,?_,Λ.coe_nonneg,?_⟩,rfl,rfl⟩
  · intro x hx
    exact χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,χ] using hx)
  · intro x hx
    exact χ.zero_of_le_dist (by simpa only [dist_zero_right,χ] using hx)
  · intro x y
    have hh := hΛ.dist_le_mul x y
    rw [Real.dist_eq,dist_eq_norm,Prod.norm_def] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ Λ.coe_nonneg
    simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierSignals
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section BarrierSignals
open Classical Set
open scoped ContDiff

theorem exists_firstBarrierSignal {R₀ R₁ : ℝ} (hR₀ : 0<R₀) (hR : R₀<R₁) :
    ∃S : FieldSignalData,S.q=-3 ∧
      (∀x,‖x‖≤R₀ → S.signal x=3) ∧ (∀x,R₁≤‖x‖ → S.signal x=-3) := by
  let b : ContDiffBump (0 : ℝ×ℝ) := ⟨R₀,R₁,hR₀,hR⟩
  let ψ : (ℝ×ℝ) → ℝ := fun x => 6*b x
  have hs : ContDiff ℝ 2 ψ := contDiff_const.mul b.contDiff
  have hc : HasCompactSupport ψ := b.hasCompactSupport.mul_left
  obtain ⟨S,hψ,hq⟩ := exists_fieldSignalData ψ hs hc (-3)
  refine ⟨S,hq,?_,?_⟩
  · intro x hx
    have hb : b x=1 := b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,b] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hb]
    norm_num
  · intro x hx
    have hb : b x=0 := b.zero_of_le_dist (by simpa only [dist_zero_right,b] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hb,mul_zero,add_zero]

theorem exists_secondBarrierSignal (ℓ : (ℝ×ℝ) →L[ℝ] ℝ) {R₁ : ℝ} (hR₁ : 0<R₁) :
    ∃S : FieldSignalData,S.q=-3 ∧
      (∀x,‖x‖≤R₁ → |ℓ x|≤1 → S.signal x=3) ∧
      (∀x,3≤|ℓ x| → S.signal x=-3) := by
  let α : ContDiffBump (0 : ℝ) := ⟨1,3,by norm_num,by norm_num⟩
  let β : ContDiffBump (0 : ℝ×ℝ) := ⟨R₁,R₁+1,hR₁,by linarith⟩
  let ψ : (ℝ×ℝ) → ℝ := fun x => 6*α (ℓ x)*β x
  have hs : ContDiff ℝ 2 ψ := (contDiff_const.mul (α.contDiff.comp ℓ.contDiff)).mul β.contDiff
  have hc : HasCompactSupport ψ := β.hasCompactSupport.mul_left
  obtain ⟨S,hψ,hq⟩ := exists_fieldSignalData ψ hs hc (-3)
  refine ⟨S,hq,?_,?_⟩
  · intro x hx hℓ
    have hα : α (ℓ x)=1 := α.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,α] using hℓ)
    have hβ : β x=1 := β.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,β] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hα,hβ]
    norm_num
  · intro x hx
    have hα : α (ℓ x)=0 := α.zero_of_le_dist (by simpa only [dist_zero_right,Real.norm_eq_abs,α] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hα,mul_zero,zero_mul,add_zero]

theorem conjugateLineForm_integral (a : ℕ) (j : Fin 4) (u : CutRing×CutRing) :
    conjugateLineForm a j (conjugate u.1,conjugate u.2)=conjugate (integralCutForm a j u) := by
  fin_cases j <;> simp [conjugateLineForm,lineNormal,integralCutForm] <;> ring

end BarrierSignals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierCore
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section BarrierCore
open Classical

theorem conjugateLineForm_site {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (z : FlagSite a m D v) (j : Fin 4) (c : CutRing)
    (hc : cutForm a j (barrierSitePoint z)=ordinary c) :
    conjugateLineForm a j (flagSiteConjugate z)=conjugate c := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hpoint : (ordinary (flagSiteNumerator z).1,ordinary (flagSiteNumerator z).2)=
      (D:ℝ) • barrierSitePoint z := by
    rw [show barrierSitePoint z=scaledOrdinary D (flagSiteNumerator z) from (flagSiteNumerator_spec z).symm]
    apply Prod.ext <;> simp [scaledOrdinary,mul_div_cancel₀ _ hD']
  have hlevel : integralCutForm a j (flagSiteNumerator z)=(D:CutRing)*c := by
    apply ordinary_injective
    rw [←cutForm_ordinary,hpoint,cutForm_smul,hc,map_mul,map_natCast]
  have hconj : flagSiteConjugate z=(D:ℝ)⁻¹ •
      (conjugate (flagSiteNumerator z).1,conjugate (flagSiteNumerator z).2) := by
    apply Prod.ext <;> simp [flagSiteConjugate,scaledConjugate,div_eq_mul_inv,mul_comm]
  rw [hconj,map_smul,conjugateLineForm_integral,hlevel,map_mul,map_natCast]
  simp [hD']

theorem conjugateIntersectionCoefficient_nonneg (a : ℕ) (i j : Fin 4) :
    0 ≤ conjugateIntersectionCoefficient a i j := by unfold conjugateIntersectionCoefficient; positivity

theorem conjugateLineForm_bound {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i≠j)
    (c d : ℝ) (p : ℝ×ℝ) (hi : conjugateLineForm a i p=c)
    (hj : conjugateLineForm a j p=d) {δ : ℝ} (hδ : 0≤δ) (hc : |c|≤δ) (hd : |d|≤δ) :
    ‖p‖ ≤ conjugateIntersectionCoefficient a i j*δ := by
  have hdet : conjugate (lineNormal a i).1*conjugate (lineNormal a j).2-
      conjugate (lineNormal a j).1*conjugate (lineNormal a i).2≠0 := by
    have hh := conjugate_injective.ne (lineDet_ne_zero ha i j hij)
    simpa only [lineDet,map_sub,map_mul,map_zero] using hh
  have hi' : conjugate (lineNormal a i).1*p.1+conjugate (lineNormal a i).2*p.2=c := by
    simpa [conjugateLineForm] using hi
  have hj' : conjugate (lineNormal a j).1*p.1+conjugate (lineNormal a j).2*p.2=d := by
    simpa [conjugateLineForm] using hj
  have hh := real_two_lines_distance_bound _ _ _ _ c d hdet p 0 hi' hj' δ hδ
    (by simpa using hc) (by simpa using hd)
  simpa [dist_zero_right,conjugateIntersectionCoefficient,lineDet] using hh

theorem exists_barrierIntersection_core {a : ℕ} (ha : 0<a) (Q B : ℝ) :
    ∃R : ℝ,0<R ∧ ∀N : ℝ,1≤N → ∀i j : Fin 4,i≠j → ∀c d : CutRing,
      |conjugate c|≤4*N+Q → |conjugate d|≤B → ∀p : ℝ×ℝ,
      conjugateLineForm a i p=conjugate c → conjugateLineForm a j p=conjugate d →
      ‖p‖≤R*N := by
  let C := ∑i : Fin 4,∑j : Fin 4,conjugateIntersectionCoefficient a i j
  have hC : 0≤C := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => conjugateIntersectionCoefficient_nonneg a i j))
  have hCij (i j : Fin 4) : conjugateIntersectionCoefficient a i j≤C := by
    apply (Finset.single_le_sum (fun k _ => conjugateIntersectionCoefficient_nonneg a i k)
      (Finset.mem_univ j)).trans
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      (fun l _ => conjugateIntersectionCoefficient_nonneg a k l)) (Finset.mem_univ i)
  let A := 4+|Q|+|B|
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨1+C*A,by positivity,?_⟩
  intro N hN i j hij c d hc hd p hi hj
  have hN₀ : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hc' : |conjugate c|≤A*N := by
    have hQ : |Q|≤|Q| *N := le_mul_of_one_le_right (abs_nonneg _) hN
    have hBN : 0≤|B| *N := mul_nonneg (abs_nonneg _) hN₀.le
    dsimp [A]; nlinarith [le_abs_self Q]
  have hd' : |conjugate d|≤A*N := by
    have hB : |B|≤|B| *N := le_mul_of_one_le_right (abs_nonneg _) hN
    have hQN : 0≤|Q| *N := mul_nonneg (abs_nonneg _) hN₀.le
    dsimp [A]; nlinarith [le_abs_self B]
  have hh := conjugateLineForm_bound ha i j hij (conjugate c) (conjugate d) p hi hj
    (mul_nonneg hA.le hN₀.le) hc' hd'
  calc
    ‖p‖ ≤ conjugateIntersectionCoefficient a i j*(A*N) := hh
    _ ≤ C*(A*N) := mul_le_mul_of_nonneg_right (hCij i j) (by positivity)
    _ ≤ (1+C*A)*N := by nlinarith

theorem exists_barrierIncoming_core {a : ℕ} (ha : 0<a) :
    ∃R : ℝ,0<R ∧ ∀m : ℕ,∀i : Fin m,∀N : ℝ,1≤N → ∀j : Fin 4,∀c : CutRing,
      ∀hc : c∈barrierCandidate a j N,
      ‖flagSiteConjugate (barrierIncomingSite ha i hc)‖≤R*N := by
  obtain ⟨R,hR,hcore⟩ := exists_barrierIntersection_core ha 0 0
  refine ⟨R,hR,?_⟩
  intro m i N hN j c hc
  obtain ⟨k,hkj,hk⟩ := barrierIncoming_edge hc
  apply hcore N hN j k hkj.symm c 0 (by simpa using hc.1) (by simp)
  · apply conjugateLineForm_site (commonVertexDenominator_pos ha)
    exact cutForm_barrierLinePoint a j c _
  · apply conjugateLineForm_site (commonVertexDenominator_pos ha)
    exact hk

end BarrierCore

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierSignalSystem
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section BarrierSignalSystem
open Classical Set

theorem exists_barrierSignalSystem {a : ℕ} (ha : 0 < a) (Q B : ℝ) :
    Nonempty (BarrierSignalSystem a ha Q B) := by
  obtain ⟨R,hR,hcore⟩ := exists_barrierIntersection_core ha Q B
  obtain ⟨T,hT,hin⟩ := exists_barrierIncoming_core ha
  let R₀ := R+T+1
  let R₁ := R₀+2
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  have hR₁ : 0 < R₁ := by dsimp [R₁]; linarith
  obtain ⟨first,hq,hp,hn⟩ := exists_firstBarrierSignal hR₀ (show R₀ < R₁ by dsimp [R₁]; linarith)
  choose second hsq hsp hsn using fun j : Fin 4 => exists_secondBarrierSignal (conjugateLineForm a j) hR₁
  refine ⟨⟨R₀,R₁,hR₀,by dsimp [R₁]; linarith,first,second,hq,hsq,hp,hn,hsp,hsn,?_,?_⟩⟩
  · intro N hN i j hij c d hc hd p hi hj
    exact (hcore N hN i j hij c d hc hd p hi hj).trans
      (mul_le_mul_of_nonneg_right (by dsimp [R₀]; linarith) (by linarith))
  · intro m i N hN j c hc
    exact (hin m i N hN j c hc).trans
      (mul_le_mul_of_nonneg_right (by dsimp [R₀]; linarith) (by linarith))

end BarrierSignalSystem

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ObservableProducts
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
section ObservableProducts
open Classical MeasureTheory Set

theorem ObservableClose.refl {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    ObservableClose μ μ 0 := by
  intro f hf hb
  simp

theorem ObservableClose.trans {X : Type*} [MeasurableSpace X]
    {μ ν ρ : Measure X} {ε δ : ℝ} (h : ObservableClose μ ν ε) (k : ObservableClose ν ρ δ) :
    ObservableClose μ ρ (ε+δ) := by
  intro f hf hb
  exact (abs_sub_le _ _ _).trans (add_le_add (h f hf hb) (k f hf hb))

theorem ObservableClose.prod_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {ε : ℝ} (h : ObservableClose μ ν ε) :
    ObservableClose (ρ.prod μ) (ρ.prod ν) ε := by
  have hh := (h.prod_right ρ).map measurable_swap
  simpa only [Measure.prod_swap] using hh

theorem ObservableClose.prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ρ σ : Measure Y} [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    {ε δ : ℝ} (h : ObservableClose μ ν ε) (k : ObservableClose ρ σ δ) :
    ObservableClose (μ.prod ρ) (ν.prod σ) (ε+δ) :=
  (h.prod_right ρ).trans (k.prod_left ν)

theorem ObservableClose.fin_pi (n : ℕ) {X : Fin n → Type*} [∀i,MeasurableSpace (X i)]
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (ε : Fin n → ℝ) (h : ∀i,ObservableClose (μ i) (ν i) (ε i)) :
    ObservableClose (Measure.pi μ) (Measure.pi ν) (∑i,ε i) := by
  induction n with
  | zero =>
    have he : μ=ν := by funext i; exact Fin.elim0 i
    subst ν
    simpa using ObservableClose.refl (Measure.pi μ)
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove X (0 : Fin (n+1))
    have hμ := (measurePreserving_piFinSuccAbove μ (0 : Fin (n+1))).symm.map_eq
    have hν := (measurePreserving_piFinSuccAbove ν (0 : Fin (n+1))).symm.map_eq
    have hi := ih (fun i => μ ((0 : Fin (n+1)).succAbove i))
      (fun i => ν ((0 : Fin (n+1)).succAbove i))
      (fun i => ε ((0 : Fin (n+1)).succAbove i)) (fun i => h _)
    have hh := ((h 0).prod hi).map e.symm.measurable
    rw [hμ,hν] at hh
    simpa only [Fin.succAbove_zero,Fin.sum_univ_succ] using hh

end ObservableProducts

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

theorem jointBitFieldLaw_transport {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (F : Finset (polygonFullGroup a m))
    {ε : ℝ} (hε : 0<ε) :
    ∃η κ : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ ∀ᶠn : ℕ in atTop,∀g∈F,
      ObservableClose (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n)
        ((jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n).map (jointBitReindex v hD g)) ε := by
  have hk : (0:ℝ)<(k:ℝ)+1 := by positivity
  obtain ⟨η,κ,hη,hη₁,hκ,ht⟩ := finiteSignalFields_transport v S hD F (div_pos hε hk)
  refine ⟨η,κ,hη,hη₁,hκ,?_⟩
  filter_upwards [ht] with n hn g hg
  let μ (j : Fin k) := (S j).bitLaw (a:=a) (m:=m) (v:=v j) hD η κ n
  have (j : Fin k) : IsProbabilityMeasure ((μ j).map (bitReindex (flagSitePermutation hD g))) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (bitReindex_measurable _).aemeasurable)
  have hh := ObservableClose.fin_pi k μ
    (fun j => (μ j).map (bitReindex (flagSitePermutation hD g)))
    (fun _ => ε/((k:ℝ)+1)) (fun j => hn g hg j)
  rw [← Measure.pi_map_pi (fun j => (bitReindex_measurable (flagSitePermutation (v:=v j) hD g)).aemeasurable)] at hh
  apply hh.mono
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hk).mpr (by nlinarith)

end JointBitField

section JointFieldSuccess
open Classical MeasureTheory Filter Set
open scoped Topology

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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section BarrierFiniteMenu
open Classical Set

theorem barrier_uniform_constants {a m : ℕ} (F : Finset (polygonFullGroup a m)) :
    ∃Q B : ℝ,0 ≤ Q ∧ 0 ≤ B ∧ ∀g ∈ F,∀i (p : GenericSquare a),
      (∀j,|conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| ≤ Q) ∧
      (∀l ∈ barrierChartCuts g i ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
        |conjugate (l.2+integralCutForm a l.1 (fullGroupAffineData g i p).2)| ≤ B) := by
  let R (g : polygonFullGroup a m) (i : Fin m) :=
    (squareArrangement_finite_range (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i)).toFinset
  let C (g : polygonFullGroup a m) (i : Fin m) : ℝ := ∑d ∈ R g i,∑j : Fin 4,|conjugate (integralCutForm a j d.2)|
  have hC (g : polygonFullGroup a m) (i : Fin m) : 0 ≤ C g i :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  let Q : ℝ := ∑g ∈ F,∑i,C g i
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun g _ => Finset.sum_nonneg (fun i _ => hC g i))
  have hshift (g : polygonFullGroup a m) (hg : g ∈ F) (i : Fin m) (p : GenericSquare a) (j : Fin 4) :
      |conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| ≤ Q := by
    have hd : fullGroupAffineData g i p ∈ R g i := (Set.Finite.mem_toFinset _).mpr ⟨p,rfl⟩
    calc
      _ ≤ ∑j : Fin 4,|conjugate (integralCutForm a j (fullGroupAffineData g i p).2)| :=
        Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ C g i := by
        dsimp [C]
        exact Finset.single_le_sum (s := R g i) (f := fun d : Fin m × (CutRing × CutRing) => ∑j : Fin 4, |conjugate (integralCutForm a j d.2)|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hd
      _ ≤ ∑i,C g i := Finset.single_le_sum (fun i _ => hC g i) (Finset.mem_univ i)
      _ ≤ Q := Finset.single_le_sum (fun g _ => Finset.sum_nonneg (fun i _ => hC g i)) hg
  let D (g : polygonFullGroup a m) (i : Fin m) : ℝ := ∑l ∈ barrierChartCuts g i ∪ squareBoundaryCuts,|conjugate l.2|
  have hD (g : polygonFullGroup a m) (i : Fin m) : 0 ≤ D g i := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let L : ℝ := ∑g ∈ F,∑i,D g i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun g _ => Finset.sum_nonneg (fun i _ => hD g i))
  have hlevel (g : polygonFullGroup a m) (hg : g ∈ F) (i : Fin m)
      (l : PlaneCut) (hl : l ∈ barrierChartCuts g i ∪ squareBoundaryCuts) : |conjugate l.2| ≤ L := by
    calc
      _ ≤ D g i := Finset.single_le_sum (fun _ _ => abs_nonneg _) hl
      _ ≤ ∑i,D g i := Finset.single_le_sum (fun i _ => hD g i) (Finset.mem_univ i)
      _ ≤ L := Finset.single_le_sum (fun g _ => Finset.sum_nonneg (fun i _ => hD g i)) hg
  refine ⟨Q,L+Q,hQ,add_nonneg hL hQ,?_⟩
  intro g hg i p
  refine ⟨hshift g hg i p,?_⟩
  intro l hl
  refine ⟨by linarith [hlevel g hg i l hl],?_⟩
  rw [map_add]
  exact (abs_add_le _ _).trans (add_le_add (hlevel g hg i l hl) (hshift g hg i p l.1))

theorem exists_barrierMenu {a m : ℕ} (ha : 0 < a) (F : Finset (polygonFullGroup a m)) :
    Nonempty (BarrierMenu a m ha F) := by
  obtain ⟨Q,B,hQ,hB,hall⟩ := barrier_uniform_constants F
  obtain ⟨S⟩ := exists_barrierSignalSystem ha Q B
  exact ⟨⟨Q,B,hQ,hB,S,fun g hg i p => (hall g hg i p).1,fun g hg i p => (hall g hg i p).2⟩⟩

end BarrierFiniteMenu

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

theorem matchingSupport_nonempty {a m : ℕ} (P : TrackPolygonPartition a m) : (matchingSupport P).Nonempty := by
  obtain ⟨g,hg⟩ := partitionBaseline_related P
  exact ⟨g,(mem_matchingSupport P g).mpr hg⟩

end UniformShapeMatchings

section FiniteSupportedLaws
open Classical MeasureTheory Set

theorem integral_of_finite_support {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T) (f : X → ℝ) :
    (∫x,f x ∂μ)=∑x∈T,μ.real {x}*f x := by
  have he : f=ᵐ[μ] fun x => ∑z∈T,({z} : Set X).indicator (fun _ => f z) x := by
    filter_upwards [hT] with x hx
    symm
    rw [Finset.sum_eq_single x]
    · simp
    · intro _ _ distinct
      simp [Set.indicator_of_notMem,Ne.symm distinct]
    · exact fun hn => (hn hx).elim
  rw [integral_congr_ae he,integral_finsetSum T (fun z _ =>
    (integrable_const (f z)).indicator (measurableSet_singleton z))]
  apply Finset.sum_congr rfl
  intro point _
  rw [integral_indicator_const (f point) (measurableSet_singleton point)]
  rfl

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

section FiniteMixtureWeights
open Classical

theorem finiteUniformWeight_nonneg {G : Type*} (U : Finset G) (x : G) :
    0 ≤ finiteUniformWeight U x := by unfold finiteUniformWeight; split_ifs <;> positivity

theorem finiteUniformWeight_sum {G : Type*} (S U : Finset G) (hUS : U ⊆ S) (f : G → ℝ) :
    (∑x∈S,finiteUniformWeight U x*f x)=(∑x∈U,f x)/U.card := by
  calc
    _ = ∑x∈U,finiteUniformWeight U x*f x := by
      symm
      apply Finset.sum_subset hUS
      intro x hx hxU
      simp [finiteUniformWeight,hxU]
    _ = ∑x∈U,f x/(U.card:ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [finiteUniformWeight,hx,div_eq_mul_inv,mul_comm]
    _ = _ := by rw [Finset.sum_div]

theorem finite_uniform_mixture {X G : Type*} (T : Finset X) (w : X → ℝ) (U : X → Finset G)
    (hw : ∀x∈T,0 ≤ w x) (hmass : (∑x∈T,w x)=1) (hU : ∀x∈T,(U x).Nonempty) :
    ∃ (S : Finset G) (p : G → ℝ), (∀g,0 ≤ p g) ∧ (∀g∉S,p g=0) ∧ (∑g∈S,p g)=1 ∧
      ∀f : G → ℝ,(∑g∈S,p g*f g)=∑x∈T,w x*((∑g∈U x,f g)/(U x).card) := by
  let S := T.biUnion U
  let p := fun g => ∑x∈T,w x*finiteUniformWeight (U x) g
  have hcontains (x : X) (hx : x∈T) : U x ⊆ S := by
    intro g hg
    exact Finset.mem_biUnion.mpr ⟨x,hx,hg⟩
  have htest (f : G → ℝ) : (∑g∈S,p g*f g)=∑x∈T,w x*((∑g∈U x,f g)/(U x).card) := by
    simp only [p,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [mul_assoc]
    rw [←Finset.mul_sum,finiteUniformWeight_sum S (U x) (hcontains x hx)]
  refine ⟨S,p,fun g => Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx)
    (finiteUniformWeight_nonneg (U x) g)),?_,?_,htest⟩
  · intro g hg
    apply Finset.sum_eq_zero
    intro x hx
    have hgU : g∉U x := fun h => hg (hcontains x hx h)
    simp [finiteUniformWeight,hgU]
  · have hh := htest (fun _ => 1)
    simp only [mul_one,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    rw [hh]
    calc
      (∑x∈T,w x*(((U x).card:ℝ)/(U x).card)) = ∑x∈T,w x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hcard : ((U x).card:ℝ)≠0 := by exact_mod_cast (hU x hx).card_pos.ne'
        field_simp
      _ = 1 := hmass

end FiniteMixtureWeights

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

theorem matchingLaw_finite_weights {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {a m : ℕ} (μ : Measure X) [IsProbabilityMeasure μ] (T : Finset X)
    (hT : ∀ᵐx ∂μ,x∈T) (P : X → TrackPolygonPartition a m) :
    ∃(S : Finset (polygonFullGroup a m)) (p : polygonFullGroup a m → ℝ),
      (∀g,0 ≤ p g) ∧ (∀g∉S,p g=0) ∧ (∑g∈S,p g)=1 ∧
      ∀f : polygonFullGroup a m → ℝ,(∑g∈S,p g*f g)=∫x,matchingAverage (P x) f ∂μ := by
  have hmass : (∑x∈T,μ.real {x})=1 := by
    have hh := integral_of_finite_support μ T hT (fun _ => (1:ℝ))
    simpa using hh.symm
  obtain ⟨S,p,hp,hs,hm,ht⟩ := finite_uniform_mixture T (fun x => μ.real {x})
    (fun x => matchingSupport (P x)) (fun _ _ => measureReal_nonneg) hmass
    (fun x _ => matchingSupport_nonempty (P x))
  refine ⟨S,p,hp,hs,hm,?_⟩
  intro f
  rw [integral_of_finite_support μ T hT]
  exact ht f

theorem polygonFullGroup_finiteTestReiter_oai {a m : ℕ} (ha : 0 < a) :
    FiniteTestReiter (polygonFullGroup a m) := by
  intro F ε hε
  obtain ⟨M⟩ := exists_barrierMenu ha F
  obtain ⟨η,κ,hη,hη₁,hκ,ht⟩ := jointBitFieldLaw_transport (a:=a) (m:=m)
    (barrierEightDirections ha) M.signals.eight (commonVertexDenominator_pos ha) F
    (show 0 < ε/8 by linarith)
  let μ (n : ℕ) := jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
    (commonVertexDenominator_pos ha) η κ n
  have hs : ∀ᶠn : ℕ in atTop,(μ n).real
      {b | ¬jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b} < ε/8 :=
    (jointBitFieldLaw_success (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
      (commonVertexDenominator_pos ha) hη hκ).eventually (gt_mem_nhds (by linarith))
  have hscale : ∀ᶠn : ℕ in atTop,M.Q < sourceDyadicN n ∧ M.B ≤ sourceDyadicN n := by
    filter_upwards [sourceDyadic_radius_eventually (max (M.Q+1) M.B)] with n hn
    have hnN : (2:ℝ)^n ≤ sourceDyadicN n := by
      unfold sourceDyadicN
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact ⟨lt_of_lt_of_le (by linarith [(le_max_left (M.Q+1) M.B).trans hn]) hnN,
      ((le_max_right (M.Q+1) M.B).trans hn).trans hnN⟩
  obtain ⟨n,hn,hsn,hN⟩ := (ht.and (hs.and hscale)).exists
  obtain ⟨T,hT⟩ := jointBitFieldLaw_finite_support (a:=a) (m:=m) (barrierEightDirections ha)
    M.signals.eight M.signals.eight_q (commonVertexDenominator_pos ha) η κ n
  obtain ⟨S,p,hp,hsupp,hm,havg⟩ := matchingLaw_finite_weights (μ n) T hT (M.signals.sampledPartition n)
  refine ⟨S,p,hp,hsupp,hm,?_⟩
  intro g hg f hf
  rw [havg,havg]
  have hh := M.matching_expectation_covariance hN.1 hN.2 g hg (hn g hg) f hf
  exact hh.trans (by change 2*(μ n).real _+2*(ε/8) ≤ ε; linarith)

end PolygonMatchingLaw

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter_oai := @OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter_oai
