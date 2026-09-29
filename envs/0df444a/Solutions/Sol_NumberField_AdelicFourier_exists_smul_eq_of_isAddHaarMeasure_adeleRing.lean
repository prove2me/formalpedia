-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/599049c0-82fd-5cf7-bf6b-407e391968f9

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing

set_option Elab.async false

noncomputable section

section CountabilitySupply

p2m_open "IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField TopologicalSpace Filter"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing of_module_finite InfinitePlace AdeleRing"
namespace AdelicFourier
namespace HHaarSupply
p2m_open "NumberField"

scoped instance instCountableIdeal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I)
    exact ⟨s, hs⟩
  exact hsurj.countable

scoped instance instCountableHeightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Countable R] : Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := by
    intro v w h
    exact HeightOneSpectrum.ext h
  exact hinj.countable

scoped instance instCountableValueGroup₀ {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
    [Countable Γ₀] (v : R →*₀ Γ₀) : Countable (MonoidWithZeroHom.ValueGroup₀ v) :=
  MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective.countable

scoped instance instCountableUnits {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Units.val_injective.countable

scoped instance instCountableWithZero {α : Type*} [Countable α] : Countable (WithZero α) := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
  refine ⟨⟨fun x => if h : x = 0 then 0 else f (WithZero.unzero h) + 1, fun a b hab => ?_⟩⟩
  dsimp only [] at hab
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · rw [ha, hb]
  · rw [dif_pos ha, dif_neg hb] at hab
    exact absurd hab.symm (Nat.succ_ne_zero _)
  · rw [dif_neg ha, dif_pos hb] at hab
    exact absurd hab (Nat.succ_ne_zero _)
  · rw [dif_neg ha, dif_neg hb] at hab
    rw [← WithZero.coe_unzero ha, ← WithZero.coe_unzero hb, hf (Nat.add_right_cancel hab)]

theorem isCountablyGenerated_uniformity_of_valued (R : Type*) (Γ₀ : Type*) [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] [Countable Γ₀] [vR : Valued R Γ₀] :
    (uniformity R).IsCountablyGenerated :=
  (Valued.hasBasis_uniformity R Γ₀).isCountablyGenerated

scoped instance instSecondCountableAdicCompletion (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable K] (v : HeightOneSpectrum R) :
    SecondCountableTopology (v.adicCompletion K) := by
  have hcg : (uniformity (v.adicCompletion K)).IsCountablyGenerated :=
    isCountablyGenerated_uniformity_of_valued _ (WithZero (Multiplicative ℤ))
  have hsep : SeparableSpace (v.adicCompletion K) := by
    have : Countable (WithVal (v.valuation K)) :=
      (WithVal.equiv (v.valuation K)).toEquiv.injective.countable
    exact ⟨_, Set.countable_range (fun k : WithVal (v.valuation K) => (k : v.adicCompletion K)),
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K v).denseRange.comp
        UniformSpace.Completion.denseRange_coe
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v)⟩
  exact UniformSpace.secondCountable_of_separable _

open RestrictedProduct Topology in
theorem secondCountableTopology_restrictedProduct {ι : Type*} [Countable ι]
    {R : ι → Type*} {B : ∀ i, Set (R i)}
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    (hBo : ∀ i, IsOpen (B i)) :
    SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.cofinite]) := by

  have hprin : ∀ t : Finset ι, Filter.cofinite ≤ Filter.principal ((↑t : Set ι)ᶜ) := fun t =>
    Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr (by simp))

  have hpiece : ∀ t : Finset ι,
      SecondCountableTopology (Πʳ i, [R i, B i]_[Filter.principal ((↑t : Set ι)ᶜ)]) := fun t =>
    (isEmbedding_coe_of_principal).secondCountableTopology

  set U : Finset ι → Set (Πʳ i, [R i, B i]_[Filter.cofinite]) :=
    fun t => Set.range (inclusion R B (hprin t)) with hU
  have hUopen : ∀ t, IsOpen (U t) := fun t =>
    (isOpenEmbedding_inclusion_principal hBo (hprin t)).isOpen_range
  have hUsc : ∀ t, SecondCountableTopology (U t) := by
    intro t
    haveI := hpiece t
    exact (((isOpenEmbedding_inclusion_principal hBo (hprin t)).isEmbedding.toHomeomorph).symm).isEmbedding.secondCountableTopology
  have hcover : ⋃ t : Finset ι, U t = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hfin : {i | x.1 i ∉ B i}.Finite := Filter.eventually_cofinite.mp x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    rw [Filter.eventually_principal]
    intro i hi
    by_contra hmem
    exact hi (by simpa using hfin.mem_toFinset.mpr hmem)
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hUopen hcover

open IsDedekindDomain in
open scoped RestrictedProduct in

scoped instance instSecondCountableFiniteAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Countable R] [Countable K] :
    SecondCountableTopology (FiniteAdeleRing R K) := by
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    secondCountableTopology_restrictedProduct fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

scoped instance instSecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SeparableSpace v.Completion :=
      ⟨_, Set.countable_range (fun k : WithAbs v.1 => (k : v.Completion)),
        (NumberField.InfinitePlace.Completion.ofCompletion_surjective v).denseRange.comp
          UniformSpace.Completion.denseRange_coe
          (NumberField.InfinitePlace.Completion.continuous_ofCompletion v)⟩
    exact UniformSpace.secondCountable_of_separable _
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

scoped instance instSecondCountableAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K] [Countable R] :
    SecondCountableTopology (AdeleRing R K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing R K)

end NumberField.AdelicFourier.HHaarSupply
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField.AdelicFourier.HHaarSupply"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField.AdelicFourier"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField"

end CountabilitySupply
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField.AdelicFourier.HHaarSupply"

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure TopologicalSpace"
open scoped NNReal

namespace NumberField p2m_export "NumberField" "InfiniteAdeleRing of_module_finite InfinitePlace AdeleRing" namespace AdelicFourier end NumberField.AdelicFourier
p2m_open_scoped "NumberField" in

theorem NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing_impl (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧ μ = c • ν := by
  haveI : Countable (𝓞 F) := Countable.of_module_finite ℤ (𝓞 F)
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
    NumberField.AdelicFourier.HHaarSupply.instSecondCountableAdeleRing (𝓞 F) F
  exact ⟨addHaarScalarFactor μ ν, addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν, isAddLeftInvariant_eq_smul μ ν⟩

example : ∀ (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure],
    ∃ c : NNReal, 0 < c ∧ μ = c • ν :=
  fun F _ _ _ _ μ ν _ _ => NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing_impl F μ ν

end
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField.AdelicFourier.HHaarSupply"

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.NumberField"

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧ μ = c • ν := by
  first
    | exact NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing_impl F μ ν
    | (apply NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing_impl <;> assumption)

end S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing (solution)
