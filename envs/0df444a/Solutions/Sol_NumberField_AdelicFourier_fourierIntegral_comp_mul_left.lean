-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_comp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/88eab927-e1dd-5b91-9057-8b6aba6b7692

import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left

set_option autoImplicit false

noncomputable section

section CountabilitySupply

p2m_open "IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField TopologicalSpace Filter"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing of_module_finite mk InfinitePlace AdeleRing"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "fourierIntegral fourierIntegral_def"
namespace R8Supply
p2m_open "NumberField.AdelicFourier NumberField"

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

end NumberField.AdelicFourier.R8Supply
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier.R8Supply"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField"

end CountabilitySupply
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier.R8Supply"

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier TopologicalSpace"
open scoped NNReal

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing of_module_finite mk InfinitePlace AdeleRing"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "fourierIntegral fourierIntegral_def"
p2m_open "NumberField.AdelicFourier NumberField"

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem countable_ringOfIntegers' : Countable (𝓞 F) := Countable.of_module_finite ℤ (𝓞 F)

theorem neg_mul_eq_neg_units_mul (a : 𝔸ˣ) (v w : 𝔸) : -(v * w) = -((↑a * v) * (↑a⁻¹ * w)) := by
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

theorem fourierIntegral_comp_mul_left_impl [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] (ψ : AddChar 𝔸 ℂ) (f : 𝔸 → ℂ) (a : 𝔸ˣ) (w : 𝔸) :
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((distribHaarChar 𝔸 a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) := by
  haveI : Countable (𝓞 F) := countable_ringOfIntegers' F
  haveI : SecondCountableTopology 𝔸 := R8Supply.instSecondCountableAdeleRing (𝓞 F) F

  set G : 𝔸 → ℂ := fun u => ψ (-(u * (↑a⁻¹ * w))) * f u with hG
  have hint : fourierIntegral ψ μ (fun v => f (a * v)) w = ∫ v, G (a • v) ∂μ := by
    rw [fourierIntegral_def]
    congr 1
    funext v
    simp only [hG, Units.smul_def, smul_eq_mul]
    rw [neg_mul_eq_neg_units_mul F a v w]
  have hdom : ∫ v, G (a • v) ∂μ = ∫ u, G u ∂(DomMulAct.mk a⁻¹ • μ) := by
    rw [integral_domSMul]
    simp
  have huniq : (DomMulAct.mk a⁻¹ • μ : Measure 𝔸) = (distribHaarChar 𝔸 a)⁻¹ • μ := by
    have h := isAddLeftInvariant_eq_smul (DomMulAct.mk a⁻¹ • μ) μ
    rwa [addHaarScalarFactor_smul_eq_distribHaarChar μ a⁻¹, map_inv (distribHaarChar 𝔸) a] at h
  rw [hint, hdom, huniq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
    Complex.ofReal_inv]
  rfl

#print axioms fourierIntegral_comp_mul_left_impl

example : ∀ [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddHaarMeasure] (ψ : AddChar 𝔸 ℂ) (f : 𝔸 → ℂ)
    (a : 𝔸ˣ) (w : 𝔸),
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((distribHaarChar 𝔸 a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) :=
  fun μ _ ψ f a w => fourierIntegral_comp_mul_left_impl F μ ψ f a w

end NumberField.AdelicFourier
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier.R8Supply"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier.R8Supply"

end
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier.R8Supply"

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.NumberField.AdelicFourier"

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) := by
  exact NumberField.AdelicFourier.fourierIntegral_comp_mul_left_impl F μ ψ f a w

end S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left (solution)
