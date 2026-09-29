-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_pureTensor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c2845eac-9a2c-5a5d-a1f6-50f5bb4357f5

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

section CountabilitySupply

p2m_open "IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField TopologicalSpace Filter"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding.span_latticeBasis mk mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace mixedEmbedding.latticeBasis InfinitePlace AdeleRing mixedEmbedding.integerLattice"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "fourierIntegral fourierIntegral_def"
namespace Ws25Supply
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

scoped instance instSecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] [Countable K] :
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

end NumberField.AdelicFourier.Ws25Supply
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25Supply"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField"

end CountabilitySupply
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25Supply"

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory MeasureTheory.Measure TopologicalSpace"

open scoped Classical nonZeroDivisors NNReal ENNReal

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding.span_latticeBasis mk mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace mixedEmbedding.latticeBasis InfinitePlace AdeleRing mixedEmbedding.integerLattice"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "fourierIntegral fourierIntegral_def"
namespace Ws25
p2m_open "NumberField.AdelicFourier NumberField"

variable (F : Type) [Field F] [NumberField F]

theorem countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

theorem countable_ringOfIntegers : Countable (𝓞 F) :=
  (Module.Free.chooseBasis ℤ (𝓞 F)).equivFun.injective.countable

section Split

theorem isOpenMap_ringEquiv_mixedSpace : IsOpenMap (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  haveI : Countable F := countable_numberField F
  exact AddMonoidHom.isOpenMap_of_sigmaCompact
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddMonoidHom
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).surjective (continuous_ringEquiv_mixedSpace F)

def eHomeo : InfiniteAdeleRing F ≃ₜ (mixedEmbedding.mixedSpace F) where
  toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace F
  continuous_invFun := by
    refine continuous_def.2 fun s hs => ?_
    rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv.invFun ⁻¹' s
        = (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv '' s from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv.image_eq_preimage_symm s).symm]
    exact isOpenMap_ringEquiv_mixedSpace F s hs

@[scoped simp] theorem eHomeo_apply (x : InfiniteAdeleRing F) :
    eHomeo F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := rfl

def split : (AdeleRing (𝓞 F) F) ≃ₜ+ mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F :=
  ContinuousAddEquiv.mk' ((eHomeo F).prodCongr (Homeomorph.refl _)) fun x y => by
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F (x + y).1, (x + y).2)
        : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F)
      = (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)
        + (InfiniteAdeleRing.ringEquiv_mixedSpace F y.1, y.2)
    rw [Prod.mk_add_mk, ← map_add]
    rfl

@[scoped simp] theorem split_apply (x : (AdeleRing (𝓞 F) F)) :
    split F x = (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2) := rfl

theorem split_image_adelicBox :
    ⇑(split F) '' adelicBox F
      = ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) ×ˢ integralFiniteAdeles (𝓞 F) F := by
  ext ⟨a, b⟩
  simp only [Set.mem_image, split_apply, Prod.mk.injEq, Set.mem_prod]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl, rfl⟩
    exact ⟨hx1, hx2⟩
  · rintro ⟨ha, hb⟩
    refine ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, b), ⟨?_, hb⟩,
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a, rfl⟩
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)
      ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [RingEquiv.apply_symm_apply]
    exact ha

end Split
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25Supply"

theorem covolume_integerLattice_eq_toReal :
    ZLattice.covolume (mixedEmbedding.integerLattice F) volume
      = (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))).toReal := by
  have key : ∀ (L : Submodule ℤ (mixedEmbedding.mixedSpace F)) [DiscreteTopology L] [IsZLattice ℝ L],
      L = Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) →
      ZLattice.covolume L volume
        = (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))).toReal := by
    intro L _ _ hL
    subst hL
    exact ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain (mixedEmbedding.latticeBasis F) volume)
  exact key _ (mixedEmbedding.span_latticeBasis F).symm

theorem addChar_prod_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (x : (AdeleRing (𝓞 F) F)) :
    ψ x = ψ (x.1, 0) * ψ (0, x.2) := by
  conv_lhs => rw [show x = ((x.1, 0) : (AdeleRing (𝓞 F) F)) + ((0, x.2) : (AdeleRing (𝓞 F) F)) from
    Prod.ext (by simp) (by simp)]
  exact AddChar.map_add_eq_mul ψ _ _

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]

theorem fourierIntegral_pureTensor_eq_impl
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (g : (mixedEmbedding.mixedSpace F) → ℂ) (h : (FiniteAdeleRing (𝓞 F) F) → ℂ) (w : (AdeleRing (𝓞 F) F)) :
    fourierIntegral ψ μ
        (fun x ↦ g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2) w
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ)
        * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            volume g (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
        * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν h w.2 := by

  haveI : Countable F := countable_numberField F
  haveI : Countable (𝓞 F) := countable_ringOfIntegers F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := inferInstance
  haveI : SecondCountableTopology (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := inferInstance
  haveI : BorelSpace (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := Prod.borelSpace
  haveI : SigmaFinite ν := inferInstance

  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he
  set ψV : AddChar (mixedEmbedding.mixedSpace F) ℂ :=
    ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp e.symm.toAddMonoidHom) with hψV
  set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr _ _) with hψf
  set π : Measure (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := (volume : Measure (mixedEmbedding.mixedSpace F)).prod ν with hπ
  haveI hπHaar : π.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set μ' : Measure (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := μ.map ⇑(split F) with hμ'
  haveI hμ'Haar : μ'.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ (split F)

  set c : ℝ≥0 := μ'.addHaarScalarFactor π with hc
  have huniq : μ' = c • π := Measure.isAddLeftInvariant_eq_smul μ' π

  set Φm : (AdeleRing (𝓞 F) F) ≃ᵐ mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F := (split F).toHomeomorph.toMeasurableEquiv with hΦm
  have hΦm_coe : ⇑Φm = ⇑(split F) := rfl

  have hbox : μ (adelicBox F)
      = c * (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))
          * ν (integralFiniteAdeles (𝓞 F) F)) := by
    have h1 : μ (adelicBox F) = μ' (⇑(split F) '' adelicBox F) := by
      rw [hμ', ← hΦm_coe, MeasurableEquiv.map_apply, Φm.preimage_image]
    rw [h1, huniq, Measure.smul_apply, split_image_adelicBox, hπ, Measure.prod_prod,
      ENNReal.smul_def, smul_eq_mul]
  have hcov := covolume_integerLattice_eq_toReal F
  have hc_eq : (c : ℝ) = (μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) := by
    have hne1 : ZLattice.covolume (mixedEmbedding.integerLattice F) volume ≠ 0 :=
      ZLattice.covolume_ne_zero _ _
    have hne2 : (ν (integralFiniteAdeles (𝓞 F) F)).toReal ≠ 0 := by
      refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
      · exact ((isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, fun v => zero_mem _⟩).ne'
      · exact (isCompact_integralFiniteAdeles F).measure_lt_top.ne
    rw [eq_div_iff (mul_ne_zero hne1 hne2), hcov, ← ENNReal.coe_toReal c, ← ENNReal.toReal_mul,
      ← ENNReal.toReal_mul, hbox]

  set G₁ : (mixedEmbedding.mixedSpace F) → ℂ := fun a => ψV (-(a * e w.1)) * g a with hG₁
  set G₂ : (FiniteAdeleRing (𝓞 F) F) → ℂ := fun b => ψf (-(b * w.2)) * h b with hG₂
  have hint : ∀ x : (AdeleRing (𝓞 F) F),
      ψ (-(x * w)) * (g (e x.1) * h x.2) = G₁ (split F x).1 * G₂ (split F x).2 := by
    intro x
    have hsplit := addChar_prod_apply F ψ (-(x * w))
    have h1 : ψ ((-(x * w)).1, 0) = ψV (-(e x.1 * e w.1)) := by
      rw [hψV, AddChar.compAddMonoidHom_apply]
      congr 1
      change ((-(x * w)).1, (0 : FiniteAdeleRing (𝓞 F) F)) = (e.symm (-(e x.1 * e w.1)), 0)
      rw [map_neg, map_mul, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
      rfl
    have h2 : ψ (0, (-(x * w)).2) = ψf (-(x.2 * w.2)) := by
      rw [hψf, AddChar.compAddMonoidHom_apply]
      rfl
    rw [hsplit, h1, h2]
    simp only [split_apply, hG₁, hG₂]
    ring

  calc fourierIntegral ψ μ (fun x ↦ g (e x.1) * h x.2) w
      = ∫ x, G₁ (split F x).1 * G₂ (split F x).2 ∂μ := by
        rw [fourierIntegral_def]; exact integral_congr_ae (Filter.Eventually.of_forall hint)
    _ = ∫ x, (fun p : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F => G₁ p.1 * G₂ p.2) (Φm x) ∂μ := by rfl
    _ = ∫ p, G₁ p.1 * G₂ p.2 ∂μ' := by
        rw [hμ', ← hΦm_coe]; exact (integral_map_equiv Φm (fun p => G₁ p.1 * G₂ p.2)).symm
    _ = (c : ℝ) • ∫ p, G₁ p.1 * G₂ p.2 ∂π := by
        rw [huniq, integral_smul_nnreal_measure]; rfl
    _ = (c : ℝ) • ((∫ a, G₁ a ∂volume) * ∫ b, G₂ b ∂ν) := by rw [hπ, integral_prod_mul]
    _ = ((c : ℝ) : ℂ) * (∫ a, G₁ a ∂volume) * ∫ b, G₂ b ∂ν := by
        rw [Complex.real_smul, mul_assoc]
    _ = _ := by
        rw [hc_eq, fourierIntegral_def, fourierIntegral_def, hG₁, hG₂]
        push_cast
        try rfl

end NumberField.AdelicFourier.Ws25
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25Supply P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25Supply"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25Supply"

end
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25Supply P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier.Ws25"

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory"
open scoped Classical nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ
        (fun x ↦ g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2) w
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ)
        * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            MeasureTheory.volume (g : mixedEmbedding.mixedSpace F → ℂ) (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
        * fourierIntegral
            (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν h w.2 :=
  NumberField.AdelicFourier.Ws25.fourierIntegral_pureTensor_eq_impl F μ ν ψ g h w

end S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq (solution)
