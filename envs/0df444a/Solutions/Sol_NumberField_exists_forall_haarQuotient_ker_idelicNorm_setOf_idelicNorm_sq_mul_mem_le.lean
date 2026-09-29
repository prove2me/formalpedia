-- Prove2me | solution 1 for NumberField.exists_forall_haarQuotient_ker_idelicNorm_setOf_idelicNorm_sq_mul_mem_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b69737e3-b379-59e9-8fa5-7c989d308737

import Theorems.Thm_NumberField_exists_pos_forall_lintegral_comp_idelicNorm_haarQuotient_ker_eq_mul_setLIntegral_range
import Theorems.Thm_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_forall_haarQuotient_ker_idelicNorm_setOf_idelicNorm_sq_mul_mem_le
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped ENNReal in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (C₀ : Set (AdeleRing (𝓞 K) K)ˣ) (hC₀ : IsCompact C₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : (AdeleRing (𝓞 K) K)ˣ,
        HaarQuotient.measure νZL N1 μN
            {wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ |
              (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ) ^ 2 * b
                ∈ C₀} ≤
          ENNReal.ofReal C := by
  classical

  letI mK : MeasurableSpace (AdeleRing (𝓞 K) K)ˣ := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K)ˣ := ⟨rfl⟩
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.locallyCompactSpace_adeleRing (𝓞 K) K
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  set νZK : Measure (AdeleRing (𝓞 K) K)ˣ := Measure.haar with hνZK

  obtain ⟨C₁, hC₁, hlin, -⟩ :=
    NumberField.exists_pos_forall_lintegral_comp_idelicNorm_haarQuotient_ker_eq_mul_setLIntegral_range K L νZL νZK N1 hN1c hN1 μN

  set K₀ : Set (AdeleRing (𝓞 K) K)ˣ := (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => p.1 * p.2⁻¹) '' (C₀ ×ˢ C₀) with hK₀
  have hK₀c : IsCompact K₀ := (hC₀.prod hC₀).image (continuous_fst.mul continuous_snd.inv)
  have hSQ : IsCompact {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ K₀} :=
    NumberField.AdeleRing.isCompact_setOf_sq_mem_of_isCompact K K₀ hK₀c
  set M : ℝ≥0∞ := νZK {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ K₀} with hM
  have hMt : M < ⊤ := hSQ.measure_lt_top
  refine ⟨C₁ * M.toReal, mul_nonneg hC₁.le ENNReal.toReal_nonneg, fun b => ?_⟩

  set Nm := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNm
  have hNc : Continuous Nm := Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange K L)
  have hNout : ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      Nm ((Quotient.mk'' w : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ).out) = Nm w := by
    intro w
    have hrel : ((Quotient.mk'' w : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ).out) ∈ MulAction.orbit N1 w :=
      @Quotient.exact _ (MulAction.orbitRel N1 (AdeleRing (𝓞 L) L)ˣ) _ _ (Quotient.out_eq _)
    rw [MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    rw [← hn, show (n • w : (AdeleRing (𝓞 L) L)ˣ) = (n : (AdeleRing (𝓞 L) L)ˣ) * w from rfl, map_mul,
      (hN1 _).mp n.2, one_mul]
  have hNm : Measurable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ => Nm wq.out) := by
    rw [measurable_from_quotient]
    have : (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ => Nm wq.out) ∘ Quotient.mk'' = Nm :=
      funext fun w => hNout w
    rw [this]
    exact hNc.measurable

  set T : Set (AdeleRing (𝓞 K) K)ˣ := {u | u ^ 2 * b ∈ C₀} with hT
  have hTm : MeasurableSet T :=
    (hC₀.isClosed.preimage ((continuous_pow 2).mul continuous_const)).measurableSet
  have hS : {wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ | Nm (wq.out : (AdeleRing (𝓞 L) L)ˣ) ^ 2 * b ∈ C₀} =
      (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ => Nm wq.out) ⁻¹' T := rfl
  have hSm : MeasurableSet {wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ | Nm (wq.out : (AdeleRing (𝓞 L) L)ˣ) ^ 2 * b ∈ C₀} := by
    rw [hS]; exact hNm hTm

  have hTle : νZK T ≤ M := by
    by_cases hT0 : T = ∅
    · rw [hT0, measure_empty]; exact bot_le
    obtain ⟨u₀, hu₀⟩ := Set.nonempty_iff_ne_empty.mpr hT0
    have hsub : T ⊆ (fun u => u₀⁻¹ * u) ⁻¹' {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ K₀} := by
      intro u hu
      show (u₀⁻¹ * u) ^ 2 ∈ K₀
      refine ⟨(u ^ 2 * b, u₀ ^ 2 * b), ⟨hu, hu₀⟩, ?_⟩
      show u ^ 2 * b * (u₀ ^ 2 * b)⁻¹ = (u₀⁻¹ * u) ^ 2
      rw [mul_inv, mul_pow, inv_pow, mul_mul_mul_comm, mul_inv_cancel, mul_one, mul_comm]
    calc νZK T ≤ νZK ((fun u => u₀⁻¹ * u) ⁻¹' {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ K₀}) := measure_mono hsub
      _ = M := by rw [hM, MeasureTheory.measure_preimage_mul]

  have hind : (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ => T.indicator (1 : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) (Nm wq.out)) =
      {wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ | Nm (wq.out : (AdeleRing (𝓞 L) L)ˣ) ^ 2 * b ∈ C₀}.indicator 1 := by
    funext wq
    simp only [hS, Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  have key := hlin (T.indicator (1 : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞)) (measurable_one.indicator hTm)
  rw [hind, lintegral_indicator_one hSm] at key
  calc HaarQuotient.measure νZL N1 μN {wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ |
          Nm (wq.out : (AdeleRing (𝓞 L) L)ˣ) ^ 2 * b ∈ C₀}
      = ENNReal.ofReal C₁ * ∫⁻ u in Set.range Nm, T.indicator (1 : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) u ∂νZK := key
    _ ≤ ENNReal.ofReal C₁ * ∫⁻ u, T.indicator (1 : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞) u ∂νZK :=
        mul_le_mul_right (setLIntegral_le_lintegral _ _) _
    _ = ENNReal.ofReal C₁ * νZK T := by rw [lintegral_indicator_one hTm]
    _ ≤ ENNReal.ofReal C₁ * M := mul_le_mul_right hTle _
    _ = ENNReal.ofReal (C₁ * M.toReal) := by
        rw [ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_toReal hMt.ne]

end S_NumberField_exists_forall_haarQuotient_ker_idelicNorm_setOf_idelicNorm_sq_mul_mem_le
end P2MW
export P2MW.S_NumberField_exists_forall_haarQuotient_ker_idelicNorm_setOf_idelicNorm_sq_mul_mem_le (solution)
