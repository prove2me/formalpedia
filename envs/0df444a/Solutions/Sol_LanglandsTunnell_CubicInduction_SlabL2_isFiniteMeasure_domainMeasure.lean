-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.isFiniteMeasure_domainMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/00691d8f-ac44-5751-b126-b5a620c7d128

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Theorems.Thm_LanglandsTunnell_CubicInduction_ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
import Theorems.Thm_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_isFiniteMeasure_domainMeasure
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.RankinSelberg.mem_primeFibre HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul"

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_isFiniteMeasure_domainMeasure.MeasureTheory"
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_isFiniteMeasure_domainMeasure.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"
open scoped ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace MeasureTheory
p2m_export "MeasureTheory" "Measure lintegral_iUnion_le measure_preimage_smul lintegral_one Measure.restrict_apply lintegral_mono_set IsFiniteMeasure SMulInvariantMeasure setLIntegral_one Measure.restrict_apply' IsFundamentalDomain"
namespace IsFundamentalDomain
p2m_export "MeasureTheory.IsFundamentalDomain" "setLIntegral_eq_tsum'"
p2m_open "MeasureTheory.IsFundamentalDomain MeasureTheory"

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  {μ : Measure α} [SMulInvariantMeasure G α μ] {F : Set α}

theorem setLIntegral_le_of_forall_exists_smul_mem_E (hF : IsFundamentalDomain G F μ) {S : Set α}
    (hS : ∀ x : α, ∃ g : G, g • x ∈ S) {h : α → ENNReal} (hh : ∀ (g : G) (x : α), h (g • x) = h x) :
    ∫⁻ x in F, h x ∂μ ≤ ∫⁻ x in S, h x ∂μ :=
  calc
    ∫⁻ x in F, h x ∂μ ≤ ∫⁻ x in ⋃ g : G, (g • S ∩ F), h x ∂μ := by
      refine lintegral_mono_set fun x hx => ?_
      obtain ⟨g, hg⟩ := hS x
      refine Set.mem_iUnion.2 ⟨g⁻¹, ?_, hx⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      exact hg
    _ ≤ ∑' g : G, ∫⁻ x in g • S ∩ F, h x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G, ∫⁻ x in g • S ∩ F, h (g⁻¹ • x) ∂μ := by simp only [hh]
    _ = ∫⁻ x in S, h x ∂μ := (hF.setLIntegral_eq_tsum' h S).symm

end MeasureTheory.IsFundamentalDomain

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL localMaximalCompact3 componentAt3 ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top archRoot₁ archRoot₂ archPlaceComponent3 exists_mul_eq_unipotent_mul_diagonal_mul_compact"
namespace DomainFinAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem countable_range_globalPointsGL : Countable ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range := by
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℚ))
  haveI : Countable (GL (Fin 3) ℚ) := Units.val_injective.countable
  exact (Set.countable_range (globalPointsGL 3 (𝓞 ℚ) ℚ)).to_subtype

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem measurableConstSMul_range_globalPointsGL :
    MeasurableConstSMul ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  ⟨fun c => by
    show Measurable fun x : AdelicGL 3 (𝓞 ℚ) ℚ => (c : AdelicGL 3 (𝓞 ℚ) ℚ) * x
    exact (continuous_const.mul continuous_id).measurable⟩

section Restrict
variable {α : Type*} [MeasurableSpace α] {Γ : Type*} [Group Γ] [MulAction Γ α] {μ : Measure α}
variable [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ]

theorem smulInvariantMeasure_restrict {B : Set α} (hB : ∀ γ : Γ, γ • B = B) :
    SMulInvariantMeasure Γ α (μ.restrict B) where
  measure_preimage_smul γ s hs := by
    have hpre : (fun x => γ • x) ⁻¹' s ∩ B = (fun x => γ • x) ⁻¹' (s ∩ B) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      refine and_congr_right fun _ => ⟨fun hx => ?_, fun hx => ?_⟩
      · rw [← hB γ]
        exact Set.smul_mem_smul_set hx
      · rw [← hB γ] at hx
        exact Set.smul_mem_smul_set_iff.mp hx
    have hm : MeasurableSet ((fun x => γ • x) ⁻¹' s) := MeasurableConstSMul.measurable_const_smul γ hs
    rw [Measure.restrict_apply hm, Measure.restrict_apply hs, hpre, measure_preimage_smul (μ := μ) γ (s ∩ B)]

end Restrict

end LanglandsTunnell.CubicInduction.DomainFinAux

open LanglandsTunnell.CubicInduction.DomainFinAux in
theorem solution
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀) :
    IsFiniteMeasure (domainMeasure a b Φ₀) := by
  classical
  obtain ⟨hdet1, hslab⟩ := ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
  obtain ⟨cS, CS, hcS, hcover⟩ := exists_mul_eq_unipotent_mul_diagonal_mul_compact
  have hSfin := adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top cS CS hcS a b hΦ₀.pos hΦ₀.lt

  set Sieg : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ CS) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            cS ≤ archRoot₁ ℚ w t ∧ cS ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1} with hSieg_def
  have hScov : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ γ : GL (Fin 3) ℚ, globalPointsGL 3 (𝓞 ℚ) ℚ γ * g ∈ Sieg :=
    fun g => (hcover g).elim fun γ hγ => ⟨γ, hγ⟩

  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := countable_range_globalPointsGL
  haveI : MeasurableConstSMul ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) :=
    measurableConstSMul_range_globalPointsGL
  have hsmul_slab : ∀ γ : ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range, γ • ideleNormDetSlab a b = ideleNormDetSlab a b := by
    rintro ⟨_, γ, rfl⟩
    have key : ∀ (δ : GL (Fin 3) ℚ) (x : AdelicGL 3 (𝓞 ℚ) ℚ),
        x ∈ ideleNormDetSlab a b → globalPointsGL 3 (𝓞 ℚ) ℚ δ * x ∈ ideleNormDetSlab a b := by
      intro δ x hx
      show NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ δ * x)) ∈ Set.Icc a b
      rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, hdet1, one_mul]
      exact hx
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · intro hx
      have := key γ _ hx
      simpa [Subgroup.smul_def, smul_eq_mul, ← mul_assoc] using this
    · intro hx
      have := key γ⁻¹ _ hx
      simpa [Subgroup.smul_def, smul_eq_mul, ← mul_assoc] using this
  haveI : SMulInvariantMeasure ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) (slabMeasure a b) := by
    rw [slabMeasure_def]
    exact smulInvariantMeasure_restrict hsmul_slab

  have hslab' : MeasurableSet (ideleNormDetSlab a b) := hslab a b
  have hfin : ∫⁻ _ in Sieg, (1 : ℝ≥0∞) ∂(slabMeasure a b) < ⊤ := by
    rw [setLIntegral_one, slabMeasure_def, Measure.restrict_apply' hslab']
    exact hSfin

  have hle : ∫⁻ _, (1 : ℝ≥0∞) ∂(domainMeasure a b Φ₀) ≤ ∫⁻ _ in Sieg, (1 : ℝ≥0∞) ∂(slabMeasure a b) := by
    rw [domainMeasure_def]
    refine MeasureTheory.IsFundamentalDomain.setLIntegral_le_of_forall_exists_smul_mem_E hΦ₀.isFundamentalDomain
      (fun g => ?_) (fun _ _ => rfl)
    exact (hScov g).elim fun γ hγ => ⟨⟨globalPointsGL 3 (𝓞 ℚ) ℚ γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩, hγ⟩
  refine ⟨?_⟩
  rw [← lintegral_one]
  exact hle.trans_lt hfin

end S_LanglandsTunnell_CubicInduction_SlabL2_isFiniteMeasure_domainMeasure
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_isFiniteMeasure_domainMeasure (solution)
