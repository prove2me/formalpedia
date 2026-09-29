-- Prove2me | solution 1 for NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a76bfce1-81eb-541e-ae11-27a38c2932af

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Matrix Set
open scoped ENNReal NNReal

namespace KcAdicLinCVModule

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K

theorem main
    (V : Type) [AddCommGroup V] [Module (v.adicCompletion K) V]
    [FiniteDimensional (v.adicCompletion K) V]
    [TopologicalSpace V] [IsModuleTopology (v.adicCompletion K) V]
    [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [ν.IsAddHaarMeasure]
    (T : V →ₗ[v.adicCompletion K] V) (hT : LinearMap.det T ≠ 0) :
    Measure.map T ν = ENNReal.ofReal ‖LinearMap.det T‖⁻¹ • ν := by
  classical
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup (v.adicCompletion K) V
  haveI : ContinuousSMul (v.adicCompletion K) V :=
    IsModuleTopology.toContinuousSMul (v.adicCompletion K) V

  set n : ℕ := Module.finrank (v.adicCompletion K) V with hn
  let b : Module.Basis (Fin n) (v.adicCompletion K) V := Module.finBasis (v.adicCompletion K) V
  let e : V ≃ₗ[v.adicCompletion K] (Fin n → v.adicCompletion K) := b.equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let ec : V ≃L[v.adicCompletion K] (Fin n → v.adicCompletion K) :=
    { e with continuous_toFun := he, continuous_invFun := hes }
  have hec : ∀ x, ec x = e x := fun _ => rfl

  letI : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩

  haveI hν' : (Measure.map ec ν).IsAddHaarMeasure := ec.isAddHaarMeasure_map ν
  set μ0 : Measure (v.adicCompletion K) := Measure.addHaar with hμ0
  set P : Measure (Fin n → v.adicCompletion K) := Measure.pi fun _ : Fin n => μ0 with hP
  have huniq : Measure.map ec ν = (Measure.map ec ν).addHaarScalarFactor P • P :=
    Measure.isAddLeftInvariant_eq_smul (Measure.map ec ν) P
  set c : ℝ≥0 := (Measure.map ec ν).addHaarScalarFactor P with hc

  set M : Matrix (Fin n) (Fin n) (v.adicCompletion K) := LinearMap.toMatrix b b T with hM
  have hMdet : M.det = LinearMap.det T := LinearMap.det_toMatrix b T
  have hMne : M.det ≠ 0 := by rw [hMdet]; exact hT
  have hcv := NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi K v μ0 M hMne

  have hconj : ∀ x, ec (T x) = M.mulVec (ec x) := by
    intro x
    rw [hec, hec]
    have h1 : (e x : Fin n → v.adicCompletion K) = b.repr x := Module.Basis.equivFun_apply b x
    have h2 : (e (T x) : Fin n → v.adicCompletion K) = b.repr (T x) :=
      Module.Basis.equivFun_apply b (T x)
    rw [h1, h2, hM, LinearMap.toMatrix_mulVec_repr]
  have hmv : Measurable fun y : Fin n → v.adicCompletion K => M.mulVec y :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hTe : (T : V → V) = ec.symm ∘ (fun y => M.mulVec y) ∘ ec := by
    funext x
    simp only [Function.comp_apply]
    rw [← hconj, ContinuousLinearEquiv.symm_apply_apply]
  have hTm : Measurable (T : V → V) := (IsModuleTopology.continuous_of_linearMap T).measurable
  calc Measure.map T ν
      = Measure.map ec.symm (Measure.map (fun y => M.mulVec y) (Measure.map ec ν)) := by
        rw [Measure.map_map hmv ec.continuous.measurable,
          Measure.map_map ec.symm.continuous.measurable (hmv.comp ec.continuous.measurable), ← hTe]
    _ = Measure.map ec.symm (Measure.map (fun y => M.mulVec y) ((c : ℝ≥0∞) • P)) := by
        rw [huniq, ENNReal.smul_def]
    _ = Measure.map ec.symm ((c : ℝ≥0∞) • (ENNReal.ofReal ‖M.det‖⁻¹ • P)) := by
        rw [Measure.map_smul, hcv]
    _ = ENNReal.ofReal ‖M.det‖⁻¹ • Measure.map ec.symm ((c : ℝ≥0∞) • P) := by
        rw [smul_comm, Measure.map_smul]
    _ = ENNReal.ofReal ‖M.det‖⁻¹ • Measure.map ec.symm (Measure.map ec ν) := by
        rw [← ENNReal.smul_def, ← huniq]
    _ = ENNReal.ofReal ‖LinearMap.det T‖⁻¹ • ν := by
        rw [Measure.map_map ec.symm.continuous.measurable ec.continuous.measurable,
          ContinuousLinearEquiv.symm_comp_self, Measure.map_id, hMdet]

end KcAdicLinCVModule

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module (v.adicCompletion K) V]
    [FiniteDimensional (v.adicCompletion K) V]
    [TopologicalSpace V] [IsModuleTopology (v.adicCompletion K) V]
    [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [ν.IsAddHaarMeasure]
    (T : V →ₗ[v.adicCompletion K] V) (hT : LinearMap.det T ≠ 0) :
    Measure.map T ν = ENNReal.ofReal ‖LinearMap.det T‖⁻¹ • ν :=
  KcAdicLinCVModule.main V ν T hT

end S_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
end P2MW
export P2MW.S_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure (solution)
