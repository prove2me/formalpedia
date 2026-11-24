-- Prove2me | solution 1 for GlobalTheory.scale_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:42.988448+00:00
-- url     : https://prove2.me/submissions/37ad5310-b498-4d95-86ec-063ca74fee99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DualCinvOKSmallStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EventuallyTestFunctionMulInverseUnitEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerIntegralEqVolumeMulIntegralPerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_VolumeScaledIntegersMulVolumeDualEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegral
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (f : A.K → ℂ) (t : A.K), IsUnit t → ∫ b, f (t * b) ∂μK = ((A.absK t : ℂ))⁻¹ * ∫ s, f s ∂μK := by
  intro F E _ _ _ _ _ A μK hH f t ht
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have hme : MeasurableEmbedding (fun b : A.K => ht.unit • b) := (Homeomorph.smul ht.unit).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => ht.unit • b) μK =
      ((distribHaarChar A.K ht.unit : ENNReal))⁻¹ • μK := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul μK ht.unit⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, f (t * b) ∂μK = ∫ b, f b ∂(Measure.map (fun b : A.K => ht.unit • b) μK) := by
    rw [hme.integral_map]; rfl
  rw [hint, hmap, integral_smul_measure]
  simp [Et.absK, ht, Complex.real_smul]
end GlobalTheory
