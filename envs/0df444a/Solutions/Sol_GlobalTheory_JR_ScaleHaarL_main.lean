-- Prove2me | solution 1 for GlobalTheory.JR.ScaleHaarL.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:25.150496+00:00
-- url     : https://prove2.me/submissions/51f4f0c1-3d3e-4ac1-be87-79ea54301ba9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HaarMeasureLUnitSmulAbsKSq
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_pi_two
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ScaleHaarL
namespace GlobalTheory.JR.ScaleHaarL
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  intro F E _ _ _ _ U A μ hμ c S
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := GlobalTheory.JR.EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  let u : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) c
  have hu : (u : A.L) = algebraMap A.K A.L (c : A.K) := rfl
  have hset : {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = u • S := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, Units.smul_def, hu, smul_eq_mul]
    exact ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩
  have hc1 : Continuous (b.equivFun.symm : (Fin 2 → A.K) → A.L) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)
  have hc2 : Continuous (b.equivFun : A.L → (Fin 2 → A.K)) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)
  let e : (Fin 2 → A.K) ≃ₜ+ A.L :=
    { b.equivFun.symm.toAddEquiv with
      continuous_toFun := hc1
      continuous_invFun := hc2 }
  have key : distribHaarChar A.L u = distribHaarChar A.K c ^ 2 := by
    rw [GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e c u (fun x => ?_),
      GlobalTheory.JR.ModuleNorm.distribHaarChar_pi_two]
    change b.equivFun.symm ((c : A.K) • x) = (u : A.L) * b.equivFun.symm x
    rw [map_smul, Algebra.smul_def, hu]
  rw [hset, ← distribHaarChar_mul μ u S, key, GlobalTheory.JR.EtMeas.absK_unit]
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]
end GlobalTheory.JR.ScaleHaarL
