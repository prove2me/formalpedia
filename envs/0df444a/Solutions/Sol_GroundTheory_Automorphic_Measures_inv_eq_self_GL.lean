-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.inv_eq_self_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:07.047792+00:00
-- url     : https://prove2.me/submissions/e24bc556-8390-4a38-a04e-b6c735b79e72

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.inv = μ := by
  have := isMulRightInvariant_GL F n μ
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ∞ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have e := isMulLeftInvariant_eq_smul μ.inv μ
  have hc : haarScalarFactor μ.inv μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e
    simp only [Measure.inv_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have hKinv : (K : Set (GL (Fin n) F))⁻¹ = K := by
      ext x
      simp
    rw [hKinv] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]
end GroundTheory.Automorphic.Measures
