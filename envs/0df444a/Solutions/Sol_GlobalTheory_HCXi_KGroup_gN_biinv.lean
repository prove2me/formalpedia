-- Prove2me | solution 1 for GlobalTheory.HCXi.KGroup.gN_biinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:12.654679+00:00
-- url     : https://prove2.me/submissions/ff633a01-e282-45bc-b598-ed798ec74f67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Theorems.Thm_GlobalTheory_HCXi_KGroup_sum_normSq_eq_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.KGroup
namespace GlobalTheory.HCXi.KGroup
theorem _root_.solution {k r : ℕ} {κ κ' : Mat k r} (h : κ ∈ Kset k r) (h' : κ' ∈ Kset k r) (g : Mat k r) :
    gN (κ * g * κ') = gN g := by
  have h2 : κ' * κ'ᴴ = 1 := mul_eq_one_comm.mp h'.2
  unfold gN
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace]
  have e : (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * g * κ') := by
    calc (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * (κᴴ * κ) * g * κ') := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h.2, Matrix.mul_one]
  rw [e, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]
end GlobalTheory.HCXi.KGroup
