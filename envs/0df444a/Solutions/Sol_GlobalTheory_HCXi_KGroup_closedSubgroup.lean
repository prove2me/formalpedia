-- Prove2me | solution 1 for GlobalTheory.HCXi.KGroup.closedSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:06:27.972857+00:00
-- url     : https://prove2.me/submissions/03513eba-ddb0-4822-9640-c0d0679c1729

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Theorems.Thm_Formalism_FourierDecayAlt_P_unitary_group_closed


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
theorem _root_.solution (k r : ℕ) : IsClosedSubgroup (Kset k r) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  refine ⟨⟨hG.one_mem, by simp⟩, ?_, ?_, fun a ha => hG.unit a ha.1, ?_⟩
  · intro a ha b hb
    refine ⟨hG.mul_mem a ha.1 b hb.1, ?_⟩
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha.2, Matrix.one_mul, hb.2]
  · intro a ha
    refine ⟨hG.inv_mem a ha.1, ?_⟩
    rw [Matrix.inv_eq_left_inv ha.2, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp ha.2
  · have hc : Continuous fun g : Mat k r => gᴴ * g :=
      (continuous_id.matrix_conjTranspose).matrix_mul continuous_id
    exact hG.closed.inter (isClosed_singleton.preimage hc)
end GlobalTheory.HCXi.KGroup
