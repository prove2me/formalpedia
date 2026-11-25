-- Prove2me | solution 1 for GlobalTheory.HCXi.KGroup.comm_hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:33.60715+00:00
-- url     : https://prove2.me/submissions/5d058fac-7a7e-48c0-a120-e8c7537a4c84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties

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
theorem _root_.solution {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κ * Hpk k r = Hpk k r * κ := by
  have h1 : κᴴ * Hpk k r * κ = Hpk k r := h.1
  have h2 : κ * κᴴ = 1 := mul_eq_one_comm.mp h.2
  calc κ * Hpk k r = κ * (κᴴ * Hpk k r * κ) := by rw [h1]
    _ = (κ * κᴴ) * Hpk k r * κ := by simp only [Matrix.mul_assoc]
    _ = Hpk k r * κ := by rw [h2, Matrix.one_mul]
end GlobalTheory.HCXi.KGroup
