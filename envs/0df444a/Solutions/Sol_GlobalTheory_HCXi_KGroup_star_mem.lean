-- Prove2me | solution 1 for GlobalTheory.HCXi.KGroup.star_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:44.851547+00:00
-- url     : https://prove2.me/submissions/2090e085-e384-4a13-845d-1630a52466b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Theorems.Thm_GlobalTheory_HCXi_KGroup_closedSubgroup

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
theorem _root_.solution {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κᴴ ∈ Kset k r := by
  have := (closedSubgroup k r).inv_mem κ h
  rwa [Matrix.inv_eq_left_inv h.2] at this
end GlobalTheory.HCXi.KGroup
