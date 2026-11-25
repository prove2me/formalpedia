-- Prove2me | solution 1 for GlobalTheory.HCXi.KGroup.compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:52:56.436008+00:00
-- url     : https://prove2.me/submissions/b931cce6-cd6b-4674-8b0d-760ec04cacc4

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
theorem _root_.solution (k r : ℕ) : IsCompact (Kset k r) := by
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (s := (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1)) hB
      (closedSubgroup k r).closed ?_
  intro g hg i _ j _
  have hu : Matrix.of g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr hg.2
  simpa using entry_norm_bound_of_unitary hu i j
end GlobalTheory.HCXi.KGroup
