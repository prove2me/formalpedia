-- Prove2me | solution 1 for GlobalTheory.HCXi.KGroup.hpk_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:44.406452+00:00
-- url     : https://prove2.me/submissions/4862673a-bf69-4218-b511-b1d8dc09778c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold


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
theorem _root_.solution (k r : ℕ) : Hpk k r ∈ Kset k r := by
  obtain ⟨h1, h2, -⟩ := hermitian_pos_facts_hold k r
  refine ⟨?_, by rw [h1, h2]⟩
  show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
  rw [h1, h2, Matrix.one_mul]
end GlobalTheory.HCXi.KGroup
