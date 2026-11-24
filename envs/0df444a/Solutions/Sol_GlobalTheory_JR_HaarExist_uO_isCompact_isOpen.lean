-- Prove2me | solution 1 for GlobalTheory.JR.HaarExist.uO_isCompact_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:59:57.252802+00:00
-- url     : https://prove2.me/submissions/b48dc4e7-5c98-401e-9a41-83e1de85a7c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize
import Theorems.Thm_GlobalTheory_JR_HaarExist_entryBall_compact_open
import Theorems.Thm_GlobalTheory_JR_HaarExist_norm_one_entry_le

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HaarExist
variable (r : ℕ)
namespace GlobalTheory.JR.HaarExist
theorem _root_.solution (E : Type) [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [ContinuousStar E] :
    IsCompact (uO r E) ∧ IsOpen (uO r E) ∧ (uO r E).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r E
  have hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  exact ⟨hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc, ho.preimage continuous_subtype_val,
    1, fun i j => norm_one_entry_le r E i j⟩
end GlobalTheory.JR.HaarExist
