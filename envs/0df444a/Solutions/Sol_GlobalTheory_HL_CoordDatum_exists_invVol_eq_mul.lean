-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.exists_invVol_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:52.853384+00:00
-- url     : https://prove2.me/submissions/b1086279-08c3-4dd9-adc0-816c25e4ff74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerCommensurableInvVolumeSmulComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsWtEqMulNu
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
namespace GlobalTheory.HL.CoordDatum
theorem _root_.solution {G : Type} [Group G] (K' K0 : Subgroup G) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ K : Subgroup G, K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
      invVol K' K = κ * invVol K0 K := by
  by_cases hc : K'.relIndex K0 ≠ 0 ∧ K0.relIndex K' ≠ 0
  · refine ⟨invVol K' K0, ?_, fun K hK hK' => ?_⟩
    · unfold invVol
      positivity
    · exact (invVol_mul_pos_le_conj K' K0 K hc.1 hc.2
        (Subgroup.relIndex_ne_zero_trans hc.1 hK)
        (Subgroup.relIndex_ne_zero_trans hK' hc.2)).1
  · refine ⟨0, le_rfl, fun K hK hK' => ?_⟩
    rw [zero_mul]
    unfold invVol
    by_cases h1 : K.relIndex K' = 0
    · simp [h1]
    · have h2 : K'.relIndex K = 0 := by
        by_contra h2
        exact hc ⟨Subgroup.relIndex_ne_zero_trans h2 hK', Subgroup.relIndex_ne_zero_trans hK h1⟩
      simp [h2]
end GlobalTheory.HL.CoordDatum
