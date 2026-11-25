-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.uni_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:00:21.418191+00:00
-- url     : https://prove2.me/submissions/e86e42b0-3370-4795-8358-695301351a94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) {j : ℕ}
omit [StarRing K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution {A B : Matrix (Fin j) (Fin j) K} (hA : IsUni A) (hB : IsUni B) : IsUni (A * B) := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c < a
    · rw [hA.1 _ _ hc, zero_mul]
    · rw [hB.1 _ _ (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a, hA.2, hB.2, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 _ _ h, zero_mul]
      · rw [hB.1 _ _ h, mul_zero]
    · simp
end GlobalTheory.DegCnt.PosJ
