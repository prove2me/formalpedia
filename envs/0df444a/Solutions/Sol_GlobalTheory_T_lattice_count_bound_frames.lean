-- Prove2me | solution 1 for GlobalTheory.T.lattice_count_bound_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:47.198685+00:00
-- url     : https://prove2.me/submissions/076cf2ec-c57c-422b-bee7-18380b8c4612

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFramesStatement
import Theorems.Thm_GlobalTheory_FrameOver_encard_overlattices_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, 0 ≤ S.a → ({Mh : Submodule L.O S.V | S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ ∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O}.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  first | exact @GlobalTheory.FrameOver.encard_overlattices_le | exact GlobalTheory.FrameOver.encard_overlattices_le | (intros; apply GlobalTheory.FrameOver.encard_overlattices_le <;> assumption)
end _root_.GlobalTheory.T
