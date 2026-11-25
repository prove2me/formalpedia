-- Prove2me | solution 1 for GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:31.861894+00:00
-- url     : https://prove2.me/submissions/b23455c2-6ec8-465e-9c63-49e769a1609f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerDataStatement
import Theorems.Thm_GlobalTheory_HL_CoordDatum_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective c.dat ∧ (∀ g ∈ P.UW0, ∀ d d', LocNG.Datum.Moves g d d' ↔ c.grp g • c.dat d = c.dat d') ∧ (∀ d d', LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ (∀ d g, g ∈ LocNG.Datum.Stab d ↔ c.grp g ∈ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) ∧ ∀ d0 d, LocNG.Datum.wt d0 d = invVol (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
  first | exact @GlobalTheory.HL.CoordDatum.transport | exact GlobalTheory.HL.CoordDatum.transport | (intros; apply GlobalTheory.HL.CoordDatum.transport <;> assumption)
end _root_.GlobalTheory.T
