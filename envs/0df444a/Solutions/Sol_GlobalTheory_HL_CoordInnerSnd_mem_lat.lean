-- Prove2me | solution 1 for GlobalTheory.HL.CoordInnerSnd.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:11.397854+00:00
-- url     : https://prove2.me/submissions/f1f4e23b-11a7-44eb-bd8c-228a8184dd73

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordInnerSnd
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable (Fr : LocNG.FrameD H r)
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordInnerSnd
theorem _root_.solution (Λ : Submodule M.L.O V) (v : V) : c.e v ∈ c.lat Λ ↔ v ∈ Λ := by
  constructor
  · rintro ⟨y, hy, h⟩
    rwa [← c.e.injective h]
  · intro h; exact ⟨v, h, rfl⟩
end GlobalTheory.HL.CoordInnerSnd
