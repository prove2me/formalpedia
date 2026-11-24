-- Prove2me | solution 1 for GlobalTheory.HL.CoordInnerSnd.mem_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:25.526729+00:00
-- url     : https://prove2.me/submissions/bb1b4731-9c25-4073-b521-770fd7737626

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
namespace GlobalTheory.HL.CoordInnerSnd
theorem _root_.solution (L : Submodule M.L.O (H.Wb Fr.f)) (v : V) :
    v ∈ pre Fr L ↔ ∃ hv : v ∈ H.perp (H.X Fr.f), H.mkW Fr.f ⟨v, hv⟩ ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, h, rfl⟩
end GlobalTheory.HL.CoordInnerSnd
