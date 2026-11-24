-- Prove2me | solution 1 for GlobalTheory.HL.CoordInnerSnd.coe_mem_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:49:17.811374+00:00
-- url     : https://prove2.me/submissions/f9890f47-c267-45a0-9626-d53a80a8e420

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices
import Theorems.Thm_GlobalTheory_HL_CoordInnerSnd_mem_pre

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
theorem _root_.solution (L : Submodule M.L.O (H.Wb Fr.f)) (x : ↥(H.perp (H.X Fr.f))) :
    (x : V) ∈ pre Fr L ↔ H.mkW Fr.f x ∈ L := by
  rw [mem_pre]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
end GlobalTheory.HL.CoordInnerSnd
