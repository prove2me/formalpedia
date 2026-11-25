-- Prove2me | solution 1 for GlobalTheory.HL.CoordTerm.mem_inn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:47.191831+00:00
-- url     : https://prove2.me/submissions/32bfc1cf-90b4-442c-a5a6-a88119eefc04

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinates
import Theorems.Thm_GlobalTheory_HL_CoordTerm_mem_lat
import Theorems.Thm_GlobalTheory_HL_CoordInnerSnd_mem_lat
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_lat


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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordTerm
theorem _root_.solution (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (y : S.V) :
    y ∈ c.inn f L ↔ ∃ x : ↥(H.perp (H.X f)), y = c.e x ∧ H.mkW f x ∈ L := by
  obtain ⟨v, rfl⟩ := c.e.surjective y
  unfold Coord.inn
  rw [mem_lat]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩
  · rintro ⟨x, h, hx⟩
    exact ⟨x, hx, (c.e.injective h).symm⟩
end GlobalTheory.HL.CoordTerm
