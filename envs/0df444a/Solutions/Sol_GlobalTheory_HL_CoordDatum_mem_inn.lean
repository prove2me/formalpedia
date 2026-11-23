-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.mem_inn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:34.206823+00:00
-- url     : https://prove2.me/submissions/abf0146a-c743-4915-a8e5-373ec3dd5f48

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordDatum
theorem _root_.solution (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (v : V) :
    c.e v ∈ c.inn f L ↔ ∃ hv : v ∈ H.perp (H.X f), H.mkW f ⟨v, hv⟩ ∈ L := by
  unfold Coord.inn Coord.lat
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    have h' : (x : V) = v := c.e.injective h
    subst h'
    exact ⟨x.2, hx⟩
  · rintro ⟨hv, h⟩
    exact ⟨v, ⟨⟨v, hv⟩, h, rfl⟩, rfl⟩
end GlobalTheory.HL.CoordDatum
