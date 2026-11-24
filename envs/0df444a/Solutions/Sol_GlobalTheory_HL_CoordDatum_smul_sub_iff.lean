-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.smul_sub_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:30.860842+00:00
-- url     : https://prove2.me/submissions/8494974f-f6e0-45f4-9fe1-dd5e154c684e

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
theorem _root_.solution (g : S.GLV) (A B : Submodule M.L.O S.V) :
    g • A = B ↔ ∀ v, v ∈ A ↔ g v ∈ B := by
  have h : ∀ v, g v ∈ g • A ↔ v ∈ A := fun v => by
    constructor
    · rintro ⟨w, hw, hwv⟩
      have : w = v := g.injective hwv
      rwa [← this]
    · exact fun hv => ⟨v, hv, rfl⟩
  constructor
  · rintro rfl v; exact (h v).symm
  · intro h'
    ext w
    obtain ⟨v, rfl⟩ := g.surjective w
    rw [h, h']
end GlobalTheory.HL.CoordDatum
