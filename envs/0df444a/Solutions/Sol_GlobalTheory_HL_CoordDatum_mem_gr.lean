-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.mem_gr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:55.934526+00:00
-- url     : https://prove2.me/submissions/cf8c0bd9-abd3-4ab1-bf5e-1f666cec6ed7

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
theorem _root_.solution (d : LocNG.Datum P) (v' v : V) :
    (c.e v', c.e v) ∈ (c.dat d).2.2 ↔
      ∃ (hv' : v' ∈ H.perp (H.X P.B.f)) (hv : v ∈ H.perp (H.X P.A.f)), Q d ⟨v', hv'⟩ ⟨v, hv⟩ := by
  constructor
  · rintro ⟨x', x, h, hq⟩
    have h1 : v' = x' := c.e.injective (congrArg Prod.fst h)
    have h2 : v = x := c.e.injective (congrArg Prod.snd h)
    subst h1 h2
    exact ⟨x'.2, x.2, hq⟩
  · rintro ⟨hv', hv, hq⟩
    exact ⟨⟨v', hv'⟩, ⟨v, hv⟩, rfl, hq⟩
end GlobalTheory.HL.CoordDatum
