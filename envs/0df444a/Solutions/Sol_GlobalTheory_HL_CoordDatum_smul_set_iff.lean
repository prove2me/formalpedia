-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.smul_set_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:30.148499+00:00
-- url     : https://prove2.me/submissions/5be43d3e-d223-446e-b94f-aa64af9346fe

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
theorem _root_.solution (g : S.GLV) (A B : Set (S.V × S.V)) :
    g • A = B ↔ ∀ v' v, (v', v) ∈ A ↔ (g v', g v) ∈ B := by
  have h : ∀ v' v, (g v', g v) ∈ g • A ↔ (v', v) ∈ A := fun v' v =>
    Set.smul_mem_smul_set_iff (a := g) (x := (v', v))
  constructor
  · rintro rfl v' v; exact (h v' v).symm
  · intro h'
    ext ⟨w', w⟩
    obtain ⟨v, rfl⟩ := g.surjective w
    obtain ⟨v', rfl⟩ := g.surjective w'
    rw [h, h']
end GlobalTheory.HL.CoordDatum
