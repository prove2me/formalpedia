-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.stab_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:55.543139+00:00
-- url     : https://prove2.me/submissions/af02d3ac-2f1c-48d5-8f24-f81f25001986

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_isUnitary_and_fixes_frames_of_mem_complementUnitary
import Theorems.Thm_GlobalTheory_HL_CoordDatum_moves_iff

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
theorem _root_.solution (d : LocNG.Datum P) : LocNG.Datum.Stab d =
    (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom := by
  unfold LocNG.Datum.Stab
  rw [← Subgroup.closure_eq ((S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom)]
  congr 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isUnitary_and_fixes_frames_of_mem_complementUnitary c g).1 h1, (moves_iff c g h1 d d).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isUnitary_and_fixes_frames_of_mem_complementUnitary c g).2 h1, (moves_iff c g ((isUnitary_and_fixes_frames_of_mem_complementUnitary c g).2 h1) d d).2 h2⟩
end GlobalTheory.HL.CoordDatum
