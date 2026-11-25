-- Prove2me | solution 1 for GlobalTheory.HL.CoordTerm.lat_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:32:33.742479+00:00
-- url     : https://prove2.me/submissions/9039aa5d-6e86-4448-a026-a70b5b15d2ee

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
import Theorems.Thm_GlobalTheory_HL_CoordTerm_grp_e
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
theorem _root_.solution (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ := by
  ext y
  obtain ⟨x, rfl⟩ := c.e.surjective y
  rw [mem_lat, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨c.e z, (mem_lat c _ _).2 hz, grp_e c g z⟩
  · rintro ⟨w, hw, h⟩
    obtain ⟨z, rfl⟩ := c.e.surjective w
    have h2 : c.e (g z) = c.e x := (grp_e c g z).symm.trans h
    exact ⟨z, (mem_lat c _ _).1 hw, c.e.injective h2⟩
end GlobalTheory.HL.CoordTerm
