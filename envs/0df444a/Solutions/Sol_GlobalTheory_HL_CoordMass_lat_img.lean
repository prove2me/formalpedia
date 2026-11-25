-- Prove2me | solution 1 for GlobalTheory.HL.CoordMass.lat_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:57:07.424261+00:00
-- url     : https://prove2.me/submissions/41197e3b-9753-4db7-956c-1516717f6e00

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMass
import Theorems.Thm_GlobalTheory_HL_CoordMass_mem_smul_lat
import Theorems.Thm_GlobalTheory_HL_CoordMass_mem_lat
import Theorems.Thm_GlobalTheory_HL_CoordUnip_grp_apply


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordMass
open GlobalTheory.HL.Eichler GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordMass
theorem _root_.solution (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ := by
  ext v
  obtain ⟨v, rfl⟩ := c.e.surjective v
  rw [mem_lat, mem_smul_lat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨c.e y, (mem_lat c _ _).2 hy, grp_apply c g y⟩
  · rintro ⟨y, hy, h⟩
    obtain ⟨y, rfl⟩ := c.e.surjective y
    rw [grp_apply] at h
    exact ⟨y, (mem_lat c _ _).1 hy, c.e.injective h⟩
end GlobalTheory.HL.CoordMass
