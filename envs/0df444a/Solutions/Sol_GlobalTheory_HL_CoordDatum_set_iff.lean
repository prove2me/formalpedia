-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.set_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:17.397666+00:00
-- url     : https://prove2.me/submissions/bca33f7d-90e0-4f75-9df1-76767ba1bed3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_grp_apply
import Theorems.Thm_GlobalTheory_HL_CoordDatum_mem_riemannRochSpace_iff_regularAt_everywhere

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
theorem _root_.solution (g : V ≃ₗ[E] V) :
    (LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b) ↔ c.grp g ∈ S.H0 := by
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  refine and_congr ⟨fun h x y => ?_, fun h x y => ?_⟩ (forall_congr' fun b => ?_)
  · obtain ⟨x, rfl⟩ := c.e.surjective x
    obtain ⟨y, rfl⟩ := c.e.surjective y
    rw [grp_apply, grp_apply, c.h_eq, c.h_eq, h]
  · rw [← c.h_eq, ← c.h_eq, ← grp_apply, ← grp_apply, h]
  · rw [c.f_eq, c.f'_eq, grp_apply, grp_apply, c.e.injective.eq_iff, c.e.injective.eq_iff]
end GlobalTheory.HL.CoordDatum
