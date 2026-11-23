-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.isUnitary_and_fixes_frames_of_mem_complementUnitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:15.973144+00:00
-- url     : https://prove2.me/submissions/8ccf396a-1838-46e2-aefd-423c43325086

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_set_iff

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
theorem _root_.solution (g : V ≃ₗ[E] V) : g ∈ P.UW0 ↔ c.grp g ∈ S.H0 := by
  have h : {g | LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b} =
      (S.H0.comap c.grp.toMonoidHom : Subgroup (V ≃ₗ[E] V)) := by
    ext g
    exact set_iff c g
  unfold LocNG.FPair.UW0
  rw [h, Subgroup.closure_eq]
  rfl
end GlobalTheory.HL.CoordDatum
