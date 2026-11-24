-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.perp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:29.373392+00:00
-- url     : https://prove2.me/submissions/16754c66-2f1a-4b41-b6bc-90e5336454da

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_fix_span

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
theorem _root_.solution (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) (hu : LocNG.IsUnitary H g)
    (hf : ∀ b, g (f b) = f b) (v : V) : g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f) := by
  have hX : ∀ x ∈ H.X f, g x = x := fix_span g _ (by rintro _ ⟨i, rfl⟩; exact hf _)
  have key : ∀ x ∈ H.X f, H.h (g v) x = H.h v x := fun x hx => by
    rw [← hu v x, hX x hx]
  exact ⟨fun h x hx => (key x hx).symm.trans (h x hx), fun h x hx => (key x hx).trans (h x hx)⟩
end GlobalTheory.HL.CoordDatum
