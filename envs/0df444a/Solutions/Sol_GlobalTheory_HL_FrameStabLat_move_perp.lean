-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.move_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:57.754201+00:00
-- url     : https://prove2.me/submissions/472c3c2f-d4af-4a60-a93d-cde19fd90a65

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution (S : Frames L r k) (g : Fin (r + 1) → S.V) (h : S.GLV) (hh : h ∈ S.Nof g) (w : S.V)
    (hw : w ∈ perp L S.Hm S.ME) (hg : Submodule.span E (Set.range g) ≤ S.ME) :
    h w - w ∈ Submodule.span E (Set.range g) := by
  have h1 : S.spanTo g r ≤ Submodule.span E (Set.range g) :=
    Submodule.span_mono (Set.image_subset_range _ _)
  exact h1 (hh.2.2 w fun y hy => hw y (hg (h1 hy)))
end GlobalTheory.HL.FrameStabLat
