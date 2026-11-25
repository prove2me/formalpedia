-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.mem_of_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:24.391418+00:00
-- url     : https://prove2.me/submissions/6d3a6e93-30c5-4290-9f2a-e574b82c12c6

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
theorem _root_.solution (S : Frames L r k) (g g' : Fin (r + 1) → S.V) (p : S.FrP) (hp : p ∈ S.frameCls g g') :
    (∀ j, p.1 j ∈ Submodule.span L.O (Set.range g)) ∧ ∀ j, p.2 j ∈ Submodule.span L.O (Set.range g') := by
  obtain ⟨A, A', hA, hA', -, -, -, hp, hp'⟩ := hp
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [hp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨A i j, hA i j⟩ : L.O)
      (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hp']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨A' i j, hA' i j⟩ : L.O)
      (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.HL.FrameStabLat
