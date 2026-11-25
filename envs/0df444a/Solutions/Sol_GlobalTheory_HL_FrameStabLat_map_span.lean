-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.map_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:08.557809+00:00
-- url     : https://prove2.me/submissions/8d279613-65f8-465d-a7eb-b1c06b781f3d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution {ι : Type} (g : ι → V) (h : V ≃ₗ[E] V) (Λ : Submodule O V) (H : ∀ i, h (g i) ∈ Λ)
    {x : V} (hx : x ∈ Submodule.span O (Set.range g)) : h x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact H i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
  | smul c x _ hx =>
    have : h (c • x) = c • h x := h.map_smul (c : E) x
    rw [this]; exact Λ.smul_mem c hx
end GlobalTheory.HL.FrameStabLat
