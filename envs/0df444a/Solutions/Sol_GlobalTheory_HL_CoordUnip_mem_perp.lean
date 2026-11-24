-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:31.894976+00:00
-- url     : https://prove2.me/submissions/d31c7aed-bfa2-4a84-b3cd-b05d61de2382

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_X
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V)
namespace GlobalTheory.HL.CoordUnip
theorem _root_.solution (he : ∀ x y, S.h (e x) (e y) = H.h x y) (hf : ∀ a, f a = e (Fr.f a)) (x : V) :
    x ∈ H.perp (H.X Fr.f) ↔ e x ∈ perp M.L S.Hm (S.spanTo f r) := by
  have hX := mem_X S e Fr f hf
  change (∀ y ∈ H.X Fr.f, H.h x y = 0) ↔ ∀ y ∈ S.spanTo f r, S.h (e x) y = 0
  constructor
  · intro h y hy
    have := h (e.symm y) ((hX _).2 (by simpa using hy))
    rw [← he, e.apply_symm_apply] at this
    exact this
  · intro h y hy
    rw [← he]
    exact h (e y) ((hX y).1 hy)
end GlobalTheory.HL.CoordUnip
