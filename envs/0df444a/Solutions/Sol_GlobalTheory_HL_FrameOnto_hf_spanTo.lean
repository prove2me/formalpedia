-- Prove2me | solution 1 for GlobalTheory.HL.FrameOnto.hf_spanTo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:36.176429+00:00
-- url     : https://prove2.me/submissions/4b9193f7-1d7d-46e8-9189-c224d47b8542

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameOnto
theorem _root_.solution (g : Fin (r + 1) → S.V) {a : ℕ} {v w : S.V} (hv : v ∈ S.spanTo g a)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) w = 0) : hf L S.Hm v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_l, hx, hy, add_zero]
  | smul c x _ hx => rw [hf_smul_l, hx, mul_zero]
end GlobalTheory.HL.FrameOnto
