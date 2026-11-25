-- Prove2me | solution 1 for GlobalTheory.HL.FrameStab.isom_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:36:52.383135+00:00
-- url     : https://prove2.me/submissions/2075d38d-190d-4a00-b37b-e629359e025e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameStab
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) (G : Set (Fin n → E))
    (h : ∀ x ∈ G, ∀ y ∈ G, hf L Hm (φ x) (φ y) = hf L Hm x y) :
    ∀ x ∈ Submodule.span E G, ∀ y ∈ Submodule.span E G, hf L Hm (φ x) (φ y) = hf L Hm x y := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [hf]
    | add a b _ _ ha hb => rw [map_add, hf_add_r, hf_add_r, ha, hb]
    | smul c a _ ha => rw [map_smul, hf_smul_r, hf_smul_r, ha]
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [map_add, hf_add_l, hf_add_l, ha, hb]
  | smul c a _ ha => rw [map_smul, hf_smul_l, hf_smul_l, ha]
end GlobalTheory.HL.FrameStab
