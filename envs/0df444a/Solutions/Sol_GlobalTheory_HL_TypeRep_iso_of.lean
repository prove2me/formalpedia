-- Prove2me | solution 1 for GlobalTheory.HL.TypeRep.iso_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:44.976268+00:00
-- url     : https://prove2.me/submissions/95f83164-4eb4-4ba4-a1ee-0694fc3a5c3d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentatives
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_add_left
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_add_right
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_smul_left
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_smul_right
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_LevelRep_Good_add
import Theorems.Thm_GlobalTheory_HL_LevelRep_Good_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
private theorem h_zero_left' (y : S.V) : S.h 0 y = 0 := by
  simp [Frames.h, hf]
private theorem h_zero_right_flag_measures (a : S.V) : S.h a 0 = 0 := by
  simp [Frames.h, hf]
private theorem h_eq_zero_of_span_orth {s t : Set S.V} (hst : ∀ a ∈ s, ∀ b ∈ t, S.h a b = 0) {x y : S.V}
    (hx : x ∈ Submodule.span E s) (hy : y ∈ Submodule.span E t) : S.h x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb => exact hst a ha b hb
    | zero => exact h_zero_right_flag_measures S a
    | add u v _ _ hu hv => rw [h_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [h_smul_right, hu, mul_zero]
  | zero => exact h_zero_left' S y
  | add u v _ _ hu hv => rw [h_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [h_smul_left, hu, mul_zero]
end GlobalTheory.HL.TypeRep
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.TypeRep
theorem _root_.solution (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    {x y : S.V} (hx : x ∈ S.spanTo g r) (hy : y ∈ S.spanTo g r) : S.h x y = 0 := by
  unfold Frames.spanTo at hx hy
  refine h_eq_zero_of_span_orth S ?_ hx hy
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  change hf L S.Hm (g i) (g j) = 0
  rw [hg, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi
end GlobalTheory.HL.TypeRep
