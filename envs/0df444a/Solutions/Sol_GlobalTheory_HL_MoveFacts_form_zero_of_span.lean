-- Prove2me | solution 1 for GlobalTheory.HL.MoveFacts.form_zero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:13:28.42005+00:00
-- url     : https://prove2.me/submissions/38b2af43-25c3-462f-9959-4800399a443c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMoveProperties
import Theorems.Thm_GlobalTheory_HL_MoveFacts_conj_form
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
namespace GlobalTheory.HL.MoveFacts
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
private theorem hf_add_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → E) : hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem hf_smul_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (x y : Fin n → E) : hf L Hm (c • x) y = c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
private theorem hf_zero_left_flag_measures (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin n → E) : hf L Hm 0 y = 0 := by
  simp [hf]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
end GlobalTheory.HL.MoveFacts
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveFacts
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.MoveFacts
theorem _root_.solution {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (A : Set (Fin n → E)) (hA : ∀ a ∈ A, ∀ b ∈ A, hf L Hm a b = 0) :
    ∀ x ∈ Submodule.span E A, ∀ y ∈ Submodule.span E A, hf L Hm x y = 0 := by
  intro x hx y hy
  have h1 : ∀ a ∈ A, ∀ z ∈ Submodule.span E A, hf L Hm z a = 0 := by
    intro a ha z hz
    induction hz using Submodule.span_induction with
    | mem w hw => exact hA w hw a ha
    | zero => exact hf_zero_left_flag_measures L Hm a
    | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]
  induction hx using Submodule.span_induction with
  | mem w hw => rw [conj_form h y w, h1 w hw y hy, map_zero]
  | zero => exact hf_zero_left_flag_measures L Hm y
  | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
  | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]
end GlobalTheory.HL.MoveFacts
