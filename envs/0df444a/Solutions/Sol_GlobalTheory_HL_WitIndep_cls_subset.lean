-- Prove2me | solution 1 for GlobalTheory.HL.WitIndep.cls_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:02.235046+00:00
-- url     : https://prove2.me/submissions/afe4428e-0654-471b-8483-277e56a05250

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Theorems.Thm_GlobalTheory_HL_WitIndep_sum_sum
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.WitIndep
theorem _root_.solution {g g' h h' : Fin (r + 1) → S.V} (H : (h, h') ∈ S.frameCls g g') :
    S.frameCls h h' ⊆ S.frameCls g g' := by
  obtain ⟨A, A', hA, hA', h0, h1, hc, e, e'⟩ := H
  rintro p ⟨B, B', hB, hB', k0, k1, kc, d, d'⟩
  have tri : ∀ i j l : Fin (r + 1), (j < i ∨ (i = j ∧ l ≠ i)) →
      A i l * B l j = 0 ∧ A' i l * B' l j = 0 := by
    intro i j l hh
    by_cases hl : l < i
    · simp [h0 i l hl]
    · have : j < l := by
        rcases hh with hh | ⟨rfl, hh⟩
        · exact lt_of_lt_of_le hh (not_lt.1 hl)
        · exact lt_of_le_of_ne (not_lt.1 hl) hh.symm
      simp [k0 l j this]
  refine ⟨A * B, A' * B', fun i j => ?_, fun i j => ?_, fun i j hij => ?_, fun i => ?_,
    fun i j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [Matrix.mul_apply]
    exact L.O.sum_mem fun l _ => L.O.mul_mem (hA i l) (hB l j)
  · rw [Matrix.mul_apply]
    exact L.O.sum_mem fun l _ => L.O.mul_mem (hA' i l) (hB' l j)
  · rw [Matrix.mul_apply, Matrix.mul_apply]
    exact ⟨Finset.sum_eq_zero fun l _ => (tri i j l (.inl hij)).1,
      Finset.sum_eq_zero fun l _ => (tri i j l (.inl hij)).2⟩
  · constructor
    · rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => (tri i i l (.inr ⟨rfl, hl⟩)).1)
        (by simp), (h1 i).1, (k1 i).1, one_mul]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => (tri i i l (.inr ⟨rfl, hl⟩)).2)
        (by simp), (h1 i).2, (k1 i).2, one_mul]
  · choose c hcO hc using hc
    choose c' hcO' kc using kc
    refine ⟨∑ l, (c i l * B' l j + A i l * c' l j), L.O.sum_mem fun l _ =>
      L.O.add_mem (L.O.mul_mem (hcO i l) (hB' l j)) (L.O.mul_mem (hA i l) (hcO' l j)), ?_⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    linear_combination B' l j * hc i l + A i l * kc l j
  · simp only at e
    rw [d]
    simp only [e, sum_sum, Matrix.mul_apply]
  · simp only at e'
    rw [d']
    simp only [e', sum_sum, Matrix.mul_apply]
end GlobalTheory.HL.WitIndep
