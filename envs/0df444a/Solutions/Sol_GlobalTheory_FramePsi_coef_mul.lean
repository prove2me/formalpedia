-- Prove2me | solution 1 for GlobalTheory.FramePsi.coef_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:30:35.246395+00:00
-- url     : https://prove2.me/submissions/f1fb17d7-e788-4e5d-b146-85eaa0aac48e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Theorems.Thm_GlobalTheory_FramePsi_hf_span_right
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
open GlobalTheory GlobalTheory.FramePsi
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FramePsi
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (a : S.GLV) (ha : a ∈ S.Nof g) (b : S.GLV) (hb : b ∈ S.Nof g) (j : Fin r) :
    S.coef g gs (a * b) j = S.coef g gs a j + S.coef g gs b j := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at ha hb
  obtain ⟨⟨-, ha1⟩, -⟩ := ha
  obtain ⟨⟨-, hb1⟩, hb2⟩ := hb
  have hA : b (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
    by_cases hj : (j : ℕ) + 1 < r
    · refine (hb1 ⟨j + 1, hj⟩).2 _ (Submodule.subset_span ⟨j.succ, ?_, rfl⟩)
      simp
    · have hr : (j : ℕ) + 1 = r := by have := j.2; omega
      rw [hr]
      refine hb2.2 _ ?_
      refine hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [hg, if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
  have hB := (ha1 j).2 _ hA
  have hK : S.spanTo g j ≤ LinearMap.ker (pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h0 : pairL L S.Hm (gs j) (g j.succ) = 0 := by
    change hf L S.Hm (g j.succ) (gs j) = 0
    rw [hd, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1 := LinearMap.mem_ker.1 (hK hB)
  change pairL L S.Hm (gs j) (a (b (g j.succ))) =
    pairL L S.Hm (gs j) (a (g j.succ)) + pairL L S.Hm (gs j) (b (g j.succ))
  simp only [map_sub] at h1
  linear_combination h1 - h0
end GlobalTheory.FramePsi
