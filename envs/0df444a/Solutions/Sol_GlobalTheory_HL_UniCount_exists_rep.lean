-- Prove2me | solution 1 for GlobalTheory.HL.UniCount.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:42.588003+00:00
-- url     : https://prove2.me/submissions/ac7a5877-514c-48e5-94e9-a0e8518bb85e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Theorems.Thm_GlobalTheory_HL_UniCount_isUni_mul
import Theorems.Thm_GlobalTheory_HL_UniCount_mul_rowM
import Theorems.Thm_GlobalTheory_HL_UniCount_isUni_rowM
import Theorems.Thm_GlobalTheory_HL_UniCount_cos_rowM
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UniCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}
namespace GlobalTheory.HL.UniCount
theorem _root_.solution (L : LocE F E) (δ : E) (R : Set E)
    (hR : ∀ x : E, δ * x ∈ L.O → ∃ r ∈ R, r - x ∈ L.O)
    (u : Matrix (Fin N) (Fin N) E) (hu : IsUni u) (hδ : ∀ i j, δ * u i j ∈ L.O) (m : ℕ) :
    ∃ w : Matrix (Fin N) (Fin N) E, IsUni w ∧ (∀ i j, δ * w i j ∈ L.O) ∧ cos L w = cos L u ∧
      ∀ i j : Fin N, N ≤ i.val + m → i < j → w i j ∈ R := by
  induction m with
  | zero => exact ⟨u, hu, hδ, rfl, fun i j h _ => absurd i.2 (by omega)⟩
  | succ m ih =>
    obtain ⟨w, hw, hwδ, hc, hg⟩ := ih
    by_cases hm : N ≤ m
    · exact ⟨w, hw, hwδ, hc, fun i j _ h => hg i j (by omega) h⟩
    let k : Fin N := ⟨N - 1 - m, by omega⟩
    choose r hrR hr using fun j => hR (w k j) (hwδ k j)
    let c : Fin N → E := fun j => if k < j then r j - w k j else 0
    have hc0 : ∀ j, j ≤ k → c j = 0 := fun j hj => if_neg (not_lt.2 hj)
    have hc1 : ∀ j, c j ∈ L.O := fun j => by
      simp only [c]
      split_ifs
      exacts [hr j, zero_mem _]
    refine ⟨w * rowM k c, isUni_mul hw (isUni_rowM k c hc0), fun i j => ?_,
      (cos_rowM L w k c hc0 hc1).trans hc, fun i j h hij => ?_⟩
    · rw [mul_rowM, mul_add, ← mul_assoc]
      exact add_mem (hwδ i j) (mul_mem (hwδ i k) (hc1 j))
    · rw [mul_rowM]
      by_cases hik : i = k
      · subst hik
        rw [hw.2, one_mul]
        simp only [c, if_pos hij]
        simpa using hrR j
      · have h2 : i.val ≠ N - 1 - m := fun h => hik (Fin.ext h)
        have h3 : k < i := by
          show N - 1 - m < i.val
          omega
        rw [hw.1 i k h3, zero_mul, add_zero]
        exact hg i j (by omega) hij
end GlobalTheory.HL.UniCount
