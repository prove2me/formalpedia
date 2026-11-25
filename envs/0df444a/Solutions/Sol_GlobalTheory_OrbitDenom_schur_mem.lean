-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.schur_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:02:03.994647+00:00
-- url     : https://prove2.me/submissions/a8696513-82f3-4d59-8f1c-174cb9e351e8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_sum_castLE
import Theorems.Thm_GlobalTheory_OrbitDenom_sub_mul_left
import Theorems.Thm_GlobalTheory_OrbitDenom_det_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_det_three
import Theorems.Thm_GlobalTheory_OrbitDenom_col_lemma
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
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution (O : Subring E) {n l' l : ℕ} (h' : l' ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O) (j : Fin n)
    (a : Fin n) : l' ≤ (a : ℕ) → (a : ℕ) < l →
    (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * (W * B) a j ∈ O := by
  obtain ⟨G, hG, hGA⟩ := col_lemma O h' A W B hA hA1 hB hB1 hZ hW hc
  set D := (W.submatrix (Fin.castLE h') (Fin.castLE h')).det with hD
  have hDO : D ∈ O := by
    rw [hD, ← det_three h' A W B hA hA1 hB hB1]
    exact det_mem O _ fun _ _ => hZ _ _
  set C := W * B with hC
  have hZ' : ∀ a b, (A * C) a b ∈ O := by rw [hC, ← Matrix.mul_assoc]; exact hZ
  have key : ∀ a : Fin n, ∑ k : Fin n, (if l' ≤ (k : ℕ) then A a k * (D * C k j) else 0) ∈ O := by
    intro a
    have h1 : G * (A * C).submatrix (Fin.castLE h') id =
        D • (A.submatrix id (Fin.castLE h') * C.submatrix (Fin.castLE h') id) := by
      rw [sub_mul_left h' _ A C hA, ← Matrix.mul_assoc, hGA, Matrix.smul_mul]
    have h2 : D * ∑ k : Fin l', A a (Fin.castLE h' k) * C (Fin.castLE h' k) j ∈ O := by
      have h3 := congrFun (congrFun h1 a) j
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mul_apply] at h3
      simp only [Matrix.submatrix_apply, id] at h3
      rw [← h3]
      exact O.sum_mem fun k _ => O.mul_mem (hG _ _) (hZ' _ _)
    have h4 : ∑ k : Fin n, (if l' ≤ (k : ℕ) then 0 else A a k * C k j) =
        ∑ k : Fin l', A a (Fin.castLE h' k) * C (Fin.castLE h' k) j := by
      rw [sum_castLE h' _ (fun k hk => if_pos hk)]
      refine Finset.sum_congr rfl fun k _ => if_neg ?_
      have := k.2
      simp only [Fin.val_castLE]; omega
    have h5 := O.sub_mem (O.mul_mem hDO (hZ' a j)) h2
    rw [← h4, Matrix.mul_apply, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum] at h5
    convert h5 using 2 with k
    split_ifs <;> ring
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro ha' ha
    have h1 := key a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos ha', hA1, one_mul] at h1
    refine (O.add_mem_cancel_right ?_).1 h1
    refine O.sum_mem fun k hk => ?_
    have hka : k ≠ a := (Finset.mem_erase.1 hk).1
    split_ifs with hk'
    · rcases lt_or_gt_of_ne hka with h2 | h2
      · exact O.mul_mem (hAO _ _ ha hk') (ih k h2 hk' (lt_trans h2 ha))
      · rw [hA _ _ h2, zero_mul]; exact O.zero_mem
    · exact O.zero_mem
end GlobalTheory.OrbitDenom
