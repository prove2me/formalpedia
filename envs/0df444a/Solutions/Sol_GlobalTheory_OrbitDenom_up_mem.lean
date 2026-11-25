-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.up_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:14:31.614363+00:00
-- url     : https://prove2.me/submissions/84206623-318d-4e24-8dd9-c115a2ea3284

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_schur_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_scal_dvd
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
theorem _root_.solution (O : Subring E) {n l' l : ℕ} (h : l ≤ n) (h' : l' ≤ n)
    (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O)
    (t : E) (ε : Fin n → E) (hε : ∀ b, ε b ∈ O) (hε2 : ∀ b, ε b * ε b = 1)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (hrow : ∀ a b : Fin n, l' ≤ (a : ℕ) → (a : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (i : Fin n) (hi' : l' ≤ (i : ℕ)) (hi : (i : ℕ) < l) (j : Fin n) :
    (W.submatrix (Fin.castLE h) (Fin.castLE h)).det *
      (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * B i j ∈ O := by
  obtain ⟨y, hy, hD⟩ := scal_dvd O h (by omega) A W B hA hA1 hB hB1 hZ hAO t ε hε hcol
  let a : Fin n := ⟨l + l' - 1 - i, by omega⟩
  have ha' : l' ≤ (a : ℕ) := by simp only [a]; omega
  have ha : (a : ℕ) < l := by simp only [a]; omega
  have h1 := schur_mem O h' A W B hA hA1 hB hB1 hZ hW hc hAO j a ha' ha
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hrow _ _ ha' ha,
    if_pos (by simp only [a]; omega)] at h1
  · have h2 := O.mul_mem (O.mul_mem hy (hε i)) h1
    rw [hD]
    convert h2 using 1
    linear_combination (-(y * t * (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * B i j)) * hε2 i
  · intro b _ hb
    have : (b : ℕ) ≠ i := fun e => hb (Fin.ext e)
    rw [hrow _ _ ha' ha, if_neg (by simp only [a]; omega), zero_mul, zero_mul]
  · simp
end GlobalTheory.OrbitDenom
