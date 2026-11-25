-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.scal_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:57.522372+00:00
-- url     : https://prove2.me/submissions/ea5589d3-a268-4af8-b593-c8e647bc045b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_adj_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_det_up
import Theorems.Thm_GlobalTheory_OrbitDenom_sub_three
import Theorems.Thm_GlobalTheory_OrbitDenom_det_three
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
theorem _root_.solution (O : Subring E) {n l' l : ℕ} (h : l ≤ n) (hl : l' < l)
    (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O)
    (t : E) (ε : Fin n → E) (hε : ∀ b, ε b ∈ O)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b) :
    ∃ y ∈ O, (W.submatrix (Fin.castLE h) (Fin.castLE h)).det = y * t := by
  set f := Fin.castLE h with hf
  set D := (W.submatrix f f).det with hD
  set Y := ((A * W * B).submatrix f f).adjugate * A.submatrix f f with hY
  have hu : IsUnit (B.submatrix f f).det := by rw [det_up h B hB hB1]; exact isUnit_one
  have h1 : Y * W.submatrix f f * B.submatrix f f = D • (1 : Matrix (Fin l) (Fin l) E) := by
    rw [hY, Matrix.mul_assoc _ (A.submatrix f f), Matrix.mul_assoc, ← sub_three h A W B hA hB,
      Matrix.adjugate_mul, det_three h A W B hA hA1 hB hB1]
  have h2 : B.submatrix f f * (Y * W.submatrix f f) = D • (1 : Matrix (Fin l) (Fin l) E) := by
    have h3 : B.submatrix f f * (Y * W.submatrix f f) * B.submatrix f f =
        D • (1 : Matrix (Fin l) (Fin l) E) * B.submatrix f f := by
      rw [Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have h4 := congrArg (· * (B.submatrix f f)⁻¹) h3
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hu] using h4
  let p : Fin l := ⟨l - 1, by omega⟩
  let q : Fin l := ⟨l', hl⟩
  have h5 := congrFun (congrFun h2 p) p
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply,
    Finset.sum_eq_single p, Matrix.submatrix_apply, hB1, one_mul, Matrix.mul_apply,
    Finset.sum_eq_single q, Matrix.submatrix_apply,
    hcol _ _ (by simp [f, p]; omega) (by simp [f, p]; omega), if_pos (by simp [f, p, q]; omega)] at h5
  · refine ⟨Y p q * ε (f p), O.mul_mem ?_ (hε _), by rw [← h5]; ring⟩
    rw [hY, Matrix.mul_apply]
    exact O.sum_mem fun k _ => O.mul_mem (adj_mem O _ (fun _ _ => hZ _ _) _ _) (hAO _ _ k.2 le_rfl)
  · intro b _ hb
    have : (b : ℕ) ≠ l' := fun e => hb (Fin.ext e)
    rw [Matrix.submatrix_apply, hcol _ _ (by simp [f, p]; omega) (by simp [f, p]; omega),
      if_neg (by simp [f, p]; omega), zero_mul, mul_zero]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ l - 1 := fun e => hb (Fin.ext e)
    have := b.2
    rw [Matrix.submatrix_apply, hB _ _ (by rw [Fin.lt_def]; simp [f, p]; omega), zero_mul]
  · simp
end GlobalTheory.OrbitDenom
