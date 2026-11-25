-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.col_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:05:03.76695+00:00
-- url     : https://prove2.me/submissions/52625f15-1f96-42f6-9633-96ce64cc236d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_sub_mul_right
import Theorems.Thm_GlobalTheory_OrbitDenom_adj_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_det_up
import Theorems.Thm_GlobalTheory_OrbitDenom_sub_three
import Theorems.Thm_GlobalTheory_OrbitDenom_det_three
import Theorems.Thm_GlobalTheory_OrbitDenom_unit_cut
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
theorem _root_.solution (O : Subring E) {n l : ℕ} (h : l ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0) :
    ∃ G : Matrix (Fin n) (Fin l) E, (∀ a b, G a b ∈ O) ∧
      G * A.submatrix (Fin.castLE h) (Fin.castLE h) =
        (W.submatrix (Fin.castLE h) (Fin.castLE h)).det • A.submatrix id (Fin.castLE h) := by
  set f := Fin.castLE h with hf
  refine ⟨(A * W * B).submatrix id f * ((A * W * B).submatrix f f).adjugate, ?_, ?_⟩
  · intro a b
    rw [Matrix.mul_apply]
    exact O.sum_mem fun k _ => O.mul_mem (hZ _ _) (adj_mem O _ (fun _ _ => hZ _ _) _ _)
  · have hu : IsUnit (W.submatrix f f * B.submatrix f f).det := by
      rw [Matrix.det_mul, det_up h B hB hB1, mul_one]
      exact unit_cut h W hW hc
    have h1 : (A * W * B).submatrix id f = A.submatrix id f * (W.submatrix f f * B.submatrix f f) := by
      rw [sub_mul_right h _ _ B (fun k b hk hb => hB _ _ (by rw [Fin.lt_def]; omega)),
        sub_mul_right h _ A W hc, Matrix.mul_assoc]
    have h2 : (A * W * B).submatrix id f * ((A * W * B).submatrix f f).adjugate * A.submatrix f f *
        (W.submatrix f f * B.submatrix f f) =
        ((W.submatrix f f).det • A.submatrix id f) * (W.submatrix f f * B.submatrix f f) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.submatrix f f), ← sub_three h A W B hA hB,
        Matrix.mul_assoc, Matrix.adjugate_mul, det_three h A W B hA hA1 hB hB1, Matrix.smul_mul, ← h1,
        Matrix.mul_smul, Matrix.mul_one]
    have h3 := congrArg (· * (W.submatrix f f * B.submatrix f f)⁻¹) h2
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hu] using h3
end GlobalTheory.OrbitDenom
