-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_det_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:06.601144+00:00
-- url     : https://prove2.me/submissions/3e6a7d6b-8be7-4bda-972b-9f33c5a69997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_one
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_graded
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_det
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa
theorem _root_.solution (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (s : ℕ → Prop) [DecidablePred s] :
    ((kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).submatrix
        (fun p : {p // s (kdeg p)} => p.1) (fun p : {p // s (kdeg p)} => p.1)).det =
      (∏ j ∈ Finset.range (g + 1), if s (j + 1) then (C j).det ^ g.choose j else 1) *
        (if s 0 then P.det else 1) := by
  have h := Matrix.twoBlockTriangular_det
    (kosBlock (fun j => if s (j + 1) then C j else 1) (if s 0 then P else 1) :
      Matrix (KIx g d N) (KIx g d N) R) (fun p => s (kdeg p))
    (fun i hi j hj => kosBlock_graded _ _ _ _ (fun h => hi (h ▸ hj)))
  have e1 : Matrix.toSquareBlockProp
      (kosBlock (fun j => if s (j + 1) then C j else 1) (if s 0 then P else 1) :
      Matrix (KIx g d N) (KIx g d N) R) (fun p => s (kdeg p)) =
      (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).submatrix
        (fun p : {p // s (kdeg p)} => p.1) (fun p : {p // s (kdeg p)} => p.1) := by
    ext p q
    exact kosBlock_congr (fun j => if s (j + 1) then C j else 1) C (if s 0 then P else 1) P p.1 q.1
      (fun j hj => if_pos (hj ▸ p.2)) (fun hj => if_pos (hj ▸ p.2))
  have e2 : Matrix.toSquareBlockProp
      (kosBlock (fun j => if s (j + 1) then C j else 1) (if s 0 then P else 1) :
      Matrix (KIx g d N) (KIx g d N) R) (fun p => ¬ s (kdeg p)) = 1 := by
    rw [← Matrix.submatrix_one (fun p : {p : KIx g d N // ¬ s (kdeg p)} => p.1)
      Subtype.val_injective, ← kosBlock_one]
    ext p q
    exact kosBlock_congr (fun j => if s (j + 1) then C j else 1) (fun _ => 1) (if s 0 then P else 1) 1
      p.1 q.1 (fun j hj => if_neg (hj ▸ p.2)) (fun hj => if_neg (hj ▸ p.2))
  rw [e1, e2, Matrix.det_one, mul_one, kosBlock_det] at h
  rw [← h]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · split_ifs <;> simp
end GlobalTheory.KeyKa
