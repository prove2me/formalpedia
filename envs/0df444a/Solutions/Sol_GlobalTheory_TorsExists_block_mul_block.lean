-- Prove2me | solution 1 for GlobalTheory.TorsExists.block_mul_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:56.333445+00:00
-- url     : https://prove2.me/submissions/260a0584-5504-4bc4-9658-36d9e5cba43c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsExists
theorem _root_.solution {R : Type} [CommRing R] (P Q : Ix → Prop) [DecidablePred P] [DecidablePred Q]
    (M : Matrix Ix Ix R) (hM : M * M = 1) (h0 : ∀ p r, P p → ¬ Q r → M p r = 0) :
    M.submatrix (fun p : {p // P p} => p.1) (fun r : {r // Q r} => r.1) *
      M.submatrix (fun r : {r // Q r} => r.1) (fun p : {p // P p} => p.1) = 1 := by
  ext a b
  have h1 : (M * M) a.1 b.1 = (1 : Matrix {p // P p} {p // P p} R) a b := by
    rw [hM]; simp [Matrix.one_apply, Subtype.ext_iff]
  rw [← h1]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype Q (fun r => M a.1 r * M r b.1)]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {r // ¬ Q r})), add_zero]
  intro r _
  rw [h0 _ _ a.2 r.2, zero_mul]
end GlobalTheory.TorsExists
