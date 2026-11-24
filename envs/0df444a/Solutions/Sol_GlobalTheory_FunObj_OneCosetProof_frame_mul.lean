-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.frame_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:21.122092+00:00
-- url     : https://prove2.me/submissions/efe2cf6c-95fd-47e0-b539-3f3dfaa66610

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution {a c b a' c' b' : ℕ} (h : a + c = b) (h' : a' + c' = b') (g : GL (Fin b) k) (g' : GL (Fin b') k)
    (X : Matrix (Fin a ⊕ Fin c) (Fin a' ⊕ Fin c') k) :
    (g⁻¹).val * X.reindex (frame h) (frame h') * g'.val =
      (((frameGL h g)⁻¹).val * X * (frameGL h' g').val).reindex (frame h) (frame h') := by
  rw [← map_inv]
  ext i j
  simp only [frameGL, Units.coe_mapEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  simp only [Finset.sum_mul]
  rw [← (frame h').sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← (frame h).sum_comp]
  simp [Matrix.submatrix_apply, Equiv.symm_apply_apply]
end GlobalTheory.FunObj.OneCosetProof
