-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eval_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:46:34.689191+00:00
-- url     : https://prove2.me/submissions/add27bf3-852b-42a2-8154-fa227e231284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_mapMatrix_varMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution (x : ι × Fin a × Fin a → ℂ) (τ : ι) :
    eval x (1 + varMat (a := a) τ).det = (1 + famOf x τ).det := by
  rw [RingHom.map_det, map_add, map_one, mapMatrix_varMat]
end GlobalTheory.UnitaryZariskiDense
