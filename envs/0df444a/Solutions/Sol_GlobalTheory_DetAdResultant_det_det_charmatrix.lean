-- Prove2me | solution 1 for GlobalTheory.DetAdResultant.det_det_charmatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:27.997215+00:00
-- url     : https://prove2.me/submissions/6359dab0-d782-4a2e-8147-3d6f248a8350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultant
import Theorems.Thm_GlobalTheory_DetAdResultant_det_aeval_eq_resultant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
open GlobalTheory GlobalTheory.DetAdResultant
namespace GlobalTheory.DetAdResultant
theorem _root_.solution {E : Type} [Field E] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ E) (B : Matrix ι₂ ι₂ E) :
    ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix B.transpose).map (aeval A).toRingHom)).det =
      resultant A.charpoly B.charpoly := by
  rw [← Matrix.det_det, ← Matrix.charpoly, Matrix.charpoly_transpose]
  exact det_aeval_eq_resultant A B.charpoly (Matrix.charpoly_monic B)
end GlobalTheory.DetAdResultant
