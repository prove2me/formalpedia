-- Prove2me | solution 1 for GlobalTheory.UnitaryTransitive.star_dot_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:16.239801+00:00
-- url     : https://prove2.me/submissions/9ae1fa04-8660-42d1-a9e7-989d39f5cce1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
import Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_castSucc
import Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_castSucc
attribute [local simp] GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_last

set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitaryTransitive
variable {E : Type} [Field E] [StarRing E]
namespace GlobalTheory.UnitaryTransitive
theorem _root_.solution {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (w : Fin r → E) (m : Fin r) :
    star (star w ⬝ᵥ (fun j => g j m)) = (gᴴ *ᵥ w) m := by
  simp [dotProduct, Matrix.mulVec, star_sum, mul_comm]
end GlobalTheory.UnitaryTransitive
