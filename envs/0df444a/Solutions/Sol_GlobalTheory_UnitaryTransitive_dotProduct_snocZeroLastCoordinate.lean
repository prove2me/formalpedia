-- Prove2me | solution 1 for GlobalTheory.UnitaryTransitive.dotProduct_snocZeroLastCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:13.534388+00:00
-- url     : https://prove2.me/submissions/130ea404-5b21-4822-8ad5-7e6585b21773

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
variable {E : Type} [NormedField E] [StarRing E]
namespace GlobalTheory.UnitaryTransitive
theorem _root_.solution {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    f ⬝ᵥ ext0 x = (fun j => f j.castSucc) ⬝ᵥ x := by
  simp [dotProduct, Fin.sum_univ_castSucc]
end GlobalTheory.UnitaryTransitive
