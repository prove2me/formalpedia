-- Prove2me | solution 1 for GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:36.227277+00:00
-- url     : https://prove2.me/submissions/b444cbc5-f0fb-4511-af2b-0fc3739323b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
import Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_castSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_castSucc

set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitaryTransitive
variable {E : Type} [NormedField E] [StarRing E]
namespace GlobalTheory.UnitaryTransitive
theorem _root_.solution {r : ℕ} (x : Fin r → E) : ext0 x (Fin.last r) = 0 := by
  simp [ext0]
end GlobalTheory.UnitaryTransitive
