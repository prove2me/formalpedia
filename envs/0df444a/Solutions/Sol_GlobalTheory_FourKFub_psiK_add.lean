-- Prove2me | solution 1 for GlobalTheory.FourKFub.psiK_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:25.405817+00:00
-- url     : https://prove2.me/submissions/03626b95-aaab-4972-ad11-141ca4aac99a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.FourKFub
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.FourKFub
theorem _root_.solution (A : Et F E) (ψ : AddChar F ℂ) (x y : A.K) : A.psiK ψ (x + y) = A.psiK ψ x * A.psiK ψ y := by
  simp only [Et.psiK, map_add, AddChar.map_add_eq_mul]
end GlobalTheory.FourKFub
