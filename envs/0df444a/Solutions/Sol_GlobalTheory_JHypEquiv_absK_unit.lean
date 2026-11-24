-- Prove2me | solution 1 for GlobalTheory.JHypEquiv.absK_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:34.214347+00:00
-- url     : https://prove2.me/submissions/7a42a691-98c5-46c1-b08b-3713afdb46f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypUnipotentTorusEquivariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JHypEquiv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JHypEquiv
theorem _root_.solution (A : Et F E) (s : A.Kˣ) : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
  unfold Et.absK
  rw [dif_pos s.isUnit]
  congr 2
  exact Units.ext (IsUnit.unit_spec _)
end GlobalTheory.JHypEquiv
