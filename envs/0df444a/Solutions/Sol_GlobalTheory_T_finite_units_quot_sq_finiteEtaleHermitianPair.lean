-- Prove2me | solution 1 for GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:56.615965+00:00
-- url     : https://prove2.me/submissions/25e0bf7e-e3fc-4069-9b5b-d450b2f91b0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPairStatement
import Theorems.Thm_GlobalTheory_Et_finite_units_quot_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by
  first | exact @GlobalTheory.Et.finite_units_quot_sq | exact GlobalTheory.Et.finite_units_quot_sq | (intros; apply GlobalTheory.Et.finite_units_quot_sq <;> assumption)
end _root_.GlobalTheory.T
