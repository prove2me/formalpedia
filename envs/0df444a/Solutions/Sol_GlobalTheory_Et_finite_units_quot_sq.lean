-- Prove2me | solution 1 for GlobalTheory.Et.finite_units_quot_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:12.550245+00:00
-- url     : https://prove2.me/submissions/cfa261ef-2c39-464e-b142-90ccfa8cbabf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPair
import Theorems.Thm_GlobalTheory_finite_units_quot_sq_reduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
namespace Et
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E),
    Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  have : LocallyCompactSpace F := hU.lcF
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  exact finite_units_quot_sq_reduced F A.K
end Et
end GlobalTheory
