-- Prove2me | solution 1 for GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:58.676999+00:00
-- url     : https://prove2.me/submissions/6bbbfb27-fb01-4a49-b473-e5b33f71484c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactUnitariesIntegralOrbitOfHankelDetNeStatement
import Theorems.Thm_GlobalTheory_JR_SuppBdd_exists_compact_of_integral


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
theorem _root_.solution : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  first | exact @GlobalTheory.JR.SuppBdd.exists_compact_of_integral | exact GlobalTheory.JR.SuppBdd.exists_compact_of_integral | (intros; apply GlobalTheory.JR.SuppBdd.exists_compact_of_integral <;> assumption)
end _root_.GlobalTheory.T
