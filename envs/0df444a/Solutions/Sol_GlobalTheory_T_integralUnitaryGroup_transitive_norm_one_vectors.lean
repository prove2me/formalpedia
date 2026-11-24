-- Prove2me | solution 1 for GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:26:59.217903+00:00
-- url     : https://prove2.me/submissions/8caa0d14-cf11-483a-a167-1f9c9a009aff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectorsStatement
import Theorems.Thm_GlobalTheory_UnitaryTransitive_uO_transitive


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 → ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  first | exact @GlobalTheory.UnitaryTransitive.uO_transitive | exact GlobalTheory.UnitaryTransitive.uO_transitive | (intros; apply GlobalTheory.UnitaryTransitive.uO_transitive <;> assumption)
end _root_.GlobalTheory.T
