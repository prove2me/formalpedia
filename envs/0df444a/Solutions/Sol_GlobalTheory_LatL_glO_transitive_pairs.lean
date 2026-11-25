-- Prove2me | solution 1 for GlobalTheory.LatL.glO_transitive_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:01:05.72026+00:00
-- url     : https://prove2.me/submissions/7b093729-0248-44f2-a786-6d78236155e3

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormSubLeMaxUltra
import Theorems.Thm_GlobalTheory_LatL_exists_glO_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LatL
namespace GlobalTheory.LatL
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v w : Fin (r + 1) → F), (∀ i, ‖v i‖ ≤ 1) →
    (∀ i, ‖w i‖ ≤ 1) → w ⬝ᵥ v = 1 → ∃ k ∈ glO (r + 1) F,
      (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧ w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  intro F E _ _ _ _ hU r v w hv hw hwv
  haveI : IsUltrametricDist F := hU.ultraF
  exact exists_glO_pair r v w hv hw hwv
end GlobalTheory.LatL
