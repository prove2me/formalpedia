-- Prove2me | solution 1 for GlobalTheory.T.map_smul_addHaar_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:50.435637+00:00
-- url     : https://prove2.me/submissions/e2d0a73b-5bd9-4cdf-8efc-cfa480c0889d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AddHaarMapSmulOfNormEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AddHaarMapSmulOfNormEqOneStatement
import Theorems.Thm_GlobalTheory_addHaar_map_smul_of_norm_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K), ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ := by
  first | exact @GlobalTheory.addHaar_map_smul_of_norm_eq_one | exact GlobalTheory.addHaar_map_smul_of_norm_eq_one | (intros; apply GlobalTheory.addHaar_map_smul_of_norm_eq_one <;> assumption)
end _root_.GlobalTheory.T
