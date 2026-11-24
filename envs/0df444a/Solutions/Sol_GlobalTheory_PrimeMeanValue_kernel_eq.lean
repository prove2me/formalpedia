-- Prove2me | solution 1 for GlobalTheory.PrimeMeanValue.kernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:30:54.857501+00:00
-- url     : https://prove2.me/submissions/a0a85803-db1d-468c-8852-cadd07888222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.PrimeMeanValue
namespace GlobalTheory.PrimeMeanValue
theorem _root_.solution (n δ x : ℝ) :
    (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) =
      (Set.Ico (n / Real.exp δ) n).indicator (fun x => 1 / x) x := by
  rw [Set.indicator_apply]
  refine if_congr ?_ rfl rfl
  rw [Set.mem_Ico, div_le_iff₀ (Real.exp_pos δ), and_comm]
end GlobalTheory.PrimeMeanValue
