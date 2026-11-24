-- Prove2me | solution 1 for GlobalTheory.MomOne.model_norm_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:08.422087+00:00
-- url     : https://prove2.me/submissions/b5a255a2-df61-4523-b1e4-8f7980322607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGoodReductionAlgebraicWeierstrassModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology UpperHalfPlane
open GlobalTheory GlobalTheory.MomOne
namespace GlobalTheory.MomOne
theorem _root_.solution {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  let S : Subring ℂ_[q] := (NormedField.valuation (K := ℂ_[q])).integer
  have hS := Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))
  have h1 : IsIntegral S x := hx.tower_top
  have h2 := hS.mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3
end GlobalTheory.MomOne
