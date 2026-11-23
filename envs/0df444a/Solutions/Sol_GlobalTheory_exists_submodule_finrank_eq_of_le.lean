-- Prove2me | solution 1 for GlobalTheory.exists_submodule_finrank_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:35.136399+00:00
-- url     : https://prove2.me/submissions/c151118b-b4c5-4d62-9a13-7d4164833412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightContinuousOnFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIsLUBHeightRpowLowerSemicontinuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {r i : ℕ} (h : i ≤ r) :
    ∃ W : Submodule K (Fin r → K), Module.finrank K W = i := by

  have hli : LinearIndependent K ((Pi.basisFun K (Fin r)) ∘ Fin.castLE h) :=
    (Pi.basisFun K (Fin r)).linearIndependent.comp _ (Fin.castLE_injective h)
  exact ⟨_, (finrank_span_eq_card hli).trans (Fintype.card_fin i)⟩
end GlobalTheory
