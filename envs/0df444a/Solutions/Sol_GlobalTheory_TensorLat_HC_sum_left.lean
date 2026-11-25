-- Prove2me | solution 1 for GlobalTheory.TensorLat.HC_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:53:50.208429+00:00
-- url     : https://prove2.me/submissions/ca05a03a-c070-4a43-8140-5eb8d449b1ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Theorems.Thm_GlobalTheory_TensorLat_Hf_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution {κ : Type*} (s : Finset κ) (v : κ → Fin n → EuclideanSpace ℂ ι)
    (w : Fin n → EuclideanSpace ℂ ι) : HC (∑ j ∈ s, v j) w = ∑ j ∈ s, HC (v j) w := by
  simp only [← Hf_flat, map_sum, Hf_sum_left]
end GlobalTheory.TensorLat
