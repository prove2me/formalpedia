-- Prove2me | solution 1 for GlobalTheory.TensorLat.HC_flat_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:33:45.63533+00:00
-- url     : https://prove2.me/submissions/ead81804-18ea-474b-96f8-fb4e9696d302

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
noncomputable section
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (v w : EuclideanSpace ℂ (Fin n × ι)) :
    HC ((flat (n := n) (ι := ι)).symm v) (flat.symm w) = Hf v w := by
  rw [← Hf_flat, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
end GlobalTheory.TensorLat
