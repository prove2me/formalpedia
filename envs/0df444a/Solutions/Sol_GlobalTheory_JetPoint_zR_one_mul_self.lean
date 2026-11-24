-- Prove2me | solution 1 for GlobalTheory.JetPoint.zR_one_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:12.543149+00:00
-- url     : https://prove2.me/submissions/95a1d627-cf93-4e53-96e5-2ad7976af7de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetPointsOfIsLieBasis
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetPoint
open GlobalTheory.SqZero
variable {R : Type} [CommRing R]
namespace GlobalTheory.JetPoint
theorem _root_.solution {κ : Type} (j : κ) : zR (R := R) 1 j * zR (R := R) 1 j = 0 :=
  mul_eq_zero_of_sq (ker_jetAug_pow (R := R) κ 1) (zR_mem_ker 1 j) (zR_mem_ker 1 j)
end GlobalTheory.JetPoint
