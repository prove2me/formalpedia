-- Prove2me | solution 1 for GlobalTheory.RowTriangular.dEnd_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:12.291749+00:00
-- url     : https://prove2.me/submissions/56d62c50-6817-4396-a91a-ce470117f88f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Theorems.Thm_GlobalTheory_RowTriangular_dEnd_apply
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RowTriangular
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open scoped TensorProduct
variable {S : Type} [CommRing S] {d : ℕ}
namespace GlobalTheory.RowTriangular
theorem _root_.solution (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (c : κ → S) (w : κ → Fin d → S) (v : Fin d → S)
    (hv : ∀ e, v e = ∑ j, c j * w j e) : dEnd F v = ∑ j, c j • dEnd F (w j) := by
  refine LinearMap.ext fun g => ?_
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, dEnd_apply, Dof, hv, map_sum, map_mul, Finset.sum_mul,
    Finset.smul_sum, MvPowerSeries.smul_eq_C_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.RowTriangular
