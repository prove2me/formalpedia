-- Prove2me | solution 1 for GlobalTheory.RowTriangular.prodForm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:15.169222+00:00
-- url     : https://prove2.me/submissions/67e5fa90-e2ec-4bdc-bdef-ba322d3d6060

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
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
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] {n : ℕ} (lam : Fin n → A →ₗ[S] S) (x : Fin n → A) :
    prodForm lam (∏ b, PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => A) b (x b)) = ∏ b, lam b (x b) := by
  have e : (∏ b, PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => A) b (x b)) =
      PiTensorProduct.tprod S x := by
    simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply]
    rw [← PiTensorProduct.tprod_prod, Finset.univ_prod_mulSingle]
  rw [e]
  simp [prodForm]
end GlobalTheory.RowTriangular
