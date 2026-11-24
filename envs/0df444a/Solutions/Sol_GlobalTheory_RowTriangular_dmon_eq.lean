-- Prove2me | solution 1 for GlobalTheory.RowTriangular.dmon_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:13.212921+00:00
-- url     : https://prove2.me/submissions/2465a803-850a-47d3-822b-d5d49843f70a

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
import Theorems.Thm_GlobalTheory_FormalLog_CZ_cons
import Theorems.Thm_GlobalTheory_FormalLog_CZ_nil
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
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] (F : Fin d → PS S 2 d) (Ψ : A →ₐ[S] Module.End S (PS S 1 d))
    {I : Type} [Fintype I] (u : I → Fin d → S) (x : I → A) (hx : ∀ l, Ψ (x l) = dEnd F (u l)) (m : I →₀ ℕ)
    (g : PS S 1 d) : DmonOf F u m g = Ψ (∏ l, x l ^ m l) g := by
  classical
  have hD : ∀ v, ⇑(dEnd F v) = Dof F v := fun v => funext (dEnd_apply F v)
  have key : ∀ L : List I,
      L.foldr (fun l h => (Dof F (u l))^[m l] h) g = Ψ ((L.map fun l => x l ^ m l).prod) g := by
    intro L
    induction L with
    | nil => simp
    | cons l L ih =>
      rw [List.foldr_cons, List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← ih, map_pow,
        hx, Module.End.pow_apply, hD]
  rw [DmonOf, key, Finset.prod_map_toList]
end GlobalTheory.RowTriangular
