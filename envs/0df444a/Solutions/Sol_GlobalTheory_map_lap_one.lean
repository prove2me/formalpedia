-- Prove2me | solution 1 for GlobalTheory.map_lap_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:54.761864+00:00
-- url     : https://prove2.me/submissions/ca5afb88-857b-43e5-a3a5-4d7379ec0999

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AdmissibleColumnsLeAndHarmonicMapCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k' 1 τ τ' a a' (MvPolynomial.map f P) = MvPolynomial.map f (lap r n k 1 τ τ' a a' P) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
    Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, pderiv_map]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 2
  by_cases h : b = b' <;> simp [Matrix.one_apply, h]
end GlobalTheory
