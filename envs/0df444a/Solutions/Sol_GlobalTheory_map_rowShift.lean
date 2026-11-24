-- Prove2me | solution 1 for GlobalTheory.map_rowShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:02.422047+00:00
-- url     : https://prove2.me/submissions/a2d8e81e-2c1e-4184-bb9a-7f280e40efc1

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
    (σ : T) (i i' : Fin (r σ)) (t : k) (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k' σ i i' (f t) (MvPolynomial.map f P) = MvPolynomial.map f (rowShift r n k σ i i' t P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowShift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp
end GlobalTheory
