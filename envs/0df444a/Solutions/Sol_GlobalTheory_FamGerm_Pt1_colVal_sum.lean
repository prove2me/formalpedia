-- Prove2me | solution 1 for GlobalTheory.FamGerm.Pt1.colVal_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:33.786973+00:00
-- url     : https://prove2.me/submissions/86f669fa-3065-49d7-81c2-451e0e3ff6ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Theorems.Thm_GlobalTheory_FamGerm_Pt1_colVal_add
import Theorems.Thm_GlobalTheory_FamGerm_Pt1_colVal_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamGerm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)
variable [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}
namespace GlobalTheory.FamGerm
namespace Pt1
theorem _root_.solution {I : Type} (S : Finset I) (c : I → F) (P : I → MvPolynomial (Λ × Fin n) F)
    (f : Fin n → PS F 1 y.d) : y.colVal h q e (∑ i ∈ S, c i • P i) f = ∑ i ∈ S, c i * y.colVal h q e (P i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Pt1.colVal]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, y.colVal_add, y.colVal_smul, ih]
end Pt1
end GlobalTheory.FamGerm
