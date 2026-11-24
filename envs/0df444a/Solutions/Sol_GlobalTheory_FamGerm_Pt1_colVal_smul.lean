-- Prove2me | solution 1 for GlobalTheory.FamGerm.Pt1.colVal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:44.145904+00:00
-- url     : https://prove2.me/submissions/f551c999-7844-4f68-a1c8-73140de399a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial

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
theorem _root_.solution (c : F) (P : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) :
    y.colVal h q e (c • P) f = c * y.colVal h q e P f := by
  classical
  unfold Pt1.colVal
  rw [Finset.mul_sum, Finset.sum_subset (MvPolynomial.support_smul (a := c) (f := P))
    fun mo _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]]
  exact Finset.sum_congr rfl fun mo _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul, _root_.mul_assoc]
end Pt1
end GlobalTheory.FamGerm
