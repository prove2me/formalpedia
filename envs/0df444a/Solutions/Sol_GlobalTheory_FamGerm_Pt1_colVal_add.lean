-- Prove2me | solution 1 for GlobalTheory.FamGerm.Pt1.colVal_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:41.803678+00:00
-- url     : https://prove2.me/submissions/2bb449fc-36b5-45b7-9017-5f0fac06cc2b

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
theorem _root_.solution (P P' : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) :
    y.colVal h q e (P + P') f = y.colVal h q e P f + y.colVal h q e P' f := by
  classical
  unfold Pt1.colVal
  have key : ∀ R : MvPolynomial (Λ × Fin n) F, R.support ⊆ P.support ∪ P'.support → ∀ g : (Λ × Fin n →₀ ℕ) → F,
      ∑ mo ∈ R.support, R.coeff mo * g mo = ∑ mo ∈ P.support ∪ P'.support, R.coeff mo * g mo := fun R hR g =>
    Finset.sum_subset hR fun mo _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]
  rw [key _ MvPolynomial.support_add, key P Finset.subset_union_left, key P' Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun mo _ => by rw [MvPolynomial.coeff_add, add_mul]
end Pt1
end GlobalTheory.FamGerm
