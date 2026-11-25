-- Prove2me | solution 1 for GlobalTheory.FamGerm.Pt1.colVal_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:57:37.413793+00:00
-- url     : https://prove2.me/submissions/50a8ebef-199c-42a7-8b36-fc355d46c99f

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
theorem _root_.solution (mo : Λ × Fin n →₀ ℕ) (c : F) (f : Fin n → PS F 1 y.d) :
    y.colVal h q e (MvPolynomial.monomial mo c) f =
      c * ∏ b, (letI := H.starRing; y.B.nabVal F h H.w0 q (f b) e (MvPolynomial.monomial (colM mo b) 1)) := by
  classical
  unfold Pt1.colVal
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPolynomial.support_monomial, if_neg hc, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]
end Pt1
end GlobalTheory.FamGerm
