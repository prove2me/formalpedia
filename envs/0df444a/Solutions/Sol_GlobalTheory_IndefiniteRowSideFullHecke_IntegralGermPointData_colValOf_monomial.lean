-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData.colValOf_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:21.263468+00:00
-- url     : https://prove2.me/submissions/d8027760-6cd0-4f85-bab2-faf650fa9d72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PointDataQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
theorem _root_.solution (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {κ : Type} [Fintype κ] (u : κ → Fin d → k) {n : ℕ} (a : κ × Fin n →₀ ℕ) (c : k) (f : Fin n → PS k 1 d) :
    colValOf B k h w0 m u (MvPolynomial.monomial a c) f =
      c * ∏ i, B.nabVal k h w0 m (f i) u (MvPolynomial.monomial (colExp a i) 1) := by
  classical
  unfold colValOf
  by_cases hc : c = 0
  · simp [hc]
  · simp [MvPolynomial.support_monomial, hc]
end GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
