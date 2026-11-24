-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication.constantCoeff_mulSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:08.142778+00:00
-- url     : https://prove2.me/submissions/804abc41-313b-46c0-bc0a-bf3dce7c03a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OriginChartMultiplication_mulSeries_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
namespace GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ)
    (i : Fin d) : MvPowerSeries.constantCoeff (mulSeries F n i) = 0 := by
  induction n generalizing i with
  | zero => simp [mulSeries_zero]
  | succ n ih =>
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulSeries F n, pt R d 0] : Fin 2 → Pt R 1 d) q.1 q.2) = 0 := by
      rintro ⟨a, j⟩
      fin_cases a
      · exact ih j
      · simp [pt]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h) h (F.const i)
end GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
