-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:41.829595+00:00
-- url     : https://prove2.me/submissions/ef1cb1a8-6cc8-4844-a6fe-37e610623fb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues

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
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
variable [IsDiscreteValuationRing R]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
theorem _root_.solution {r : R} (h0 : r ≠ 0) (h : r ∈ maximalIdeal R) :
    0 < (ord_vw R).toFun (toUnitK r h0) := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
      (toUnitK r h0).val < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).2 h
  have h2 := (WithZero.log_lt_log (valuation_ne_zero R (toUnitK r h0)) one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  exact neg_pos.2 h2
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
