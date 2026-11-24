-- Prove2me | solution 1 for GlobalTheory.ThetaShiftProofs.isOpenImmersion_jK_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:56.22996+00:00
-- url     : https://prove2.me/submissions/48703ac7-1783-490b-9913-c7c7243ee8e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsOpenImmersionJKPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaShiftProofs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ThetaShiftProofs
theorem _root_.solution (k : Type) [Field k] : IsOpenImmersion (Out.jK (PowerSeries k)) := by
  have hX : Irreducible (PowerSeries.X : PowerSeries k) := PowerSeries.X_irreducible
  have : IsLocalization.Away (PowerSeries.X : PowerSeries k) (FractionRing (PowerSeries k)) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers (PowerSeries.X : PowerSeries k))
      (nonZeroDivisors (PowerSeries k)) (powers_le_nonZeroDivisors_of_noZeroDivisors hX.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hX
    exact ⟨PowerSeries.X ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization (PowerSeries.X : PowerSeries k)
end GlobalTheory.ThetaShiftProofs
