-- Prove2me | solution 1 for GlobalTheory.OfPeriod.finrank_hom_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:07.798231+00:00
-- url     : https://prove2.me/submissions/b5b0c64c-bb30-46d4-9754-08ca47e67d3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


attribute [local simp] GlobalTheory.OfPeriod.reForm_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
namespace GlobalTheory.OfPeriod
theorem _root_.solution : Module.finrank ℤ (Y →+ ℤ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).finrank_eq]
  simp [Module.finrank_linearMap]
end GlobalTheory.OfPeriod
