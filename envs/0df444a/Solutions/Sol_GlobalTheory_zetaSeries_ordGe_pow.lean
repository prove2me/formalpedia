-- Prove2me | solution 1 for GlobalTheory.zetaSeries_ordGe_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:27.12286+00:00
-- url     : https://prove2.me/submissions/20e949ec-beb4-41b6-9b25-55d258818f90

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe
import Theorems.Thm_GlobalTheory_zetaSeries_ordGe_mono
import Theorems.Thm_GlobalTheory_zetaSeries_ordGe_one
import Theorems.Thm_GlobalTheory_zetaSeries_ordGe_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory
open MvPowerSeries
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)
namespace GlobalTheory
theorem _root_.solution {f : MvPowerSeries (Fin M) C} {r : ℝ} (hf : OrdGe v ρ f r) (n : ℕ) :
    OrdGe v ρ (f ^ n) (n * r) := by
  induction n with
  | zero => simpa using zetaSeries_ordGe_one v ρ
  | succ n ih =>
    rw [pow_succ]
    exact zetaSeries_ordGe_mono v ρ (zetaSeries_ordGe_mul v ρ ih hf) (by push_cast; linarith)
end GlobalTheory
