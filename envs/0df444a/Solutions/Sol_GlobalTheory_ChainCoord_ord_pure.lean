-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:55:26.069564+00:00
-- url     : https://prove2.me/submissions/ccc4094e-b654-46b1-b0d1-7f3081e2b980

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_ChainCoord_ord_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}
namespace GlobalTheory.ChainCoord
theorem _root_.solution {r w : ℝ} {N : ℕ} {a : Fin M → C}
    (h : ∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) :
    OrdGe v (fun _ => r) (∑ j, MvPowerSeries.C (R := C) (a j) *
      (X j : MvPowerSeries (Fin M) C) ^ N) w := by
  refine ord_sum _ fun j _ α => ?_
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hα
  · subst hα
    rw [mul_one, Finset.sum_eq_single j (fun b _ hb => by simp [Finsupp.single_apply, Ne.symm hb])
      (by simp)]
    simpa using h j
  · simp
end GlobalTheory.ChainCoord
