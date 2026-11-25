-- Prove2me | solution 1 for GlobalTheory.zetaSeries_ordGe_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:31.391802+00:00
-- url     : https://prove2.me/submissions/de147770-6688-45a7-adbe-4facd92c7266

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe

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
namespace GlobalTheory
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ}
    (N : ℕ) (r w : ℝ) (a : Fin M → C) (ha : ∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) :
    OrdGe v (fun _ => r)
      (∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) w := by
  classical
  intro α
  rw [map_sum]
  apply v.map_le_sum
  intro j _
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]
  split_ifs with h
  · subst h
    have : ∑ m, r * ((Finsupp.single j N : Fin M →₀ ℕ) m : ℝ) = r * N := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro m _ hm
        simp [Finsupp.single_apply, Ne.symm hm]
      · simp
    rw [this, mul_one]
    exact ha j
  · simp
end GlobalTheory
