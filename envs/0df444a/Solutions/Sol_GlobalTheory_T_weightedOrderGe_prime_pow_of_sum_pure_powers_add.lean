-- Prove2me | solution 1 for GlobalTheory.T.weightedOrderGe_prime_pow_of_sum_pure_powers_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:10.170528+00:00
-- url     : https://prove2.me/submissions/584f9775-bb0b-4b65-8416-510e0483a99a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAddStatement
import Theorems.Thm_GlobalTheory_WeightFrobenius_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (M N k : ℕ) (r w w₂ : ℝ) (a : Fin M → C) (ν : MvPowerSeries (Fin M) C), w ≤ w₂ → (∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) →
    OrdGe v (fun _ => r) ν w₂ → OrdGe v (fun _ => r) ((∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N + ν) ^ (l ^ k) -
      ∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) (min (1 + (l : ℝ) ^ k * w) ((l : ℝ) ^ k * w₂))) := by
  first | exact @GlobalTheory.WeightFrobenius.main | exact GlobalTheory.WeightFrobenius.main | (intros; apply GlobalTheory.WeightFrobenius.main <;> assumption)
end _root_.GlobalTheory.T
