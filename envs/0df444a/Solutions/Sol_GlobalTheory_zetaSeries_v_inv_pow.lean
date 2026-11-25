-- Prove2me | solution 1 for GlobalTheory.zetaSeries_v_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:17.427699+00:00
-- url     : https://prove2.me/submissions/d7bc85eb-7ab5-4b46-95f6-9a69aea42279

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
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (x : C)
    (hx : v x = 1) (n : ℕ) : v ((x ^ n)⁻¹) = ((-(n : ℝ) : ℝ) : WithTop ℝ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at hx
    exact absurd hx (by simp)
  have h1 : v (x ^ n) = ((n : ℝ) : WithTop ℝ) := by
    rw [v.map_pow, hx, ← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
  have h2 : v (x ^ n) + v ((x ^ n)⁻¹) = 0 := by
    rw [← v.map_mul, mul_inv_cancel₀ (pow_ne_zero _ hx0), v.map_one]
  rw [h1] at h2
  cases hv : v ((x ^ n)⁻¹) with
  | top => rw [hv] at h2; simp at h2
  | coe r =>
    rw [hv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h2
    congr 1
    linarith
end GlobalTheory
