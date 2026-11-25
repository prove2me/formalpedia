-- Prove2me | solution 1 for GlobalTheory.ChainCoord.v_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:29.970847+00:00
-- url     : https://prove2.me/submissions/3c5a4ba5-ec67-4df8-99e5-589185c0ecfc

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm

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
theorem _root_.solution {x : C} (hx : v x = 1) (E : ℕ) :
    ((-(E : ℝ) : ℝ) : WithTop ℝ) ≤ v ((x ^ E)⁻¹) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at hx
    exact WithTop.top_ne_one hx
  have h1 : v ((x ^ E)⁻¹) + v (x ^ E) = 0 := by
    rw [← v.map_mul, inv_mul_cancel₀ (pow_ne_zero _ hx0), v.map_one]
  have h2 : v (x ^ E) = ((E : ℝ) : WithTop ℝ) := by
    rw [v.map_pow, hx, ← WithTop.coe_one, ← WithTop.coe_nsmul]; simp
  rw [h2] at h1
  cases hv : v ((x ^ E)⁻¹) with
  | top => exact le_top
  | coe r =>
    rw [hv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at h1
    exact WithTop.coe_le_coe.2 (by linarith)
end GlobalTheory.ChainCoord
