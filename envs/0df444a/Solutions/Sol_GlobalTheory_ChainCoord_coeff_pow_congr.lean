-- Prove2me | solution 1 for GlobalTheory.ChainCoord.coeff_pow_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:53.504229+00:00
-- url     : https://prove2.me/submissions/3cc2ed79-bdc7-44da-b095-f1488e3574f3

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
theorem _root_.solution {f g : MvPowerSeries (Fin M) C} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {D m : ℕ} (hm : 2 ≤ m)
    (h : ∀ β : Fin M →₀ ℕ, Finsupp.degree β < D → coeff β f = coeff β g)
    (α : Fin M →₀ ℕ) (hα : Finsupp.degree α = D) : coeff α (f ^ m) = coeff α (g ^ m) := by
  rw [← sub_eq_zero, ← map_sub, ← (Commute.all f g).mul_geom_sum₂ m]
  apply coeff_of_lt_order
  have h1 : (D : ℕ∞) ≤ (f - g).order := nat_le_order fun β hβ => by
    rw [map_sub, h β hβ, sub_self]
  have h2 : ((1 : ℕ) : ℕ∞) ≤ (∑ i ∈ Finset.range m, f ^ i * g ^ (m - 1 - i)).order :=
    nat_le_order fun β hβ => by
      have : β = 0 := by
        rw [← Finsupp.degree_eq_zero_iff]; omega
      subst this
      rw [coeff_zero_eq_constantCoeff_apply, map_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [map_mul, map_pow, map_pow, hf, hg, ← pow_add, zero_pow]
      have := Finset.mem_range.1 hi
      omega
  refine lt_of_lt_of_le ?_ (le_trans (add_le_add h1 h2) le_order_mul)
  rw [hα]
  exact_mod_cast Nat.lt_succ_self D
end GlobalTheory.ChainCoord
