-- Prove2me | solution 1 for GlobalTheory.ChainCoord.coeff_lgSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:49:12.94296+00:00
-- url     : https://prove2.me/submissions/40955832-4826-477d-ade4-9b829a4e88c5

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_ChainCoord_coeff_pow_eq_zero

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
theorem _root_.solution {d l : ℕ} (hl : 2 ≤ l) (al : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ c, constantCoeff (t c) = 0) (e : Fin d)
    (α : Fin M →₀ ℕ) (N : ℕ) (hN : Finsupp.degree α < N) :
    coeff α (lgSum l al t e) =
      ∑ n ∈ Finset.range N, ∑ a, al a n e * coeff α (t a ^ (l ^ n)) := by
  change ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, al a n e * coeff α (t a ^ (l ^ n)) = _
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun n _ hn => ?_
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [coeff_pow_eq_zero (ht a), mul_zero]
  have h1 : n < l ^ n := Nat.lt_pow_self hl
  simp only [Finset.mem_range] at hn
  omega
end GlobalTheory.ChainCoord
