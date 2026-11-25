-- Prove2me | solution 1 for GlobalTheory.zetaSeries_ordGe_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:27.869465+00:00
-- url     : https://prove2.me/submissions/ecdfbafc-ac46-4f0c-bbc2-0d52ac57a2e8

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
open MvPowerSeries
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)
namespace GlobalTheory
theorem _root_.solution {f g : MvPowerSeries (Fin M) C} {r s : ℝ} (hf : OrdGe v ρ f r)
    (hg : OrdGe v ρ g s) : OrdGe v ρ (f * g) (r + s) := by
  intro α
  rw [coeff_mul]
  apply v.map_le_sum
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [v.map_mul]
  have e : r + s - ∑ m, ρ m * (α m : ℝ) =
      (r - ∑ m, ρ m * (x.1 m : ℝ)) + (s - ∑ m, ρ m * (x.2 m : ℝ)) := by
    rw [← hx]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hf _) (hg _)
end GlobalTheory
