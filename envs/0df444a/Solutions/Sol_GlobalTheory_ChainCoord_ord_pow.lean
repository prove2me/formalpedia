-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:39.489749+00:00
-- url     : https://prove2.me/submissions/54189d64-92a9-4dd2-b2e2-098cab8441ba

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_psWeight_calculus


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
theorem _root_.solution {g : MvPowerSeries (Fin M) C} {w : ℝ} (h : OrdGe v ρ g w) (N : ℕ) :
    OrdGe v ρ (g ^ N) (N * w) := fun α => by
  have e : ∀ β : Fin M →₀ ℕ, β.sum (fun j e => ρ j * (e : ℝ)) = ∑ m, ρ m * β m := fun β =>
    Finsupp.sum_fintype _ _ (by simp)
  have := (GlobalTheory.psWeight_calculus C v (Fin M) ρ g g w w (fun β => by rw [e]; exact h β)).2 N α
  rwa [e] at this
end GlobalTheory.ChainCoord
