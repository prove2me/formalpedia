-- Prove2me | solution 1 for GlobalTheory.UnitCase.coeff_mvExp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:11.522423+00:00
-- url     : https://prove2.me/submissions/72ccae74-40d6-4478-a13c-6b0784443ce7

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_coeff_mul_pow_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution {a : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (m : σ →₀ ℕ) (N : ℕ) (h : m.degree < N) :
    MvPowerSeries.coeff m (mvExp a) =
      ∑ k ∈ Finset.range N, MvPowerSeries.coeff m (a ^ k) / (k.factorial : C) := by
  change ∑ k ∈ Finset.range (m.degree + 1), _ = _
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at *
    omega
  · intro k _ hk
    simp only [Finset.mem_range] at hk
    have := coeff_mul_pow_eq_zero ha ha k 0 m (by omega)
    rw [pow_zero, mul_one] at this
    rw [this, zero_div]
end GlobalTheory.UnitCase
